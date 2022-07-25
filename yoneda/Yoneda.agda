open import Library
open import Categories
open import Categories.Sets
open import Categories.Iso {b = lzero} Sets
open import Naturals
open import Functors


{-
  Dada la categoria C localmente chica. Para cada objeto X ∈ Obj C y
  un funtor F : C Op -> Sets, hay un isomorfismo
          Hom(yX, F) ≅ FX
  Donde:
    - yX es el funtor de yoneda

  -------------------------------------------------------------------------
  | C es una categoria es localmente chica si ∀ X,Y ∈ Obj C, Hom(X, Y) es |
  | un conjunto.                                                          |
  -------------------------------------------------------------------------

  Para poder demostrar esto vamos a realizar 3 pasos:
    (1) Definir un morfismo η-map : Hom(yX, F) -> FX
    (2) Definir un morfismo δₐ : FX -> Hom(yX(X), FX)
       Notemos que δₐ toma un a ∈ FX nos devuelve una transformacion lineal
       (demostrar naturalidad)
    (3) Demostrar que los morfismos en (1) y (2) son mutuamente inversas
-}

module yoneda.Yoneda {C : Cat {lzero} {lzero}} where -- Categoria localmente chica

open Cat C

{-
  yoneda : C Op -> Sets
  Sean X,A,B ∈ Obj C y f ∈ Hom(A, B) morfismo en la categoria C
  Luego el funtor de yoneda se comporta de la siguiente forma:
    - yoneda{X}(A) : Hom(A, X)
    - yoneda{X}(f) : yoneda{X}(B) -> yoneda{X}(A)

  Ejemplo: Dado X,Y,Z ∈ Obj C y f ∈ Hom (Y, Z)
    yoneda{X}(Y) = Hom(Y, X)
    yoneda{X}(f) : yoneda{X}(Z) -> yoneda{X}(Y)
                 : Hom(Z, X) -> Hom(Y, X)
    yoneda{X}(f) = λ g : Hom(Z, X) → g ∙ f
-}

yoneda : {X : Obj} -> Fun (C Op) Sets
yoneda {X} = functor
              (λ Y → Hom Y X) -- Obj → Set b
              (λ f g → g ∙ f) -- {X = X₁ : Obj} {Y : Obj} → Hom Y X₁ → Hom X₁ X → Hom Y X
              (ext (λ _ → idr)) -- {X = X₁ : Obj} → (λ g → g ∙ iden) ≅ (λ x → x)
              (ext (λ _ → sym ass)) -- {X = X₁ : Obj} {Y Z : Obj} {f : Hom Z Y} {g : Hom Y X₁} →
                                    -- (λ g₁ → g₁ ∙ g ∙ f) ≅ (λ x → (x ∙ g) ∙ f)
{-
  (1)
  Comenzamos definiendo el morfismo η-map:
    η-map : Hom(yX, F) -> FX
  Dado un δ : yX -> F
    η-map(δ) = δₓ(idₓ)

  Notemos que δₓ : yX(X) -> FX
                 : Hom(X, X) -> FX
  Entonces δₓ(idₓ) ∈ FX
-}
η-map : {X : Obj} {F : Fun (C Op) Sets} -> Cat.Hom Sets (NatT yoneda F) (Fun.OMap F X)
η-map {X} δ = let open NatT δ
              in cmp X iden

{-
  (1)
  Ahora para el otro lado, dado cualquier a ∈ FX, definimos la transformacion natural:
      δₐ : yX -> F
  Dado un X' : Obj
      δₐX : yX(X') -> FX'
      δₐX : Hom(X', X) -> FX'
      δₐX(h) = F(h) a
  
  A nosotros nos va a quedar δₐ un morfismo que toma a ∈ FX y nos devuelve la transformacion natural.
  Notemos que dado a ∈ FX, X' : Obj,
    (NatT.cmp δₐ) X' : Hom(X', X) -> FX'

  Para demostrar la condición de naturalidad hay que considerar el siguiente diagrama:

  yX(X') ------ yX(f) -----> yX(Y)     Hom(X', X) ------ yX(f) -----> Hom(Y, X)
    |                         |         |                               |
    |                         |         |                               |
   δₐ X'                      δₐ Y      δₐ X'                            δₐ Y
    |                         |         |                               |
    |                         |         |                               |
    V                         V         V                               V
  FX'    ------ F(f)  -----> FY        FX'  ------------ F(f)  ----->  FY

  Dado h ∈ yX(X'), queremos demostrar que:
    δₐ Y ∙ yX(f)(h) ≅ F(f) ∙ δₐ X' h
  Sabemos por definicion que:
  (∙) δₐ Y (h) = F(h) a
  (∙) yX(f)(h) = h ∙ f
  Luego nos queda:
    δₐ Y ∙ yX(f)(h) ≅ F(h ∙ f) a
-}

δₐ : {X : Obj} {F : Fun (C Op) Sets} -> Cat.Hom Sets (Fun.OMap F X) (NatT yoneda F)
δₐ {F = F} a = let open Fun F
               in natural
                  (λ X' h → (HMap h) a) -- (X' : Obj) → Hom X' X → OMap X
                  -- {X' Y : Obj} {f : Hom Y X'} →
                  -- (λ h → HMap f (HMap h a)) ≅ (λ h → HMap (h ∙ f) a)
                  (λ {X Y} {f} → ext (λ h → sym (proof
                                                   HMap (h ∙ f) a
                                                 ≅⟨ cong (λ g → g a) fcomp ⟩
                                                   HMap f (HMap h a)
                                                 ∎)))

{-
  (3)
  Ahora demostremos que η-map y δₐ son mutuamente inversas:

  Primero demostremos que dado X,X' ∈ Obj C y δ : yX -> F,
    δₐ (η-map δ) ≅ δ
  Si instanciamos en X' nos queda:
    δₐ (η-map δ) X' ≅ δ X'
  Notemos que:
    (a) δₐ (η-map δ) X' : Hom(X', X) -> FX'
    (b) δ X' : Hom(X', X) -> FX'
  Como (a) (b) son transformaciones naturales mas adelante vamos
  a utilizar NatTEq (queremos ver que son iguales)

  Tenemos una transformacion natural: δ : yX -> F
  yX(X) ----- yX(h) ----> yX(X')
    |                      |
    |                      |
   δ X                    δ X'
    |                      |
    |                      |
    V                      V       
  FX    -----  F h  ----> FX'
-}

δₐ-inv-η-map : {X X' : Obj} {F : Fun (C Op) Sets} {δ : NatT (yoneda {X}) F} ->
               (NatT.cmp (δₐ {X} {F} (η-map {X} {F} δ))) X' ≅ NatT.cmp δ X'
δₐ-inv-η-map {X} {X'} {F} {δ} =
    let open NatT (δₐ {X} {F} (η-map {X} {F} δ)) renaming (cmp to ρ'; nat to ρ-nat) -- rename
        open NatT (δ) renaming (cmp to δ'; nat to δ-nat)
        open Fun (yoneda {X}) renaming (OMap to yX-OMap; HMap to yX-HMap; fid to yX-fid; fcomp to yX-fcomp)
        open Fun F renaming (OMap to F-OMap; HMap to F-HMap; fid to F-fid; fcomp to F-fcomp)
    -- Dado h : Hom X' X queremos probar δₐ' X' h ≅ δ' X' h
    in ext (λ h → proof
                    ρ' X' h
                  ≅⟨ refl ⟩
                    (F-HMap h) (δ' X iden)
                  -- (λ x → F-HMap h (δ' X x)) ≅ (λ x → δ' X' (x ∙ h))
                  ≅⟨ cong (λ x → x iden) (δ-nat {X} {X'} {h}) ⟩
                    (δ' X') ((yX-HMap h) iden)
                  ≅⟨ cong (δ' X') idl ⟩
                    δ' X' h
                  ∎)
{-
  Ahora demostremos que dado X ∈ Obj C y a ∈ FX,
    η-map (δₐ a) ≅ a
-}

η-map-inv-δₐ : {X : Obj} {F : Fun (C Op) Sets} {a : Fun.OMap F X} ->
               η-map (δₐ {X} {F} a) ≅ a
η-map-inv-δₐ {X} {F} {a} =
    let open Fun F
        open NatT (δₐ {X} {F} a)
    in proof
        η-map (δₐ {X} {F} a)
       ≅⟨ refl ⟩
        cmp X iden
       ≅⟨ refl ⟩
        (HMap iden) a
       ≅⟨ cong (λ x → x a) fid ⟩
        a
       ∎

lemma-yoneda : {X : Obj} {F : Fun (C Op) Sets} -> Iso (η-map {X} {F})
lemma-yoneda {X} {F} = iso
                        δₐ
                        (ext (λ a → η-map-inv-δₐ {X} {F} {a}))
                        (ext (λ δ → NatTEq (ext (λ X' → δₐ-inv-η-map {X} {X'} {F} {δ}))))
 
module

public import CFSG.Quasithin.Background.G11Defs
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.OddKernel.SectionRep

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

abbrev tildeVBot (H : Subgroup (GLV V)) : Submodule (ZMod 2) V :=
  fixedSpace H ⊓ commSpace H ⊤

abbrev TildeV (H : Subgroup (GLV V)) : Type :=
  ↥(commSpace H ⊤) ⧸ (fixedSpace H).comap (commSpace H ⊤).subtype

abbrev HasIrrTildeV (H : Subgroup (GLV V)) : Prop :=
  IrrSec H (tildeVBot H) (commSpace H ⊤)

abbrev layerIn (G : Subgroup (GLV V)) : Subgroup (GLV V) :=
  (CFSG.layer ↥G).map G.subtype

structure Setup6 (G S L : Subgroup (GLV V)) : Prop where
  S_le : S ≤ G
  isPGroup : IsPGroup 2 S
  component : IsComponentOf L (G ⊓ Subgroup.centralizer (S : Set (GLV V)))
  irrTilde : HasIrrTildeV L

structure Setup6Irr (G S L : Subgroup (GLV V)) : Prop extends Setup6 G S L where
  irr : IsIrr G ⊤
  gen : G = normalClosure G L ⊔ S

@[expose] def IsAltHeartFor (E : Subgroup (GLV V)) (N : ℕ) : Prop :=
  ∃ (φ : ↥E ≃* alternatingGroup (Fin N)) (ψ : V ≃+ altHeart N),
    ∀ (e : ↥E) (v : V) (x : evenWeight N), ψ v = (x : altHeart N) →
      ψ ((e : GLV V) v) = (evenWeightPerm (φ e : Equiv.Perm (Fin N)) x : altHeart N)

@[expose] def IsOmegaPlusFor (E : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ (φ : ↥E ≃* ↥(omegaPlusTwo m)) (ψ : V ≃ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)),
    ∀ (e : ↥E) (v : V),
      ψ ((e : GLV V) v) =
        ((φ e : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ ψ v

@[expose] def IsOmegaMinusFor (E : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ (φ : ↥E ≃* ↥(omegaMinusTwo m)) (ψ : V ≃ₗ[ZMod 2] (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)),
    ∀ (e : ↥E) (v : V),
      ψ ((e : GLV V) v) =
        ((φ e : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ ψ v

@[expose] def TildeVWitness (L : Subgroup (GLV V)) (X M : Type) [Group X] [AddGroup M]
    (R : X → M → M → Prop) : Prop :=
  ∃ α : ↥L →* X, Function.Surjective α ∧
    ∃ β : ↥(commSpace L ⊤) →+ M, Function.Surjective β ∧
      β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup ∧
      ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
        R (α ℓ) (β w) (β w')

@[expose] def IsAltNaturalModule (L : Subgroup (GLV V)) (n : ℕ) : Prop :=
  TildeVWitness L (alternatingGroup (Fin n)) (altHeart n) fun σ a b =>
    ∀ x : evenWeight n, a = (x : altHeart n) →
      b = (evenWeightPerm (σ : Equiv.Perm (Fin n)) x : altHeart n)

@[expose] def IsOmegaPlusModule (L : Subgroup (GLV V)) (m : ℕ) : Prop :=
  TildeVWitness L ↥(omegaPlusTwo m) (Fin m ⊕ Fin m → ZMod 2) fun g a b =>
    b = ((g : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
      *ᵥ a

@[expose] def IsOmegaMinusModule (L : Subgroup (GLV V)) (m : ℕ) : Prop :=
  TildeVWitness L ↥(omegaMinusTwo m) (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) fun g a b =>
    b = ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a

@[expose] def IsA7FourModule (L : Subgroup (GLV V)) : Prop :=
  (∃ α : ↥L →* alternatingGroup (Fin 7), Function.Surjective α) ∧
    Module.finrank (ZMod 2) (TildeV L) = 4

@[expose] def IsA6Z3Module (L : Subgroup (GLV V)) : Prop :=
  (∃ α : ↥L →* alternatingGroup (Fin 6), Function.Surjective α) ∧
    Module.finrank (ZMod 2) (TildeV L) = 6

@[expose] def IsFModule (L : Subgroup (GLV V)) : Prop :=
  (∃ n : ℕ, 6 ≤ n ∧ IsAltNaturalModule L n) ∨ IsA7FourModule L ∨
    (∃ m : ℕ, 3 ≤ m ∧ IsOmegaPlusModule L m) ∨ (∃ m : ℕ, 2 ≤ m ∧ IsOmegaMinusModule L m) ∨
      IsA6Z3Module L

abbrev Sect (W₀ W₁ : Submodule (ZMod 2) V) : Type :=
  ↥W₁ ⧸ W₀.comap W₁.subtype

@[expose] noncomputable def sectHom (H : Subgroup (GLV V)) {W₀ W₁ : Submodule (ZMod 2) V}
    (h₀ : Invariant H W₀) (h₁ : Invariant H W₁) : ↥H →* GLV (Sect W₀ W₁) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Sect W₀ W₁)).toMonoidHom.comp
    (CFSG.RankThree.OddKernel.sectionRep H.subtype (fun h w hw => h₀ h h.2 w hw)
      (fun h w hw => h₁ h h.2 w hw)).asGroupHom

theorem sectHom_mk (H : Subgroup (GLV V)) {W₀ W₁ : Submodule (ZMod 2) V}
    (h₀ : Invariant H W₀) (h₁ : Invariant H W₁) (h : ↥H) (w : ↥W₁) :
    sectHom H h₀ h₁ h (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨(h : GLV V) w, h₁ h h.2 w w.2⟩ :=
  rfl

end CFSG.CGT.Foote82

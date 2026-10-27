module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec4Setting (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) : Prop
    extends Sec3SettingLB G t L where
  omega7 : LieModel (L ⧸ oddCore L) .POmegaOdd 3 3 1

structure Sec4Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) : Prop
    extends Sec4Setting G t L, Asc82Notation t L S z

@[expose] def SLC {G : Type} [Group G] (S L : Subgroup G) : Subgroup G :=
  S ⊓ (L ⊔ centralizer (L : Set G))

@[expose] def vecWeight {n : ℕ} (v : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

@[expose] def IsEvenVec {n : ℕ} (v : Fin n → ZMod 2) : Prop :=
  ∑ i, v i = 0

@[expose] def permVec {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  v ∘ ⇑σ.symm

variable {G : Type} [Group G]

@[expose] def IsPermModuleVia {n : ℕ} (P : (Fin n → ZMod 2) → Prop) (φ : (Fin n → ZMod 2) → G)
    (E H : Subgroup G) (Alt : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  (∀ v w, P v → P w → φ (v + w) = φ v * φ w) ∧
    (∀ v w, P v → P w → φ v = φ w → v = w) ∧
    (∀ x : G, x ∈ E ↔ ∃ v, P v ∧ φ v = x) ∧
    (∀ h ∈ H, ∃ σ ∈ Alt, ∀ v, P v → h * φ v * h⁻¹ = φ (permVec σ v)) ∧
    (∀ σ ∈ Alt, ∃ h ∈ H, ∀ v, P v → h * φ v * h⁻¹ = φ (permVec σ v))

end CFSG.OddStandard.SmallF3.Omega

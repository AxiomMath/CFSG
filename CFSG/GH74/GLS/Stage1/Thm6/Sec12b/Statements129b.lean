module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type*} [Group G]

@[expose] def IsDihedral2 (D : Subgroup G) : Prop :=
  ∃ ρ s : G, ρ ∈ D ∧ s ∈ D ∧ s * s = 1 ∧ s * ρ * s⁻¹ = ρ⁻¹ ∧
    ∀ d ∈ D, ∃ i : ℤ, d = ρ ^ i ∨ d = s * ρ ^ i

@[expose] def IP_Rd_dihedral (x : G) (Rd : Subgroup G) : Prop :=
  ∀ P' : Subgroup G, P' ≤ Rd → P' ⊓ Subgroup.zpowers x = ⊥ → P' ⊔ Subgroup.zpowers x = Rd →
    IsDihedral2 P'

@[expose] def IP_Rd_fuse (x : G) (P Rd : Subgroup G) : Prop :=
  P ⊔ Subgroup.zpowers x ≠ Rd → ∀ E E' : Subgroup G, E ≤ P ⊔ Subgroup.zpowers x →
    E' ≤ P ⊔ Subgroup.zpowers x → IsElemAb2 E → IsElemAb2 E' → Nat.card E = 8 →
    Nat.card E' = 8 → ∃ r ∈ Rd, E' = Hconj r E

@[expose] def IP_T_normal (x z : G) (T P Rd : Subgroup G) : Prop :=
  (∀ E E' : Subgroup G, E ≤ Rd → E' ≤ Rd → IsElemAb2 E → IsElemAb2 E' → Nat.card E = 8 →
      Nat.card E' = 8 → ∃ t ∈ T, E' = Hconj t E) ∨
  ∃ F' : Subgroup G, F' ≤ T ∧ Subgroup.zpowers x ≤ F' ∧ IsCyclic F' ∧
    F' ⊓ Rd = Subgroup.zpowers x ∧ Rd ⊔ F' = T ∧
    (∀ w ∈ F', w ^ 4 = 1 → (∀ p ∈ P, w * p = p * w) ∧
      ∀ b ∈ Rd, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z) ∧
    (Nat.card P = 4 → F' = Subgroup.zpowers x) ∧
    (8 ≤ Nat.card P → ∀ t ∈ T, (∀ p ∈ P, t * p = p * t) →
      ∃ u ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z, ∃ w ∈ F', w ^ 4 = 1 ∧ t = u * w)

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b

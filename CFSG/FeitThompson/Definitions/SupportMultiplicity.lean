module

public import Mathlib.Data.Set.Card
public import CFSG.FeitThompson.Definitions.SupportOfAMaximalSubgroupCoreFamily
public import CFSG.FeitThompson.Definitions.SupportingMaximalSubgroupsOfAnElement
public import Mathlib.Data.Set.Lattice

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

noncomputable def supportMultiplicity (𝓜 : Set (Subgroup G)) (S : Subgroup G → Subgroup G)
    (x : G) : ℕ :=
  (supportingMaximals 𝓜 S x).ncard

variable {𝓜 𝓝 : Set (Subgroup G)} {S T : Subgroup G → Subgroup G} {x : G}

theorem supportMultiplicity_eq_ncard (𝓜 : Set (Subgroup G)) (S : Subgroup G → Subgroup G) (x : G) :
    supportMultiplicity 𝓜 S x = (supportingMaximals 𝓜 S x).ncard := (rfl)

@[simp]
theorem supportMultiplicity_empty (S : Subgroup G → Subgroup G) (x : G) :
    supportMultiplicity (∅ : Set (Subgroup G)) S x = 0 := by
  have h : supportingMaximals (∅ : Set (Subgroup G)) S x = ∅ := by ext M; simp
  rw [supportMultiplicity_eq_ncard, h, Set.ncard_empty]

@[simp]
theorem supportMultiplicity_one : supportMultiplicity 𝓜 S 1 = 𝓜.ncard := by
  rw [supportMultiplicity_eq_ncard, supportingMaximals_one]

@[simp]
theorem supportMultiplicity_inv : supportMultiplicity 𝓜 S x⁻¹ = supportMultiplicity 𝓜 S x := by
  rw [supportMultiplicity_eq_ncard, supportMultiplicity_eq_ncard, supportingMaximals_inv]

theorem supportMultiplicity_le_ncard (h𝓜 : 𝓜.Finite := by toFinite_tac) :
    supportMultiplicity 𝓜 S x ≤ 𝓜.ncard :=
  Set.ncard_le_ncard supportingMaximals_subset h𝓜

theorem supportMultiplicity_pos_iff (h𝓜 : 𝓜.Finite := by toFinite_tac) :
    0 < supportMultiplicity 𝓜 S x ↔ ∃ M ∈ 𝓜, x ∈ S M := by
  rw [supportMultiplicity_eq_ncard, Set.ncard_pos (supportingMaximals_finite_of_finite h𝓜)]
  simp only [Set.Nonempty, mem_supportingMaximals]

theorem supportMultiplicity_eq_zero_iff (h𝓜 : 𝓜.Finite := by toFinite_tac) :
    supportMultiplicity 𝓜 S x = 0 ↔ ∀ M ∈ 𝓜, x ∉ S M := by
  rw [← Nat.pos_iff_ne_zero.not_left, supportMultiplicity_pos_iff h𝓜]
  simp

theorem supportMultiplicity_pos_of_mem_coreFamilySupport (hx : x ∈ coreFamilySupport 𝓜 S)
    (h𝓜 : 𝓜.Finite := by toFinite_tac) : 0 < supportMultiplicity 𝓜 S x := by
  obtain ⟨M, hM, hxS, -⟩ := mem_coreFamilySupport_iff.1 hx
  exact (supportMultiplicity_pos_iff h𝓜).2 ⟨M, hM, hxS⟩

theorem supportMultiplicity_mono (h : 𝓜 ⊆ 𝓝) (h𝓝 : 𝓝.Finite := by toFinite_tac) :
    supportMultiplicity 𝓜 S x ≤ supportMultiplicity 𝓝 S x :=
  Set.ncard_le_ncard (supportingMaximals_mono h) (supportingMaximals_finite_of_finite h𝓝)

theorem supportMultiplicity_mono_family (h : ∀ M ∈ 𝓜, S M ≤ T M)
    (h𝓜 : 𝓜.Finite := by toFinite_tac) :
    supportMultiplicity 𝓜 S x ≤ supportMultiplicity 𝓜 T x :=
  Set.ncard_le_ncard
    (fun M hM => mem_supportingMaximals.2
      ⟨(mem_supportingMaximals.1 hM).1,
        h M (mem_supportingMaximals.1 hM).1 (mem_supportingMaximals.1 hM).2⟩)
    (supportingMaximals_finite_of_finite h𝓜)

end

end CFSG.FeitThompson

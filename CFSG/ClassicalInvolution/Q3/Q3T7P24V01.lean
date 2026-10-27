module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24H01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
open scoped commutatorElement

section Vertex

variable {G : Type} [Group G] [Finite G]

theorem isSubnormal_modOdd_of_subnormal {M : Subgroup G} {z : G}
    (hsub : IsSubnormal M (Subgroup.centralizer ({z} : Set G))) : (modOdd z M).IsSubnormal := by
  have h := isSubnormal_subgroupOf hsub (Subgroup.centralizer ({z} : Set G))
  rw [Subgroup.subgroupOf_self] at h
  have hsurj : Function.Surjective (oddQuotMk z) := QuotientGroup.mk'_surjective _
  have h2 := CFSG.ComponentClassification.Components.chain_map (oddQuotMk z) h
  rw [Subgroup.map_top_of_surjective _ hsurj] at h2
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib _).mp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).mpr h2)

theorem isSolvable_modOdd_of_solvable {M : Subgroup G} {z : G}
    (hMC : M ≤ Subgroup.centralizer ({z} : Set G)) (hM : Group.IsSolvable ↥M) :
    Group.IsSolvable ↥(modOdd z M) := by
  let ψ : ↥M →* OddQuot z := (oddQuotMk z).comp (Subgroup.inclusion hMC)
  have hrange : ψ.range = modOdd z M := by
    ext x
    rw [MonoidHom.mem_range, mem_modOdd_iff]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨⟨m, hMC m.2⟩, m.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have : Group.IsSolvable ↥ψ.range := Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  rwa [hrange] at this

theorem commutator_component_modOdd_of_member {M : Subgroup G} {z : G}
    (hM : Q3T8.Generic.IsClassicalMember M z) {L : Subgroup (OddQuot z)} (hL : CFSG.IsComponent L) :
    ⁅L, modOdd z M⁆ = ⊥ := by
  have hMC : M ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hM.subnormal
  have hsolv : Group.IsSolvable ↥M :=
    (IsClassicalMember3.isSolvable (hM.toQ3 (by norm_num : (3 : ℕ) ^ 1 = 3)))
  exact (CFSG.LocalCores.component_solvable_centralizer
    (isSolvable_modOdd_of_solvable hMC hsolv) (isSubnormal_modOdd_of_subnormal hM.subnormal)).1
      L hL

end Vertex

section Hyp51


theorem hyp51VertexThree_proved : Hyp51VertexThree := by
  intro G _ _ _ Ω K₀ hst K K' z x y e₁ e₂ hKΩ hK'Ω hzK hzK' B hB hzB hxK hyK' hxyB hxy1 hxyz
    _ _ _ _ _ _ _ _
  have hΩ : HypOmegaModT Ω := hst.modU
  have hc₁ : Q3T8.Generic.IsClassicalMember K z := isClassicalMember_of_twin hΩ hKΩ hzK
  have hc₂ : Q3T8.Generic.IsClassicalMember K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hz1 : z ≠ 1 := hzK.ne_one
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hc₁.subnormal
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hc₂.subnormal
  have hx' : x ∈ Subgroup.centralizer ({z} : Set G) := hKz hxK
  have hy' : y ∈ Subgroup.centralizer ({z} : Set G) := hK'z hyK'
  have hxC : x * y ∈ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.centralizer ({z} : Set G)).mul_mem hx' hy'
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L → MovedByAll B z L → False := by
    intro L hL hmov
    have hxm : oddQuotMk z ⟨x * y, hxC⟩ ∈ modOdd z B := oddQuotMk_mem_modOdd hxyB hxC
    have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 hxyB hxy1 hxyz hxC
    obtain ⟨w, hw, hwne⟩ := hmov _ hxm hnot
    apply hwne
    have hcx : ∀ v ∈ L, v * oddQuotMk z ⟨x, hx'⟩ = oddQuotMk z ⟨x, hx'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨x, hx'⟩⁆ ∈ ⁅L, modOdd z K⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hxK hx')
      rw [commutator_component_modOdd_of_member hc₁ hL, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hcy : ∀ v ∈ L, v * oddQuotMk z ⟨y, hy'⟩ = oddQuotMk z ⟨y, hy'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨y, hy'⟩⁆ ∈ ⁅L, modOdd z K'⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hyK' hy')
      rw [commutator_component_modOdd_of_member hc₂ hL, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have e1 : oddQuotMk z ⟨x * y, hxC⟩ = oddQuotMk z ⟨x, hx'⟩ * oddQuotMk z ⟨y, hy'⟩ := by
      rw [← map_mul]
      rfl
    rw [e1, mul_assoc, ← hcy w hw, ← mul_assoc, ← hcx w hw, mul_assoc]
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end Hyp51

end CFSG.ClassicalInvolution.Q3.Q3T7P24

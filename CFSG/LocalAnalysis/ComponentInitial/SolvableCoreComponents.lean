module

public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem not_le_of_isComponent_of_isSolvable {K R : Subgroup H} (hK : CFSG.IsComponent K)
    (hR : Group.IsSolvable R) : ¬ K ≤ R := by
  intro hKR
  have : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hKR)
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect K := hK.1.1
  exact Group.IsPerfect.not_isSolvable (G := K) ‹_›

theorem isPComponent_of_isComponent_of_not_le (p : ℕ) {K : Subgroup H} (hK : CFSG.IsComponent K)
    (hKR : ¬ K ≤ CFSG.pPrimeCore p H) : CFSG.IsPComponent p K := by
  set R := CFSG.pPrimeCore p H with hRdef
  have hKq := assembly_isQuasisimple_of_isComponent hK
  have hKRc : (R.subgroupOf K) ≤ center K := by
    rcases quasisimple_normal_subgroups hK.1 ((CFSG.pPrimeCore_normal (p := p) (G := H)).subgroupOf K) with
      h | h
    · exact absurd (fun k hk => (Subgroup.mem_subgroupOf.1
        (h ▸ Subgroup.mem_top (⟨k, hk⟩ : K)) : (k : H) ∈ R)) hKR
    · exact h
  refine ⟨K.map (QuotientGroup.mk' R), component_quotient_image hK hKR, hK.2, rfl, ?_⟩
  intro D hDK _ hDmap
  apply (lt_iff_le_not_ge.1 hDK).2
  have hdecomp : ∀ k ∈ K, ∃ d ∈ D, ∃ z ∈ K, z ∈ R ∧ d * z = k ∧ ∀ y ∈ K, Commute z y := by
    intro k hk
    obtain ⟨d, hd, hdk⟩ : QuotientGroup.mk' R k ∈ D.map (QuotientGroup.mk' R) :=
      hDmap ▸ ⟨k, hk, rfl⟩
    have hz : d⁻¹ * k ∈ R := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (QuotientGroup.mk' R d)⁻¹ * QuotientGroup.mk' R k = 1
      rw [hdk, inv_mul_cancel]
    have hzK : d⁻¹ * k ∈ K := mul_mem (inv_mem (hDK.le hd)) hk
    have hzc : (⟨d⁻¹ * k, hzK⟩ : K) ∈ center K := hKRc (Subgroup.mem_subgroupOf.2 hz)
    refine ⟨d, hd, d⁻¹ * k, hzK, hz, mul_inv_cancel_left d k, fun y hy => ?_⟩
    exact (congrArg Subtype.val (mem_center_iff.1 hzc ⟨y, hy⟩)).symm
  rw [← commutator_self_of_isQuasisimple hKq, commutator_le]
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨d₁, hd₁, z₁, hz₁K, -, rfl, hz₁⟩ := hdecomp k₁ hk₁
  obtain ⟨d₂, hd₂, z₂, hz₂K, -, rfl, hz₂⟩ := hdecomp k₂ hk₂
  rw [commutatorElement_mul_mul_of_commute (hz₁ _ (hDK.le hd₂)) (hz₁ _ hz₂K)
    (hz₂ _ (hDK.le hd₁))]
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)

theorem solvable_prime_core_ordinary_components (p : ℕ) (_hp : p.Prime)
    (hR : Group.IsSolvable (CFSG.pPrimeCore p H)) :
    (∀ K : Subgroup H, CFSG.IsComponent K → CFSG.IsPComponent p K) ∧
      CFSG.layer H ≤ CFSG.pLayer H p ∧
      ((∀ L : Subgroup H, CFSG.IsPComponent p L → CFSG.IsComponent L) →
        CFSG.layer H = CFSG.pLayer H p) := by
  have hcomp : ∀ K : Subgroup H, CFSG.IsComponent K → CFSG.IsPComponent p K := fun K hK =>
    isPComponent_of_isComponent_of_not_le p hK (not_le_of_isComponent_of_isSolvable hK hR)
  have hle : CFSG.layer H ≤ CFSG.pLayer H p := sSup_le_sSup fun K hK => hcomp K hK
  exact ⟨hcomp, hle, fun h => le_antisymm hle (sSup_le_sSup fun L hL => h L hL)⟩

end CFSG.LocalAnalysis.ComponentInitial

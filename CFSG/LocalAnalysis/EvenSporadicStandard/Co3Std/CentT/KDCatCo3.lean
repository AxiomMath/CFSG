module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Co3Inv
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

theorem false_of_perfect_index_two {G : Type*} [Group G] (hG : commutator G = ⊤)
    {H : Subgroup G} (h : H.index = 2) : False := by
  haveI : H.Normal := Subgroup.normal_of_index_eq_two h
  have hq : Nat.card (G ⧸ H) = 2 := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hq
  have hcomm : ∀ a b : G ⧸ H, a * b = b * a := fun a b => by
    letI : CommGroup (G ⧸ H) := IsCyclic.commGroup
    exact mul_comm a b
  have hle : commutator G ≤ H := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    have h1 : QuotientGroup.mk' H ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    exact (QuotientGroup.eq_one_iff _).1 h1
  have htop : H = ⊤ := top_le_iff.1 (hG ▸ hle)
  rw [htop, Subgroup.index_top] at h
  omega

section Co3


theorem kd_false_of_co3 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (es : S ≃* Carrier .Co3) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hinn : σ ∈ (MulAut.conj : S →* MulAut S).range)
    {Dbar : Subgroup S} (hle : Dbar ≤ fixedSubgroup σ) (hcard : Nat.card ↥Dbar = 1451520) :
    False := by
  obtain ⟨u, hu⟩ := hinn
  have hκ := CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna
  have hu2 : orderOf u = 2 := by
    rw [← orderOf_injective _ hκ u, hu]
    exact hσ
  have hfix : fixedSubgroup σ = centralizer ({u} : Set S) := by
    rw [← hu]
    ext x
    rw [mem_centralizer_singleton_iff]
    change u * x * u⁻¹ = x ↔ x * u = u * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hΛ : IsSporadic ↥(⊤ : Subgroup S) .Co3 := ⟨Subgroup.topEquiv.trans es⟩
  have hCle : Dbar ≤ (⊤ : Subgroup S) ⊓ centralizer ({u} : Set S) :=
    le_inf le_top (hfix ▸ hle)
  rcases co3_centralizer_cases hΛ (Subgroup.mem_top u) hu2 with ⟨⟨e⟩⟩ | ⟨N, -, -, -, hC⟩
  ·
    have hTwo : IsTwoSp62 ↥((⊤ : Subgroup S) ⊓ centralizer ({u} : Set S)) :=
      IsTwoSp62.of_mulEquiv e.symm isTwoSp62_co3M
    have hCcard : Nat.card ↥((⊤ : Subgroup S) ⊓ centralizer ({u} : Set S)) = 2 * 1451520 := by
      have h := hTwo.isSp62Cover.card_eq
      rw [hTwo.2.1] at h
      exact h
    have hD'card : Nat.card ↥(Dbar.subgroupOf ((⊤ : Subgroup S) ⊓ centralizer ({u} : Set S))) =
        1451520 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCle).toEquiv).trans hcard
    have hidx : (Dbar.subgroupOf ((⊤ : Subgroup S) ⊓ centralizer ({u} : Set S))).index = 2 := by
      have h := Subgroup.card_mul_index
        (Dbar.subgroupOf ((⊤ : Subgroup S) ⊓ centralizer ({u} : Set S)))
      rw [hD'card, hCcard] at h
      omega
    exact false_of_perfect_index_two hTwo.1 hidx
  ·
    have hdvd : Nat.card ↥Dbar ∣ Nat.card ↥((⊤ : Subgroup S) ⊓ centralizer ({u} : Set S)) :=
      Subgroup.card_dvd_of_le hCle
    rw [hC, hcard] at hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)

end Co3

end CFSG.EvenSporadicStandard.Co3Std.CentT

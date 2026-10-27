module

public import CFSG.CGT.PushingUpLit.SolKR2.Torus
public import CFSG.RankThree.GF2n.Tim78S31Model

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

namespace Data31

variable
  {U : Subgroup G} {g α x : G} (D : Data31 U g α x) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include D hCen hU

theorem card_omega_four : Nat.card ↥(PartTwo.omegaOneSub U) = 4 := by
  obtain ⟨f, hf2, hrel, hN', ⟨e⟩⟩ := D.linear hCen hU
  have hf : f = 2 := by
    by_contra hne
    exact D.false_of_linear hCen hU (by omega : 3 ≤ f) hrel e
  rw [D.card_eq hCen hU, hrel, hf]
  norm_num

theorem card_eq_sixteen : Nat.card ↥U = 16 := by
  have h1 := Subgroup.card_mul_index ((PartTwo.omegaOneSub U).subgroupOf U)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (PartTwo.omegaOneSub_le U)).toEquiv,
    D.card_omega_four hCen hU] at h1
  have h2 : ((PartTwo.omegaOneSub U).subgroupOf U).index = 4 := by
    have := D.card_eq hCen hU
    rw [D.card_omega_four hCen hU] at this
    exact this.symm
  rw [h2] at h1
  omega

theorem not_comm_UC : ¬ ∀ a ∈ U, ∀ b ∈ conjSubgroup x U, a * b = b * a := by
  intro h
  have P := D.pair
  obtain ⟨v, hv, hvN⟩ := P.exists_not_mem_N hCen hU (U ⊔ conjSubgroup α U).one_mem
  obtain ⟨w, hw, hwN⟩ := P.exists_not_mem_N hCen hU D.memX
  rw [conjSubgroup_one] at hv
  have hvw := h v hv w hw
  have heq := P.eq_of_commute hCen hU (U ⊔ conjSubgroup α U).one_mem D.memX
    (by rw [conjSubgroup_one]; exact hv) hvN hw hwN
    (by rw [hvw, mul_inv_cancel]; exact Subgroup.one_mem _)
  rw [conjSubgroup_one] at heq
  exact D.ne_C heq

theorem pairUC : NCPair U (conjSubgroup x U) := by
  have K := D.core
  have key : ∀ b ∈ PartTwo.omegaOneSub U, ∀ c ∈ conjSubgroup x U,
      b * c * b⁻¹ ∈ conjSubgroup x U := by
    intro b hb c hc
    have hbN : b ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U) :=
      Subgroup.mem_sup_left hb
    have h1 := D.pair.comm_mem_conj hCen hU D.memX hc hbN
    have h2 := (PartTwo.omegaOneSub (conjSubgroup x U)).inv_mem h1
    have e : b * c * b⁻¹ = (c * b * c⁻¹ * b⁻¹)⁻¹ * c := by group
    rw [e]
    exact (conjSubgroup x U).mul_mem (PartTwo.omegaOneSub_le _ h2) hc
  have hΩ : ∀ b ∈ PartTwo.omegaOneSub U, b ∈ Subgroup.normalizer (conjSubgroup x U : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => key b hb c hc, fun hc => ?_⟩
    have h1 := key b⁻¹ ((PartTwo.omegaOneSub U).inv_mem hb) _ hc
    rwa [show b⁻¹ * (b * c * b⁻¹) * b⁻¹⁻¹ = c by group] at h1
  refine ⟨⟨K.comm, K.two, K.exp_ne, K.ti, ⟨x, rfl⟩, ?_⟩, K.exp, D.not_comm_UC hCen hU⟩
  intro hbot
  obtain ⟨β, hβ, hβ1⟩ := K.exists_ne_one_omega 1
  rw [conjSubgroup_one] at hβ
  have hmem : β ∈ U ⊓ Subgroup.normalizer (conjSubgroup x U : Set G) :=
    Subgroup.mem_inf.2 ⟨PartTwo.omegaOneSub_le U hβ, hΩ β hβ⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hβ1 hmem

theorem exists_torus :
    ∃ K : Subgroup G, K ≤ U ⊔ conjSubgroup x U ∧ Nat.card ↥K = 3 ∧
      K ≤ Subgroup.normalizer (U : Set G) ∧
      K ≤ Subgroup.normalizer (conjSubgroup x U : Set G) ∧
      (∀ k ∈ K, k ≠ 1 → ∀ w ∈ PartTwo.omegaOneSub (conjSubgroup x U),
        k * w * k⁻¹ = w → w = 1) ∧
      (∀ k ∈ K, k ≠ 1 → ∀ w ∈ PartTwo.omegaOneSub U, k * w * k⁻¹ = w → w = 1) ∧
      (∀ k ∈ K, k ≠ 1 → ∀ s ∈ U,
        k * s * k⁻¹ * s⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) →
          s ∈ PartTwo.omegaOneSub U) ∧
      (∀ k ∈ K, k ≠ 1 → ∀ s ∈ conjSubgroup x U,
        k * s * k⁻¹ * s⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) →
          s ∈ PartTwo.omegaOneSub (conjSubgroup x U)) :=
  (D.pairUC hCen hU).exists_torus hCen hU (D.card_eq_sixteen hCen hU) (D.card_omega_four hCen hU)

end Data31

end CFSG.RankThree.GF2n.Tim78

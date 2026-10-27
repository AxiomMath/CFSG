module

public import CFSG.LieType.ChevTwo.OrthogonalBasic
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem GoodQ.omegaTwoAutInduced_of_card {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → ZMod 2) → ZMod 2} (hQ : GoodQ Q)
    (hcard : Nat.card (MulAut ↥(StatedOmega Q)) = 2 * Nat.card ↥(StatedOmega Q)) :
    OmegaTwoAutInduced Q := by
  intro α
  rw [inducedByIso_iff_mem_range]
  have h1 : Nat.card (kappa Q).range = Nat.card (isoGrp Q) :=
    (Nat.card_congr (MonoidHom.ofInjective hQ.kappa_injective).toEquiv).symm
  have h2 : Nat.card (isoGrp Q) = 2 * Nat.card (StatedOmega Q) := by
    have := Subgroup.relIndex_mul_card (H := StatedOmega Q) (K := isoGrp Q)
    rw [hQ.relIndex_eq, inf_of_le_left (statedOmega_le_isoGrp Q)] at this
    exact this.symm
  have htop : (kappa Q).range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [h1, h2, hcard])
  rw [htop]
  exact Subgroup.mem_top α

theorem card_mulAut_eq_two_mul_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Nat.card (MulAut H) = 2 * Nat.card H) : Nat.card (MulAut G) = 2 * Nat.card G := by
  rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv, h]

theorem card_mulAut_alternatingGroup {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut ↥(alternatingGroup (Fin n))) =
      2 * Nat.card ↥(alternatingGroup (Fin n)) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [two_mul_nat_card_alternatingGroup]
  exact (Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6))).symm

theorem card_mulAut_of_center_eq_bot_of_card_outer {K : Type*} [Group K]
    (hc : Subgroup.center K = ⊥) (ho : Nat.card (Outer K) = 2) :
    Nat.card (MulAut K) = 2 * Nat.card K := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner K)
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have : a ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun σ : MulAut K => σ g) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * a = (a * g * a⁻¹) * a := by rw [this]
        _ = a * g := by group
    rw [hc, Subgroup.mem_bot] at this
    exact this
  have h2 : Nat.card (inner K) = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  change Nat.card (MulAut K) = Nat.card (Outer K) * Nat.card (inner K) at h1
  rw [h1, ho, h2]

private theorem center_eq_bot_of_isSimpleGroup_of_not_comm {K : Type*} [Group K] (hs : IsSimpleGroup K)
    (hna : ¬ ∀ x y : K, x * y = y * x) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h0 | h1
  · exact h0
  · exact absurd (fun x y => (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y)) x) hna

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag in
theorem card_mulAut_statedOmega_quadMinus_three :
    Nat.card (MulAut ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1))) =
      2 * Nat.card ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) := by
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨E, _, h, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      hK hirr
  obtain ⟨hsimple, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (Or.inr rfl) hirr
  have : Finite E := h.finite
  have hE : Nat.card E = (2 ^ 1) ^ 2 := by rw [h.card_eq_sq]
  have hcenterT : Subgroup.center (StatedSU 4 (2 ^ 1) E) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_not_comm (by have := hsimple; exact eSU.symm.isSimpleGroup)
      fun hc => hna fun x y => eSU.injective (by rw [map_mul, map_mul, hc])
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hscal : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    rw [← (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := 1) hE (by norm_num) hnq).2, hcenterT]
  let ψ : unitaryPSU h 4 ≃* StatedSU 4 (2 ^ 1) E :=
    (unitaryPSUEquiv h (n := 4) (by norm_num)).trans
      ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot)
  have hout : Nat.card (Outer (unitaryPSU h 4)) = 2 := by
    have := (UnitaryHigher.unitary_full_diagonal_outer_order h (n := 4) (by norm_num)
      (by norm_num)).2.2.2.2.1
    rw [this]
    norm_num
  let e : ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) ≃* unitaryPSU h 4 := eSU.trans ψ.symm
  apply card_mulAut_of_center_eq_bot_of_card_outer
    (center_eq_bot_of_isSimpleGroup_of_not_comm hsimple hna)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact hout

theorem omegaTwoAutInduced_minus_one :
    OmegaTwoAutInduced (StatedQuadMinus 2 (ZMod 2) 1 1) :=
  (goodQ_minus (n := 1) le_rfl).omegaTwoAutInduced_of_card
    (card_mulAut_eq_two_mul_of_mulEquiv
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_two_mulEquiv_alt5
      (card_mulAut_alternatingGroup le_rfl (by decide)))

theorem omegaTwoAutInduced_minus_two :
    OmegaTwoAutInduced (StatedQuadMinus 3 (ZMod 2) 1 1) :=
  (goodQ_minus (n := 2) (by norm_num)).omegaTwoAutInduced_of_card
    card_mulAut_statedOmega_quadMinus_three

theorem omegaTwoAutInduced_plus_two :
    OmegaTwoAutInduced (StatedQuadPlus 3 (ZMod 2)) :=
  (goodQ_plus (n := 2) le_rfl).omegaTwoAutInduced_of_card
    (card_mulAut_eq_two_mul_of_mulEquiv
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_three_mulEquiv_alt8
      (card_mulAut_alternatingGroup (by norm_num) (by decide)))

end CFSG.LieType.ChevTwo

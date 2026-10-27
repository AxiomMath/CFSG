module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.OrthCentGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem autU42Five : AutU42Five := by
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
  have hsimpleT : IsSimpleGroup (StatedSU 4 (2 ^ 1) E) := by
    have := hsimple
    exact eSU.symm.isSimpleGroup
  have hnaT : ¬ ∀ x y : StatedSU 4 (2 ^ 1) E, x * y = y * x := fun hc =>
    hna fun x y => eSU.injective (by rw [map_mul, map_mul, hc])
  have hcenter : Subgroup.center (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    have := hsimpleT
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedSU 4 (2 ^ 1) E)) with h0 | h1
    · exact h0
    · exact absurd (fun x y => (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y)) x) hnaT
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hscal : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    rw [← (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := 1) hE (by norm_num) hnq).2, hcenter]
  let ψ : unitaryPSU h 4 ≃* StatedSU 4 (2 ^ 1) E :=
    (unitaryPSUEquiv h (n := 4) (by norm_num)).trans
      ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot)
  have hout : Nat.card (Outer (unitaryPSU h 4)) = 2 := by
    have := (UnitaryHigher.unitary_full_diagonal_outer_order h (n := 4) (by norm_num)
      (by norm_num)).2.2.2.2.1
    rw [this]
    norm_num
  have hinner : ∀ τ : MulAut (unitaryPSU h 4), τ ^ 5 = 1 →
      τ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU h 4) := by
    intro τ hτ
    have h1 : orderOf (QuotientGroup.mk τ : Outer (unitaryPSU h 4)) ∣ 5 :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one])
    have h2 : orderOf (QuotientGroup.mk τ : Outer (unitaryPSU h 4)) ∣ 2 := by
      have := orderOf_dvd_natCard (QuotientGroup.mk τ : Outer (unitaryPSU h 4))
      rwa [hout] at this
    have h3 : orderOf (QuotientGroup.mk τ : Outer (unitaryPSU h 4)) = 1 :=
      Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  intro σ hσ
  exact exists_conj_of_mulEquiv (eSU.trans ψ.symm) 5 hinner σ hσ

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

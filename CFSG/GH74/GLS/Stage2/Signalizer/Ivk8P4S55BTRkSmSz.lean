module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkSmK
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.Ree

namespace RkSm

theorem card_le_of_sq_suzuki {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (E : Subgroup (suzukiGroup a K))
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ Nat.card K := by
  classical
  have := finite_suzukiGroup hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hEQ⟩ := (isPGroup_of_sq hE).exists_le_sylow
  let P := Sylow.ofCard (suzukiU a K) (RankThree.card_suzukiU_eq hK)
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P Q
  have key : ∀ x ∈ E, ∃ v : K, x = g * suzukiSElt a K 0 v * g⁻¹ := by
    intro x hx
    have hxU : g⁻¹ * x * g ∈ suzukiU a K := (mem_smul_sylow_iff P g x).mp (hEQ hx)
    have h2 : (g⁻¹ * x * g) ^ 2 = 1 := by
      rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, ← map_pow, hE x hx, map_one]
    by_cases h1 : g⁻¹ * x * g = 1
    · refine ⟨0, ?_⟩
      rw [suzukiSElt_zero_zero hK, ← h1]
      group
    · obtain ⟨v, -, hv⟩ := RankThree.eq_suzukiSElt_zero_of_sq_eq_one hK hxU h2 h1
      exact ⟨v, by rw [← hv]; group⟩
  choose f hf using key
  refine Nat.card_le_card_of_injective (fun x : E => f x x.2) fun x y hxy => Subtype.ext ?_
  have hxy' : f x x.2 = f y y.2 := hxy
  rw [hf x x.2, hf y y.2, hxy']

end RkSm

theorem rankCell_l28sz8 :
    RankCell (fun Y _ => LieModel Y .PSL 2 2 3 ∨ LieModel Y .twistedB2 0 2 3) := by
  intro k hk Y _ _ _ hY
  have := RkSm.finite_mulAut (Y := Y)
  rcases hY with h | h
  · have hst : StatedClassicalModel Y .PSL 2 2 3 := by
      rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact h
      all_goals exact absurd h0 (by norm_num)
    have hb := LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound Y 2 2 3 hst
    have hY : Nat.card Y = 504 := by
      rw [hb.1]
      decide
    have hO : Nat.card (Outer Y) ∣ 3 := (hb.2.2.2.1 rfl).trans (by norm_num)
    have hc : center Y = ⊥ := RkSm.center_eq_bot (by rw [hY]; norm_num)
    refine ⟨RkSm.not_kindFactorAll hk hY (a := 10) (by norm_num) (by norm_num)
      (RkSm.not_isSection_alt7_of_card hY), ?_⟩
    refine RkSm.admRank3_of_sq fun E hE => RkSm.card_le_eight_of_not_dvd ?_ E hE
    rw [RkSm.card_mulAut hc, hY]
    rcases (Nat.dvd_prime Nat.prime_three).mp hO with h1 | h3
    · rw [h1]
      norm_num
    · rw [h3]
      norm_num
  · obtain ⟨-, -, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ :=
      RankThree.PartOne.Sec66T.lieModel_twistedB2_iff.mp h
    obtain rfl : a = 1 := by omega
    have hK' : Nat.card K = 2 ^ (2 * 1 + 1) := hK
    have hY : Nat.card Y = 29120 := by
      rw [Nat.card_congr e.toEquiv, suzuki_order hK']
      norm_num
    have hc : center Y = ⊥ := RkSm.center_eq_bot (by rw [hY]; norm_num)
    refine ⟨RkSm.not_kindFactorAll hk hY (a := 38) (by norm_num) (by norm_num)
      (RkSm.not_isSection_of_not_dvd hY (by norm_num)), ?_⟩
    have hodd : Odd (Nat.card (Outer Y)) := by
      rw [Nat.card_congr (equivalence e).toEquiv]
      exact (RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting 1 le_rfl K
        hK').2.2.2.2.2.2
    refine RkSm.admRank3_of_sq fun E hE => RkSm.card_le_of_inner hc hodd
      (RkSm.bound_of_mulEquiv e fun E' hE' => ?_) E hE
    exact (RkSm.card_le_of_sq_suzuki hK' E' hE').trans (hK'.le.trans (by norm_num))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

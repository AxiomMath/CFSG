module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74L38
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ThreeL38Bal
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ThreeL38Conn

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CliffordAlgebra CFSG.LieType.Universal.Spin
open CFSG.OddStandard.Solomon75 CFSG.OddStandard.Solomon75.CoreAux

theorem nonempty_mulEquiv_spinSeven_odd {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hY : IsCoverOf .POmegaOdd 3 p f 2 Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (Y ≃* spinGroup (quadOdd 3 K)) := by
  rcases pow_eq_three_or_five_le_of_isCoverOf hp hp2 hY with h3 | h5
  · obtain ⟨K, _, _, hK, e⟩ := nonempty_mulEquiv_spinSeven_three h3 hY
    exact ⟨K, inferInstance, inferInstance, hK.trans h3.symm, e⟩
  · obtain ⟨K, _, _, hK, -, -, -, e⟩ := nonempty_mulEquiv_spinOdd h5 hY
    exact ⟨K, inferInstance, inferInstance, hK, e⟩


theorem pPrimeCore_eq_bot_of_hyp31iOdd {G : Type} [Group G] [Finite G] {z : G} {p f : ℕ}
    (h : Hyp31iOdd G z p f) : pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ := by
  have : IsSimpleGroup G := h.simple
  obtain ⟨Lb, hLn, hLi, hL, hCL⟩ := h.spin
  have hbal := L38.oddCoreBalanced_of_hypOdd h
  have hLcard := L38.card_of_isCoverOf h.hp h.hp2 hL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_spinSeven_odd h.hp h.hp2 hL
  have : Finite (spinGroup (quadOdd 3 K)) := Finite.of_equiv _ e.toEquiv
  have hXcard : Nat.card (spinGroup (quadOdd 3 K)) = Nat.card K ^ 9 *
      ((Nat.card K ^ 2 - 1) * ((Nat.card K ^ 4 - 1) * (Nat.card K ^ 6 - 1))) := by
    rw [← Nat.card_congr e.toEquiv, hLcard, hK]
  obtain ⟨S, hSz⟩ := L38.exists_sylow_le_cen h.hz h.oneClass
  obtain ⟨P, ⟨eS⟩⟩ := L38.exists_sylow_mulEquiv hLn hLi e S hSz
  obtain ⟨hconnP, hrankP⟩ := L38.spin_sylow_connected_odd h.hp h.hp2 hK hXcard P
  have hconn := L38.connected_of_mulEquiv eS.symm hconnP
  have h3 : 3 ≤ Open.pRank 2 (S : Subgroup G) := by
    rw [CFSG.RankThreeEvenClassification.Helpers.pRank_eq_of_subgroup_equiv 2 Nat.prime_two _ _
      eS]
    exact hrankP
  obtain ⟨E, hES, hEab, hEcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained 2 Nat.prime_two (S : Subgroup G)
  have hE8 : 8 ≤ Nat.card E := by
    rw [hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ Open.pRank 2 (S : Subgroup G) := Nat.pow_le_pow_right (by norm_num) h3
  have hE2 : 2 ≤ Open.pRank 2 E := le_trans (by omega) (L38.le_pRank_of_le le_rfl hEab hEcard)
  obtain ⟨U₀, hU₀E, hU₀ab, hU₀4⟩ := exists_fourSub_of_two_le_pRank hE2
  have hWE : Wsub U₀ = Wsub E := Wsub_eq_of_le hbal hEab hE8 hU₀E hU₀4
  obtain ⟨hWodd, -, -⟩ := Wsub_complete hbal hEab hE8
  have hcard2 : 2 ∣ Nat.card G := h.hz ▸ orderOf_dvd_natCard z
  have hW : Wsub U₀ = ⊥ := by
    by_contra hW1
    have hnormW : normalizer (Wsub U₀ : Set G) ≠ ⊤ := by
      intro htop
      have hnormal : (Wsub U₀).Normal := normalizer_eq_top_iff.mp htop
      rcases hnormal.eq_bot_or_eq_top with h' | h'
      · exact hW1 h'
      · have : Odd (Nat.card (Wsub U₀)) := hWE ▸ hWodd
        rw [h', Subgroup.card_top] at this
        exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr hcard2)
    have hgamma := gamma_le_normalizer_W hbal hconn ⟨U₀, hU₀E.trans hES, hU₀ab, hU₀4⟩
    have hne : Open.properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤ := fun htop =>
      hnormW (top_le_iff.mp (htop ▸ hgamma))
    rcases CFSG.Milestones.cl_lit_aschbacher_proper_two_generated_core G h.nonab S h3 hne with
      h1 | ⟨⟨eJ⟩⟩
    · exact ClassicalInvolution.false_of_gamma_one_ne_top S h3 h1 h.hz le_rfl
        (L38.not_isSolvable_cen hL)
    · have hcardG : Nat.card G = 175560 := by
        rw [Nat.card_congr eJ.toEquiv, ClassicalInvolution.properTwoGenCoreJ1_eq_walterJ1]
        exact CFSG.Walter.J1Props.card_walterJ1
      have hLG : Nat.card Lb ∣ Nat.card G := (card_subgroup_dvd_card Lb).trans
        ((card_quotient_dvd_card _).trans (card_subgroup_dvd_card _))
      have h1 := Nat.le_of_dvd Nat.card_pos hLG
      rw [hLcard, hcardG] at h1
      have hq3 : 3 ≤ p ^ f := by
        rcases pow_eq_three_or_five_le_of_isCoverOf h.hp h.hp2 hL with h3 | h5 <;> omega
      generalize p ^ f = q at h1 hq3
      have h2 : 3 ^ 9 ≤ q ^ 9 := Nat.pow_le_pow_left hq3 9
      have ha : 8 ≤ q ^ 2 - 1 := by
        have := Nat.pow_le_pow_left hq3 2
        omega
      have hb : 80 ≤ q ^ 4 - 1 := by
        have := Nat.pow_le_pow_left hq3 4
        omega
      have hc : 1 ≤ q ^ 6 - 1 := by
        have := Nat.pow_le_pow_left hq3 6
        omega
      have h4 : 12597120 ≤ q ^ 9 * ((q ^ 2 - 1) * ((q ^ 4 - 1) * (q ^ 6 - 1))) :=
        le_trans (by norm_num) (Nat.mul_le_mul h2 (Nat.mul_le_mul ha (Nat.mul_le_mul hb hc)))
      omega
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨⟨a, haE⟩, ha⟩ := exists_ne (1 : E)
    exact ⟨a, haE, fun h => ha (Subtype.ext h)⟩
  have ha2 : orderOf a = 2 := orderOf_eq_two_of_isElemAbelian hEab haE ha1
  have hbot : OddStandard.Solomon75.oddCoreOf (cen a) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc OddStandard.Solomon75.oddCoreOf (cen a) ≤ Wsub E := oddCoreOf_cen_le_Wsub haE ha1
      _ = ⊥ := hWE ▸ hW
  obtain ⟨g, rfl⟩ := h.oneClass a ha2
  rw [cen_conj, oddCoreOf_map_equiv (MulAut.conj g) (cen z)] at hbot
  have hbot' : OddStandard.Solomon75.oddCoreOf (cen z) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ (cen z).subtype_injective).mp hbot'

theorem lemma38Odd_holds : Lemma38Odd := by
  intro G _ _ z p f h
  obtain ⟨Lb, -, -, hL, -⟩ := h.spin
  rcases pow_eq_three_or_five_le_of_isCoverOf h.hp h.hp2 hL with h3 | h5
  · exact pPrimeCore_eq_bot_of_hyp31iOdd h
  · exact lemma38_holds G z p f (h.toHyp31i h5)

end CFSG.ComponentClassification.HarrisLit.T1.S74

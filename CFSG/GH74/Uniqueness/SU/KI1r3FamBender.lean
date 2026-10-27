module

public import CFSG.GH74.Uniqueness.SU.KI1r3FamDefs
public import CFSG.GH74.KGroups.L28Tables
public import CFSG.GH74.KGroups.Sz8Tables
public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenAllInvolutionFourGroup

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem fourFix_of_out_inner {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a)
    (h : ∀ (φ : MulAut K) (n : ℕ), φ ^ 2 ^ n = 1 → ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹) :
    FourFix K := by
  have := hs
  refine FourFix.of_inner hnab fun α hα => ?_
  obtain ⟨k, hk⟩ := h α 1 (by rwa [pow_one])
  exact ⟨k, MulEquiv.ext fun x => (hk x).trans (MulAut.conj_apply k x).symm⟩

theorem four_le_twoRank_of_lieModel_psl {K : Type} [Group K] [Finite K] {n f r : ℕ}
    (h : LieModel K .PSL n 2 f) (hn : 2 ≤ n) (hr : r ≤ f * (n / 2 * ((n + 1) / 2))) :
    r ≤ Open.twoRank K := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StatedProj (StatedSL n F)) := Finite.of_equiv K e.toEquiv
  have h1 := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := n) (a := n / 2) (b := (n + 1) / 2)
    (by omega) (by omega) hF
  have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) (by norm_num) e
  unfold Open.twoRank
  omega

theorem fourFix_L28
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (h : LieModel K .PSL 2 2 3) : FourFix K :=
  fourFix_of_out_inner hs hnab fun φ n hφ => CFSG.GH74.KGroups.L28.out_inner h φ n hφ

theorem fourFix_L216 {K : Type} [Group K] [Finite K]
    (h : LieModel K .PSL 2 2 4) : FourFix K :=
  FourFix.of_four_le_twoRank (four_le_twoRank_of_lieModel_psl h (by norm_num) (by norm_num))

theorem fourFix_L34 {K : Type} [Group K] [Finite K]
    (h : LieModel K .PSL 3 2 2) : FourFix K :=
  FourFix.of_four_le_twoRank (four_le_twoRank_of_lieModel_psl h (by norm_num) (by norm_num))

theorem fourFix_U34 {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (h : LieModel K .PSU 3 2 2) : FourFix K := by
  have := hs
  intro α hα
  left
  obtain ⟨V, hV, hVel, hVc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_unitary_all_involution_fixed_four_group
      K hnab (CFSG.GH74.Generic.stated_of_lieModel_PSU h) α hα
  exact ⟨V, fun v hv => hV hv,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp hVel, hVc⟩

theorem fourFix_Sz8
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (h : LieModel K .twistedB2 0 2 3) : FourFix K :=
  fourFix_of_out_inner hs hnab fun φ n hφ => CFSG.GH74.KGroups.Sz8.out_inner h φ n hφ

theorem famBender :
    FamBender := by
  intro K _ _ hs hnab h
  rcases h with h | h | h | h | h
  · exact fourFix_L28 hs hnab h
  · exact fourFix_L216 h
  · exact fourFix_L34 h
  · exact fourFix_U34 hs hnab h
  · exact fourFix_Sz8 hs hnab h

end CFSG.GH74.Uniqueness.SU.K.R3

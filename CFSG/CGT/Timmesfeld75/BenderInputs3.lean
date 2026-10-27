module

public import CFSG.CGT.Timmesfeld75.PaperSteps
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.GH74.Bender.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.BenderSuzuki

theorem statedClassicalModel_psl2_of_mulEquiv {K : Type} [Group K] {n : ℕ} (hn : 2 ≤ n)
    (e : K ≃* PSL2Model n) : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL 2 2 n := by
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩,
    GaloisField 2 n, inferInstance, inferInstance, GaloisField.card 2 n (by omega),
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 n))⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem statedClassicalModel_psu3_of_mulEquiv {K : Type} [Group K] {n : ℕ} (hn : 2 ≤ n)
    (e : K ≃* PSU3Model n) : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 2 n := by
  have hc : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  let eC : CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) (GaloisField 2 (2 * n)) (2 ^ n)) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) (GaloisField 2 (2 * n))) :=
    MulEquiv.refl _
  exact ⟨CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible n hn, GaloisField 2 (2 * n),
    inferInstance, inferInstance, hc,
    ⟨((e.trans (MulEquiv.subgroupCongr (show PSU3Model n = CFSG.Open.PSU3 2 n from rfl))).trans
      (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative n).symm).trans eC⟩⟩

theorem lieModel_twistedB2_of_mulEquiv_szModel {K : Type} [Group K] {a : ℕ} (ha : 1 ≤ a)
    (e : K ≃* SzModel a) : CFSG.Blueprint.LieModel K .twistedB2 0 2 (2 * a + 1) :=
  Or.inr (Or.inr (Or.inr ⟨rfl, rfl, CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz ha
    (e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz a)))⟩))

theorem benderListInput_of_repo : BenderListInput := by
  intro K _ hK
  rcases hK with ⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩
  · exact Or.inl ⟨2, n, le_rfl, by omega, statedClassicalModel_psl2_of_mulEquiv hn e⟩
  · exact Or.inr (Or.inr (Or.inl ⟨2 * a + 1, odd_two_mul_add_one a, by omega,
      lieModel_twistedB2_of_mulEquiv_szModel ha e⟩))
  · exact Or.inr (Or.inl ⟨n, hn, statedClassicalModel_psu3_of_mulEquiv hn e⟩)

end CFSG.CGT.Timmesfeld75

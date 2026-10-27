module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.StandardType (GGLabelRigidInput ggLabelRigidInput_holds)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem innDiagSymp_of_ggLabelRigidInput (hRig : GGLabelRigidInput) : InnDiagSymp := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hα hlabJ hJ
  rcases Y10GInnSympMark.innDiagKind_symp_data hcen hFam hin with h1 |
    ⟨K, hK, hKf, m, hm, hcard, e, A, hαA⟩
  · rw [h1]
    exact one_dvd _
  have hn : 1 ≤ (canonLabel labK).n := by
    rcases Nat.eq_zero_or_pos (canonLabel labK).n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have h2 : (2 : K) = 0 := by
    haveI := Fintype.ofFinite K
    obtain ⟨q, hq, k, hqp, hqcard⟩ := FiniteField.card' K
    have hc := hcard
    rw [Nat.card_eq_fintype_card, hqcard] at hc
    have hdvd : q ∣ 2 ^ (canonLabel labK).n := by
      rw [← hc]
      exact dvd_pow_self q (PNat.ne_zero k)
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
    subst hq2
    exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨x, hx⟩ := Y10GInnSympRed.exists_conjAut_eq_conj h2 A
  have hMEq : MulAut.congr e α = MulAut.conj (proj m K x) := by
    rw [← hx]
    ext r
    have h1 := hαA (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hZ : Subgroup.center (StatedProj (StatedSp m K)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hz (e g)
    rw [hcen, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hz'
  have hpow : MulAut.conj (proj m K x) ^ p = 1 := by
    rw [← hMEq, ← map_pow, hα, map_one]
  have hxp : x ^ p = 1 := Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
  have hJ' : GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) (J.map e.toMonoidHom) := by
    rw [← hMEq, ← Y10F.fixSubgroup_map_congr]
    exact (Y10F.glaPComponent_map_iff hp e.injective).mpr hJ
  have hlabJ' := Y10F.hasLabel_transport e hlabJ
  rcases Y10GInnSympComp.quotCenter_cases_of_glaPComponent_conj hcard hn (by omega) hp hp2 x hxp
      hJ' with ⟨a, k, E, _, _, ha, hE, hnk, hφ⟩ | ⟨a, k, E, _, _, τ, hτ, ha, hτk, hE, hnk, hφ⟩ |
      ⟨s, hs, hne, ⟨φ⟩⟩ | hK2
  ·
    rw [Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig _ labJ a k E ha hE hlabJ' hφ]
    exact hnk
  ·
    rw [Y10GInnUni.uniLabelDict_of_ggLabelRigidInput hRig _ labJ a k E τ hτ ha hτk hE hlabJ' hφ]
    exact hnk
  ·
    rw [Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs hcard hne hlabJ' φ]
  ·
    have h1 : (canonLabel labK).n = 1 := by
      have h : 2 ^ (canonLabel labK).n = 2 ^ 1 := by rw [← hcard, hK2, pow_one]
      exact Nat.pow_right_injective le_rfl h
    rw [h1]
    exact one_dvd _

section Certificates


theorem innDiagSymp_holds : InnDiagSymp :=
  innDiagSymp_of_ggLabelRigidInput ggLabelRigidInput_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end

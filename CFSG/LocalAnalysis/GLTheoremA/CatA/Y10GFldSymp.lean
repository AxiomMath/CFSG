module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.StandardType (GGLabelRigidInput ggLabelRigidInput_holds)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem fldSymp_of_ggLabelRigidInput (hRig : GGLabelRigidInput) : FldSymp := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hfld hα hlabJ hJ
  haveI := Fact.mk hp
  obtain ⟨K, hK, hKf, m, hm, hn1, hcardK, hTag, hRank, e, u, hαu, huE, huD⟩ :=
    Y10GFldSympMark.fieldKind_symp_data hcen hFam hfld
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ p = 1 := by
    rw [← hMEq, ← map_pow, hα, map_one]
  have hu1 : u ≠ 1 := fun h1 => huD (h1 ▸ (spLinearAutGroup m K).one_mem)
  have hord : orderOf u = p := orderOf_eq_prime hpow hu1
  obtain ⟨hpn, σ, hσ, hσcard, h, -, hu⟩ :=
    (CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      Nat.prime_two hn1 hm hcardK).2.2.2.2.2.2.2.2.2 p hp u huE huD hord
  let e' : S ≃* StatedProj (StatedSp m K) := e.trans (h⁻¹ : MulAut _)
  have hcongr : MulAut.congr e' α = fieldAut m K σ := by
    have h1 : MulAut.congr e' α = h⁻¹ * u * h := by
      ext r
      change h⁻¹ (e (α (e.symm (h r)))) = h⁻¹ (u (h r))
      rw [hαu, MulEquiv.apply_symm_apply]
    rw [h1, hu]
    group
  have hJ' : GLAPComponent p (fixSubgroup (fieldAut m K σ)) (J.map e'.toMonoidHom) := by
    rw [← hcongr, ← Y10F.fixSubgroup_map_congr]
    exact (Y10F.glaPComponent_map_iff hp e'.injective).mpr hJ
  have hlabJ' := Y10F.hasLabel_transport e' hlabJ
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hk : Nat.card (descentField σ) = 2 ^ ((canonLabel labK).n / p) := hσcard
  have hpn' : (canonLabel labK).n = p * ((canonLabel labK).n / p) :=
    (Nat.mul_div_cancel' hpn).symm
  by_cases h22 : m = 2 ∧ Nat.card (descentField σ) = 2
  ·
    obtain ⟨hm2, hk2⟩ := h22
    subst hm2
    obtain ⟨φ⟩ :=
      Y10GFldSympComp.nonempty_quotCenter_equiv_alternating_of_glaPComponent_fieldAut hodd hσp
        hk2 hJ'
    have hlab := Y10GSympLabel.canonLabel_eq_of_quot_alternating hRig hlabJ' φ
    have hnp : (canonLabel labK).n / p = 1 := by
      have h2 : 2 ^ ((canonLabel labK).n / p) = 2 ^ 1 := by rw [← hk, hk2, pow_one]
      exact Nat.pow_right_injective le_rfl h2
    rw [hlab]
    exact ⟨hpn'.trans (by rw [hnp]), hTag, hRank⟩
  ·
    obtain ⟨φ⟩ :=
      Y10GFldSympComp.nonempty_quotCenter_equiv_of_glaPComponent_fieldAut hm hodd hσp h22 hJ'
    rw [Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hm hk h22 hlabJ' φ]
    exact ⟨hpn', hTag, hRank⟩

section Certificates


theorem fldSymp_holds : FldSymp :=
  fldSymp_of_ggLabelRigidInput ggLabelRigidInput_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end

module

public import CFSG.HardMathSupport.Foote.FamilyReduction.Abstract
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupFix
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem compIn5_of_isComponent_sl2_five {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hna : ∃ x y : Q, x * y ≠ y * x) {t : Q} (ht : orderOf t = 2)
    {B : Subgroup ↥(centralizer ({t} : Set Q))} (hB : IsComponent B) (htB : selfCent t ∈ B)
    (eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    CFSG.HardMathSupport.Foote.FamilyReduction.CompIn5 Q := by
  have hfix : fixedSubgroup (MulAut.conj t) = centralizer ({t} : Set Q) :=
    CFSG.OddStandard.AltStdSec.lookup_fixedSubgroup_conj t
  let φ : ↥(centralizer ({t} : Set Q)) ≃* ↥(fixedSubgroup (MulAut.conj t)) :=
    MulEquiv.subgroupCongr hfix.symm
  let K : Subgroup ↥(fixedSubgroup (MulAut.conj t)) := B.map φ.toMonoidHom
  have hK : IsComponent K := CFSG.LocalCores.isComponent_map_mulEquiv φ hB
  have hKe : Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    ⟨(B.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eB⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hconj2 : (MulAut.conj t : MulAut Q) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  have hconj1 : (MulAut.conj t : MulAut Q) ≠ 1 := by
    intro h
    have ht1 : t = 1 :=
      CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna
        (h.trans (map_one (MulAut.conj : Q →* MulAut Q)).symm)
    rw [ht1, orderOf_one] at ht
    exact (by norm_num : (1 : ℕ) ≠ 2) ht
  have hα : orderOf (MulAut.conj t : MulAut Q) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact orderOf_eq_prime hconj2 hconj1
  have hw : t ∈ fixedSubgroup (MulAut.conj t) := by
    rw [CFSG.HardMathSupport.Foote.FamilyReduction.mem_fixedSubgroup_iff, MulAut.conj_apply]
    group
  have hmem : φ (selfCent t) ∈ K := Subgroup.mem_map_of_mem φ.toMonoidHom htB
  have hφ : (⟨t, hw⟩ : ↥(fixedSubgroup (MulAut.conj t))) = φ (selfCent t) := by
    apply Subtype.ext
    simp only [MulEquiv.subgroupCongr_apply]
    rfl
  refine ⟨MulAut.conj t, t, rfl, hα, K, hK, hKe, hw, ?_⟩
  rwa [hφ]

end CFSG.ComponentClassification.HarrisLit.T1.SporRow

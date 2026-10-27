module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I148XMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

variable {G : Type} [Group G] [Finite G]

theorem k148f_cat_congr {S S' : Type} [Group S] [Group S'] {Q : TauCeti.CFSGIndex → Prop} (e : S ≃* S')
    (h : catalogIs S Q) : catalogIs S' Q := by
  obtain ⟨i, hi, ⟨e'⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans e'⟩⟩

@[expose] noncomputable def k148f_psimple_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem k148f_normalizes_fix {P : Type} [Group P] {τ : MulAut P} {c : P} (hc : τ c = c) :
    c ∈ Subgroup.normalizer ((CFSG.RankThree.PartTwo.Sec4.autFix τ : Subgroup P) : Set P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  rw [CFSG.RankThree.PartTwo.Sec4.mem_autFix, CFSG.RankThree.PartTwo.Sec4.mem_autFix]
  have hτ : τ (c * v * c⁻¹) = c * τ v * c⁻¹ := by
    rw [map_mul, map_mul, map_inv, hc]
  constructor
  · intro hv
    rw [hτ, hv]
  · intro hv
    rw [hτ] at hv
    exact mul_left_cancel (mul_right_cancel hv)

theorem k148f_fixedSub_eq {K : Subgroup G} {y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G)) :
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub
        (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩) = lemma102_fixSub 3 hyN := by
  ext w
  show CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩ w = w ↔ lemma102_conjQ 3 hyN w = w
  constructor
  · intro hw
    apply (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩).injective
    rw [barAut_comp_conjQ hyN w, hw]
  · intro hw
    have h := barAut_comp_conjQ hyN w
    rw [hw] at h
    exact h

theorem k148f_autFix_barAut {K : Subgroup G} {y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G))
    {c : PQuot 3 K} (hc : MulAut.conj c = CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩) :
    CFSG.RankThree.PartTwo.Sec4.autFix (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩) =
      Subgroup.centralizer ({c} : Set (PQuot 3 K)) := by
  rw [k148f_autFix_eq, k148f_fixedSub_eq hyN]
  exact lemma102_fixSub_eq_centralizer hyN hc

theorem k148f_barX_yK {K : Subgroup G} {y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hy3 : y ^ 3 = 1)
    {c : PQuot 3 K} (hc : MulAut.conj c = CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩) :
    barX 3 K (K ⊓ Subgroup.centralizer ({y} : Set G)) = Subgroup.centralizer ({c} : Set (PQuot 3 K)) := by
  rw [← k148f_autFix_barAut hyN hc, k148f_barX_cent hyN hy3]

end CFSG.LocalAnalysis.GLTheoremA.K148F

end

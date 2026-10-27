module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Res
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Inner
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83Alt
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section I1429Red


theorem i1429At_of_residuals (hOut : I1429SubfieldOut) (hIn : I1429InnerRest) (hTwo : I1429TwoRankSp4)
    (G : Type) [Group G] [Finite G] : I1429At G := by
  unfold I1429At
  intro X J K y _hX hJ hchev hy hy3 hnc hK hU4
  have hKJ : K ≤ J := hK.1.trans inf_le_left
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 J) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hβ3 := S8.L83.barAut_pow_three hy hy3
  have hβ1 : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 J ⟨y, hy⟩ ≠ 1 := by
    intro h1
    exact hnc (show CentMod 3 J y from ⟨hy, (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.barAut_eq_one_iff
      hy).1 h1⟩)
  have hI := S8.L83.imageMod_component_fix hy hy3 hK
  obtain ⟨e⟩ := S8.L83.pquot_imageMod (K := J) (J := K) Nat.prime_three hKJ
  have hU4I : catalogIs (PSimple 3 (imageMod 3 J K)) S9.isU4two :=
    (catalogIs_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm).1 hU4
  have hsub : catalogIs (PQuot 3 J ⧸ Subgroup.center (PQuot 3 J)) isSp4_27 := by
    by_cases hin : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 J ⟨y, hy⟩ ∈
        (MulAut.conj : PQuot 3 J →* MulAut (PQuot 3 J)).range
    · obtain ⟨q, hq⟩ := hin
      have h3 : (MulAut.conj q) ^ 3 = 1 := by rw [hq]; exact hβ3
      have h1 : MulAut.conj q ≠ 1 := by rw [hq]; exact hβ1
      rw [← hq] at hI
      by_cases hcase : Subgroup.center (PQuot 3 J) = ⊥ ∧
          catalogIs (PQuot 3 J) (onLie fun d => d.characteristic = 3)
      · exact absurd hI (i1429_inner_lie_simple hcase.1 hcase.2 q h3 h1 (imageMod 3 J K))
      · exact absurd hI (hIn (PQuot 3 J) hQ hchev hcase q h3 h1 (imageMod 3 J K))
    · exact hOut (PQuot 3 J) hQ hchev _ hβ3 hin (imageMod 3 J K) hI hU4I
  exact hTwo (PQuot 3 J) hQ hsub

theorem i1429At_of_residual (h : I1429Residual) (G : Type) [Group G] [Finite G] : I1429At G :=
  i1429At_of_residuals h.1 h.2.1 h.2.2 G

end I1429Red

end CFSG.LocalAnalysis.GLTheoremA

end

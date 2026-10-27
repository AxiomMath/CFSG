module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenA
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenDefs
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GL
public import CFSG.ClassicalInvolution.Q3.TL4E3C269Sec
public import CFSG.Goldschmidt.Steps.Rank2List

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace E3S3Gen

theorem exists_conj_psl3 {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    {a b : projectiveSL 3 K} (ha : orderOf a = 2) (hb : orderOf b = 2) :
    ∃ g : projectiveSL 3 K, g * a * g⁻¹ = b := by
  set φ := LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K with hφ
  have hφa := Goldschmidt.Rank2List.psl3_isConj hodd (t := φ.symm a)
    (by rw [MulEquiv.orderOf_eq]; exact ha)
  have hφb := Goldschmidt.Rank2List.psl3_isConj hodd (t := φ.symm b)
    (by rw [MulEquiv.orderOf_eq]; exact hb)
  obtain ⟨g, hg⟩ := isConj_iff.mp (hφa.trans hφb.symm)
  refine ⟨φ g, ?_⟩
  have h1 := congrArg φ hg
  rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1

end E3S3Gen

theorem e3S3GenL3_proved : E3S3GenL3 := by
  intro X _ _ hsimp p f hp hp2 hl t s ht hs htN hsN hts hne
  have := hsimp
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  obtain ⟨K, _, _, hK, ⟨e⟩, -⟩ := E3C269.exists_psl3_equiv hl
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  exact E3S3Gen.sup_centralizer_eq_top_of_normal e
    (fun a b ha hb hab hab' => E3C269G.sup_centralizer_eq_top_psl3 hodd ha hb hab hab')
    (fun a b ha hb => E3S3Gen.exists_conj_psl3 hodd ha hb) htN hsN ht hs hts hne

end CFSG.ClassicalInvolution.Q3.TL4

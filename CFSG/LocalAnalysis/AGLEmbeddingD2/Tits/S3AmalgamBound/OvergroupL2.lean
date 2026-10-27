module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsIndex

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer
  CFSG.BenderSuzuki.MatrixGroups CFSG.Models CFSG.Assembly.LowTwoRank

theorem overgroupEqTop_psl2 {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3) :
    OvergroupEqTop (PSL2MatrixGroup F) :=
  fun hcyc _ _ hA hNW hW =>
    OvergroupPSL2.eq_top_of_normalizer_le hF hp3
      (fun E _ _ y => CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le E y)
      (fun E _ _ y => CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le E y)
      hcyc hA hNW hW

theorem kFactOvergroupL2 : KFactOvergroupL2 := by
  intro K _ _ d q hq hd ⟨e2⟩ hK hcyc A W hA hNW hW _
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hmodel :=
    ThreeRankCls.statedClassical_of_lieModel (by omega) (lieModel_A 1 q hv e2)
  obtain ⟨-, F, instF, instFin, hF, ⟨eF⟩⟩ := hmodel
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e3 : K ≃* PSL2MatrixGroup F :=
    eF.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have htop := overgroupEqTop_of_mulEquiv e3 (overgroupEqTop_psl2 hF hq) hcyc A W hA hNW hW
  rw [htop, Subgroup.index_top]
  exact odd_one

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

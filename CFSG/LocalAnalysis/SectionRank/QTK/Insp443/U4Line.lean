module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.C35Bridge
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OrthConcl
public import CFSG.Quasithin.H13.U4ParLineQuot
public import CFSG.Quasithin.Background.Omega4AutOn

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem KConfig.u4_line {m : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K)
    {L V : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0)}
    (hc : KConfig (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0) L V
      (CFSG.Quasithin.H13.U4Par.parP2 h)) :
    ConclKLeft (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0) L V
        (CFSG.Quasithin.H13.U4Par.parP2 h) ∧
      CFSG.Quasithin.IsPSL 2 2 (2 * m) (CFSG.Quasithin.ModO2 L) := by
  haveI := h.finite
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hL : L = perfectCore (CFSG.Quasithin.H13.U4Par.parP2 h) :=
    hc.eq_perfectCore_of_simple
      (CFSG.Quasithin.H13.U4Par.isSimpleGroup_modO2_perfectCore_parP2 h)
  subst hL
  have hpsl : CFSG.Quasithin.IsPSL 2 2 (2 * m)
      (CFSG.Quasithin.ModO2 (perfectCore (CFSG.Quasithin.H13.U4Par.parP2 h))) :=
    CFSG.Quasithin.H13.U4Par.isPSL_modO2_perfectCore_parP2 h
  have hQ : CFSG.Open.pCoreOf 2 (perfectCore (CFSG.Quasithin.H13.U4Par.parP2 h)) =
      CFSG.Quasithin.H13.U4Par.radQ2 h :=
    CFSG.Quasithin.H13.U4Par.pCoreOf_perfectCore_parP2_eq' h
  have hU : blockU (perfectCore (CFSG.Quasithin.H13.U4Par.parP2 h)) =
      CFSG.Quasithin.H13.U4Par.radQ2 h :=
    CFSG.Quasithin.H13.U4Par.blockU_perfectCore_parP2 h
  have hZ : blockZ (perfectCore (CFSG.Quasithin.H13.U4Par.parP2 h)) = ⊥ :=
    CFSG.Quasithin.H13.U4Par.blockZ_perfectCore_parP2 h
  have hVQ : V ≤ CFSG.Quasithin.H13.U4Par.radQ2 h := hQ ▸ hc.le_pCoreOf
  have hVN : (CFSG.Quasithin.H13.U4Par.lev2Hom h).range ≤
      Subgroup.normalizer (V : Set (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0)) :=
    (CFSG.Quasithin.H13.U4Par.lev2Hom_range_le_perfectCore h).trans hc.le_normalizer
  have hV : V = CFSG.Quasithin.H13.U4Par.radQ2 h := by
    rcases CFSG.Quasithin.H13.U4Par.radQ2_irreducible h V hVQ hVN with hbot | htop
    · exact absurd hbot hc.ne_bot
    · exact htop
  have hVU : V = blockU (perfectCore (CFSG.Quasithin.H13.U4Par.parP2 h)) :=
    hV.trans hU.symm
  subst hVU
  haveI hcomm : IsMulCommutative ↥(blockU (perfectCore
      (CFSG.Quasithin.H13.U4Par.parP2 h))) := hc.elemAbelian.1
  have hO : BinaryOrthogonalFour (V := ↥(blockU (perfectCore
        (CFSG.Quasithin.H13.U4Par.parP2 h))))
      (autOn (perfectCore (CFSG.Quasithin.H13.U4Par.parP2 h))
        (blockU (perfectCore (CFSG.Quasithin.H13.U4Par.parP2 h)))) ⊤ ⊥ m :=
    CFSG.Quasithin.IsOmega4MinusType.binaryOrthogonalFour_autOn
      (CFSG.Quasithin.F112R.isOmega4MinusType_perfectCore_parP2 h) hZ
      hc.le_normalizer hc.pCoreOf_le
  exact ⟨conclKLeft_of_binaryOrthogonalFour (m := m) h.one_le hpsl hO, hpsl⟩

end CFSG.SectionRank.QTK.Insp443

end

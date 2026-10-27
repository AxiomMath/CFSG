module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12MainCertB4
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OB1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OB3
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OB4
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3q510
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CHInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CK512
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Final16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1THolds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5NRankMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFactsF1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L65
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI9
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5B5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Wire.KForms

public section

namespace CFSG.OddStandard.SmallF3

open CFSG.OddStandard.SmallF3.Omega

theorem ys09asm_h6m (F : Sec8T84Base) (hS : Asc82SchurU43) (h84K : Asc82Thm84K) :
    AschOmega6Minus :=
  aschOmega6Minus_of_tab6_full F.hShapes F.h36 F.h37 F.h83 F.h68 F.h82
    (asc82ZExists_of F.h36 hS) F.hM F.hN (ys09asm_thm84_of_K h84K)

theorem ys09asm_sec5Inputs16 (hS : Asc82SchurU43) (hCorIIIq : Asc82CorIIIq) (hTab : Asc82Tab5)
    (hTab56 : Asc82Tab56) (hL58b : Asc82Lemma58b) (hL58d : Asc82Lemma58d) (hSym : Asc82Sym59)
    (hPoc : Asc82Pocket510) (hF513 : Asc82Fact513Comm) (hPockets6 : Asc82FactPockets6)
    (hQCent : U43OddAutTwoPlusCent) (hFrame6 : Asc82FactFrame6)
    (hOutZeta6 : Asc82FactOutZeta6) (hQCentExp : Asc82FactQCentExp6)
    (hQBCent : Asc82FactQBCent6) : Asc82Sec5Inputs16 where
  tab := hTab
  tab56 := hTab56
  factB := asc82Sec5FactB5_of hS
  fact512K := asc82Fact512K_of hS
  l58b := hL58b
  l58d := hL58d
  f510 := asc82Fact510_of_inputs hCorIIIq hSym hPoc
  fact512H := asc82Fact512H_of hS
  facts6 := ⟨hPockets6, asc82FactQCent6_of_finite hQCent, hFrame6, hOutZeta6⟩
  f513 := hF513
  m1 := asc82FactRhoStar_of hS
  f7 := asc82Fact512M8_holds
  qcentExp := hQCentExp
  qbCent := hQBCent
  cent6 := asc82FactOm6CentD_of hS
  nrank6 := asc82FactOm6NRank_of hS
  par5 := asc82FactOm6Par_of hS
  corIIIq := hCorIIIq

theorem ys09asm_omega5Open (F : Sec8T84Base) (hS : Asc82SchurU43)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hCorIII : Asc82CorIII)
    (hKBigSD : Asc82Step1111KBigSD) (hZ2A5 : Asc82Z2A5K) (h3 : Asc82Sec3Results)
    (h6m : AschOmega6Minus) (h7 : AschOmega7) (h8p : AschOmega8Plus) (h8m : AschOmega8Minus)
    (h6z : AschOmega6MinusZ2) (hFacts : Asc82Facts10) (hSplit : Asc82FactSplit5)
    (hDich : Asc82S8Dich) : Asc82Omega5Open' :=
  have s3 : Asc82Sec3Res10 := ⟨h3.l33, h3.l36, h3.l37⟩
  have hp : Asc82Pre11 := asc82Pre11_of_inputs10
    { h6p := F.h6p, h6m := h6m, h7 := h7, h8p := h8p, h8m := h8m, h6z := h6z, s3 := s3,
      facts := hFacts, corIII := hCorIII, schur := ff_schurOmega5 hGA }
  have h65 : Asc82Lemma65 := asc82Lemma65_of F.hShapes F.hAutF F.h64
  { h6p := F.h6p, h6m := h6m, h7 := h7, h8p := h8p, h8m := h8m, h6z := h6z, s3 := s3
    corIII := hCorIII, schur := ff_schurOmega5 hGA, kBigSD := hKBigSD
    s8Dich := hDich, l63 := F.h63, l65 := h65
    z4out := asc82StepZ4Out_of_noOuterInv hp hSplit
        (asc82StepZ4NoOuterInv_of hp (asc82StepZ4Cent_of hp)
            (asc82StepZ4Comp_of hp F.h63 F.hH62 h65 F.h6p h6m h7 h8p h8m h6z))
    z2a5 := hZ2A5, zExists := asc82ZExists_of F.h36 hS }

end CFSG.OddStandard.SmallF3

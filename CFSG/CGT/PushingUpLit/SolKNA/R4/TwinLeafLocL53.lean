module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocLin
public import Certificates.Certificate320321

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

theorem pairWit_l53 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (h : locCheck 5 inF5 l53Data = true) :
    ∀ x t : MulAut (projectiveSL 5 K), orderOf x = 8 → orderOf t = 2 → x * t = t * x →
      PairWit (MulAut.conj : projectiveSL 5 K →* MulAut (projectiveSL 5 K)).range x t :=
  pairWit_of_locCheck (by norm_num) hK (fun g hv he hin => inF5_spec hK hv he hin) h
    (m := 464420385) (by norm_num) (card_GL5 hK)

theorem localL53_holds : LocalL53 := by
  refine localNoQ16Q16_of_pairWit ?_
  intro F _ hF
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hF
  exact pairWit_of_equiv e (pairWit_l53 (by simpa using hK) Certificates.certificate320321)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

module

public import Certificates.Data.Kernel.U62.Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Facts
public import CFSG.Certificates.Kernel.U6Sound
import CFSG.Certificates.Kernel.U62PairWit

public section

namespace CFSG.KC.U62P

open Subgroup CFSG.KC.U6 CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoHypIICover.U62
open CFSG.Fischer (T46)

theorem kFacts_of_K
    {TV UP GV RV LV PT LB SO NI XP NXP PO NO NP : Nat} {T : ETab}
    (hTV : decA TV 12 46 = CFSG.F4.Native.tvGens) (hUP : decA UP 12 693 = CFSG.F4.Native.uPts)
    (hcard : Nat.card u62Sb = 32768)
    (hgen : ∀ k < 13, genAt TV GV (u62SbWords.map (List.map fun z => z.natAbs - 1)) k = true)
    (hrep : ∀ j < 43, repAt GV RV (u62RWords.map (List.map fun z => z.natAbs - 1)) j = true)
    (htree : ∀ i < 32768, treeAt GV LV PT LB i = true)
    (hsort : ∀ i < 32768, sortAt LV SO 32768 i = true)
    (hphi : ∀ i < 32768, phiAt LV UP XP NXP i = true)
    (hnorm : ∀ k < 13, normAt GV LV NI 32768 k = true)
    (hfix : ∀ q < 693, fixAt GV UP q = true)
    (hscan : ∀ i < 32768, scanAt LV PO T.EI NO i = true)
    (hLV : T.LV = LV) (hRV : T.RV = RV)
    (hpool : ∀ p < NP, poolAt T.W.PV p = true)
    (hrec : ∀ g < T.W.NG, recAt T.W.PV NP T.W.G1 T.W.G2 T.W.GG g = true)
    (hent : ∀ q < NO, entAt T q = true) :
    (∀ q : Fin 693, (∀ g ∈ u62SbG, g q = q) ↔ q = 0) ∧ u62Phi ∉ u62Sb ∧
      (∀ g ∈ u62SbG, u62Phi * g * u62Phi⁻¹ ∈ u62Sb) ∧
      ∀ j < 43, ∀ s ∈ u62Sb, (s * u62Phi) ^ 2 = 1 → s * u62Phi * u62R j = u62R j * (s * u62Phi) →
        MonoW T46 false (closure {u62R j, s * u62Phi}) := by
  obtain ⟨gen, hg⟩ := Snd.genRep hTV hgen
  have hl := Snd.lstRep hg htree
  have henum := Snd.sbEnum hcard hl hsort
  have hΦ := Snd.phi_not_mem hUP henum hphi
  exact ⟨Snd.fixed_point_iff hUP hg hfix, hΦ, Snd.norm_mem hg hl hnorm,
    Snd.monoW_of_checks (Snd.repRep hg hrep) henum hΦ hscan hLV hRV hpool hrec hent⟩

end CFSG.KC.U62P

end

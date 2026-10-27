module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5UniCover
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.CentralExt

theorem i5SUClosed_of_certificates :
    I5SUClosed := by
  intro K _ _ p f N hdat hN hq8 E _ _ π hπ hc
  haveI : Fact p.Prime := ⟨hdat.prime⟩
  haveI : CharP K p := hdat.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [hdat.card, ← pow_mul, Nat.mul_comm]
  by_cases he : Even N
  · obtain ⟨r, hr⟩ := he
    exact SUClosed.statedSU_exists_section_of_central hK ⟨r, hr⟩ (by omega) (by omega) hπ hc
  · exact SUOdd.statedSU_odd_exists_section_of_central hK hdat.one_le hN he
      (fun h => by have := (Prod.mk.inj h).2; omega) hπ hc

theorem kd264I5Universal_of_certificates
    (hE : KD264I5UniversalExc) : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD264I5Universal :=
  kd264I5Universal_of_inputs i5SUClosed_of_certificates hE

end CFSG.LieType.SemisimpleCentralizers.HeldLang

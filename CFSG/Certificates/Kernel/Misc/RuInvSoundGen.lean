module

public import Certificates.Data.Kernel.Misc.RuInv
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Inputs
import CFSG.Certificates.Kernel.Common.Generalize
import CFSG.Certificates.Kernel.Misc.RuInvFinal
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KC.Misc.RuInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.RuStd

#kc_generalize RuInvGen (t : String) using [CFSG.Sporadic.RuSchreier.ru4060Text ↦ t] :
  ∀ {A0 A1 AI0 AI1 C0 C1 CI0 CI1 kS BP nx P : Nat} {E PS PSI LR TR TRI Hs V : Nat → Nat},
    ruArr4060 0 = unpack 4060 12 A0 → ruArr4060 1 = unpack 4060 12 A1 →
    permOK 4060 12 (mask 12) (4060 * 12) A0 AI0 = true →
    permOK 4060 12 (mask 12) (4060 * 12) A1 AI1 = true →
    slotK cprogK A0 A1 = (C0, C1) →
    permOK 4060 12 (mask 12) (4060 * 12) C0 CI0 = true →
    permOK 4060 12 (mask 12) (4060 * 12) C1 CI1 = true →
    Nat.beq (E 0) (powP C0 10) = true →
    Nat.beq (E 1) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord1) = true →
    Nat.beq (E 31) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord2) = true →
    Nat.beq (E 271) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord3) = true →
    Nat.beq (E 751) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord4) = true →
    (∀ j < 1391, conjE E (gen2 C0 C1) (gen2 CI0 CI1) nx j = true) →
    (reachK nx 0 1 = true ∧ reachK nx 1 30 = true ∧ reachK nx 31 240 = true ∧
      reachK nx 271 480 = true ∧ reachK nx 751 640 = true) →
    (∀ j < 1391, hashE E Hs j = true) → keysK Hs P 1391 = true →
    Binds 4060 12 PS kS 2 BP (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) →
    allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true →
    LevelsOK 4060 12 PS PSI LR TR TRI kS 2 BP →
    (rcnt (LR 0) = 2048 ∧ rcnt (LR 1) = 8) →
    (∀ a < 2048, covA LR TR E V a = true) →
    ruInvCheck = true

theorem ruInvK_sound_gen (t : String) : RuInvGen t := by
  intro A0 A1 AI0 AI1 C0 C1 CI0 CI1 kS BP nx P E PS PSI LR TR TRI Hs V hA0 hA1 hpA0 hpA1 hslot hi0
    hi1 hz hw1 hw2 hw3 hw4 hconj hreach hhash hkeys hb hp hl hc hcov
  exact CFSG.KC.Misc.RuInv.P.checkW_ok hA0 hA1 hpA0 hpA1 hslot hi0 hi1 hz hw1 hw2 hw3 hw4 hconj hreach hhash hkeys hb hp
    hl hc hcov

end CFSG.KC.Misc.RuInv

end

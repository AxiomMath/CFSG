module

public import Certificates.Data.Kernel.Misc.RuInv
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Inputs
import CFSG.Certificates.Kernel.Misc.RuInvSoundGen
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.Misc.RuInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.RuStd

theorem ruInvK_sound {A0 A1 AI0 AI1 C0 C1 CI0 CI1 kS BP nx P : Nat}
    {E PS PSI LR TR TRI Hs V : Nat → Nat}
    (hA0 : ruArr4060 0 = unpack 4060 12 A0) (hA1 : ruArr4060 1 = unpack 4060 12 A1)
    (hpA0 : permOK 4060 12 (mask 12) (4060 * 12) A0 AI0 = true)
    (hpA1 : permOK 4060 12 (mask 12) (4060 * 12) A1 AI1 = true)
    (hslot : slotK cprogK A0 A1 = (C0, C1))
    (hi0 : permOK 4060 12 (mask 12) (4060 * 12) C0 CI0 = true)
    (hi1 : permOK 4060 12 (mask 12) (4060 * 12) C1 CI1 = true)
    (hz : Nat.beq (E 0) (powP C0 10) = true)
    (hw1 : Nat.beq (E 1) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord1) = true)
    (hw2 : Nat.beq (E 31) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord2) = true)
    (hw3 : Nat.beq (E 271) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord3) = true)
    (hw4 : Nat.beq (E 751) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord4) = true)
    (hconj : ∀ j < 1391, conjE E (gen2 C0 C1) (gen2 CI0 CI1) nx j = true)
    (hreach : reachK nx 0 1 = true ∧ reachK nx 1 30 = true ∧ reachK nx 31 240 = true ∧
      reachK nx 271 480 = true ∧ reachK nx 751 640 = true)
    (hhash : ∀ j < 1391, hashE E Hs j = true) (hkeys : keysK Hs P 1391 = true)
    (hb : Binds 4060 12 PS kS 2 BP (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase))
    (hp : allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true)
    (hl : LevelsOK 4060 12 PS PSI LR TR TRI kS 2 BP)
    (hc : rcnt (LR 0) = 2048 ∧ rcnt (LR 1) = 8)
    (hcov : ∀ a < 2048, covA LR TR E V a = true) :
    ruInvCheck = true :=
  RuInvGen.inst (ruInvK_sound_gen ru4060Text) hA0 hA1 hpA0 hpA1 hslot hi0 hi1 hz hw1 hw2 hw3 hw4 hconj
    hreach hhash hkeys hb hp hl hc hcov

theorem forall_of_blocks {f : Nat → Bool} {K Q : Nat}
    (h : ∀ q < Q, allN K (fun d => f (Nat.add (Nat.mul K q) d)) = true) :
    ∀ j < K * Q, f j = true := by
  intro j hj
  have hK : 0 < K := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
  have hq : j / K < Q := (Nat.div_lt_iff_lt_mul hK).2 (by rwa [Nat.mul_comm] at hj)
  have hd : j % K < K := Nat.mod_lt j hK
  have := CFSG.KS.allN_spec (h (j / K) hq) (j % K) hd
  rwa [show Nat.add (Nat.mul K (j / K)) (j % K) = j from Nat.div_add_mod j K] at this

end CFSG.KC.Misc.RuInv

end

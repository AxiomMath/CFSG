module

public import CFSG.Certificates.Kernel.O8T0Defs
import CFSG.Certificates.Kernel.O8T0Proved
public import Certificates.Data.Kernel.O8.T0

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain CFSG.KLie.CT

theorem words_sound {G : ℕ → Array ℕ} {S : Array (Array ℕ)} {W : Array (List ℕ)} {GP L : Nat}
    {ws : List (List ℕ)} (hL : S0Bind S L) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hw : W.toList = ws) (h : wordsOK GP L ws = true) : wordsCheckG G S W = true :=
  words_sound_proved hL hG hw h

theorem uIdx_sound {S : Array (Array ℕ)} {U : ℕ → Array ℕ} {L UP : Nat} (hL : S0Bind S L)
    (hU : ∀ k < 6, U k = decR (mat UP k))
    (h : andB (Nat.beq (mat L 4) (mat UP 3)) (andB (Nat.beq (mat L 5) (mat UP 4))
      (Nat.beq (mat L 6) (mat UP 5))) = true) : uIdxCheckG S U = true :=
  uIdx_sound_proved hL hU h

theorem e0_sound {S : Array (Array ℕ)} {L : Nat} (hL : S0Bind S L) (h : e0OK L = true) :
    e0CheckG S = true :=
  e0_sound_proved hL h

theorem t0_sound {S : Array (Array ℕ)} {G C : ℕ → Array ℕ} {W : Array (List ℕ)}
    {GP CP L MT YW : Nat} {ws : List (List ℕ)} (hL : S0Bind S L)
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hC : ∀ s < 6, C s = decR (mat CP s))
    (hw : W.toList = ws) (hl : wordsOK GP L ws = true)
    (hd : distinctOK L = true) (hm : mtOK L MT = true) (h : t0OK (ltK GP CP ws) MT YW = true) :
    t0CheckG S (liftTabG G C W) = true :=
  t0_sound_proved hL hG hC hw hl hd hm h

theorem comm_sound {S : Array (Array ℕ)} {G C : ℕ → Array ℕ} {W : Array (List ℕ)}
    {GP CP L MT : Nat} {ws : List (List ℕ)} (hL : S0Bind S L)
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hC : ∀ s < 6, C s = decR (mat CP s))
    (hw : W.toList = ws) (hl : wordsOK GP L ws = true)
    (hd : distinctOK L = true) (hm : mtOK L MT = true) (h : commOK (ltK GP CP ws) MT = true) :
    commCheckG S (liftTabG G C W) = true :=
  comm_sound_proved hL hG hC hw hl hd hm h

end CFSG.KC.O8

end

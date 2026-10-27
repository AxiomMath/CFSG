module

public import CFSG.Certificates.Kernel.O8DickProved

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem oCount_eq {q : ℕ → Bool} {Q : Nat} {L : List ℕ} (hq : QBind q Q)
    (h : ∀ c < 64, walkFrom Q (fun _ => 1) c = L.getD c 0) (hl : L.length ≤ 64) :
    (oColsG q).length = L.sum :=
  OrthPf.oCount_eq_proved hq h hl

theorem inv_sound {q : ℕ → Bool} {Q : Nat} (hq : QBind q Q)
    (h : ∀ c < 64, walkFrom Q invBadK c = 0) : invCheckG q = true :=
  OrthPf.inv_sound_proved hq h

theorem gen_sound {q : ℕ → Bool} {G GI : ℕ → Array ℕ} {Q GP GIP : Nat} (hq : QBind q Q)
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hGI : ∀ s < 6, GI s = decR (mat GIP s))
    (h : genOK Q GP GIP = true) : genCheckG q G GI = true :=
  OrthPf.gen_sound_proved hq hG hGI h

theorem orbit_sound {q : ℕ → Bool} {G : ℕ → Array ℕ} {OW : Array (List ℕ)} {Q GP n : Nat}
    {OWl : List (List ℕ)} (hq : QBind q Q) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hOW : OW = OWl.toArray) (hl : ∀ w ∈ OWl, ∀ s ∈ w, s < 6) (h : orbitOK Q GP n OWl = true) :
    orbitCheckG q G OW n = true :=
  OrthPf.orbit_sound_proved hq hG hOW hl h

theorem dick_sound {q : ℕ → Bool} {G GI : ℕ → Array ℕ} {Q GP GIP : Nat} (hq : QBind q Q)
    (hf : formOK Q = true) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hGI : ∀ s < 6, GI s = decR (mat GIP s)) (hgen : genCheckG q G GI = true)
    (h : genDickOK GP GIP = true) : dickCheckG q G GI = true :=
  DickPf.dick_sound_proved hq hf hG hGI hgen h

theorem cone_sound {q : ℕ → Bool} {X Xi Y Yi : Array ℕ × ℕ} {C : List ℕ}
    {Q XP XiP YP YiP CC : Nat} (hq : QBind q Q)
    (hX : X = (decR (Nat.land XP (maskN 36)), Nat.shiftRight XP 36))
    (hXi : Xi = (decR (Nat.land XiP (maskN 36)), Nat.shiftRight XiP 36))
    (hY : Y = (decR (Nat.land YP (maskN 36)), Nat.shiftRight YP 36))
    (hYi : Yi = (decR (Nat.land YiP (maskN 36)), Nat.shiftRight YiP 36))
    (hw : ∀ D ∈ [XP, XiP, YP, YiP], Nat.shiftRight D 36 < 64)
    (hC : C = (List.range 6).map fun j => colAt CC j)
    (h : coneOK Q XP XiP YP YiP CC = true) : coneCheckG q X Xi Y Yi C = true :=
  OrthPf.cone_sound_proved hq hX hXi hY hYi hw hC h

end CFSG.KC.O8

end

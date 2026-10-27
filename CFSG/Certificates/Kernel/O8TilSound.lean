module

public import CFSG.Certificates.Kernel.O8TilDefs
import CFSG.Certificates.Kernel.O8TilProved

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem til_sound {q : ℕ → Bool} {n0 : ℕ} {G C U : ℕ → Array ℕ} {X : Array ℕ}
    {RW UW : List (List ℕ)} {T : Array (Array ℕ)} {z : ℕ} {Q GP CP UP XP TL MT XI UI : Nat}
    (hq : QBind q Q) (hn : n0 < 64) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hC : ∀ s < 6, C s = decR (mat CP s)) (hU : ∀ k < 6, U k = decR (mat UP k)) (hX : dec4 X = dec4M XP) (hT : TilBind T TL)
    (hx : xOK Q n0 GP CP XP RW = true) (ht : tabOK GP CP UP XP UW TL MT XI UI = true)
    (hc : ∀ c < 16, closeOK TL MT c = true) (hi : ∀ c < 16, invOK TL MT z c = true) :
    tilCheckG q n0 G C U X RW UW T z = true :=
  til_sound_proved hq hn hG hC hU hX hT hx ht hc hi

theorem z_sound {G C : ℕ → Array ℕ} {X : Array ℕ} {UW : List (List ℕ)} {T : Array (Array ℕ)}
    {tr : Array (ℕ × ℕ)} {z r : ℕ} {ann : List (Array ℕ)} {wit : List (ℕ × ℕ × Bool)}
    {GP CP UP XP TL MT XI UI TR WM : Nat} {ZA SW : List ℕ}
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hC : ∀ s < 6, C s = decR (mat CP s))
    (hX : dec4 X = dec4M XP) (hT : TilBind T TL)
    (htr : ∀ i < 128, tr.getD i (0, 0) = (fget TR i 10 % 128, fget TR i 10 / 128))
    (ha : ann = ZA.map dig4)
    (hw : wit = SW.map fun x => (x % 4096, x / 4096 % 4096, x / 16777216 == 1))
    (ht : tabOK GP CP UP XP UW TL MT XI UI = true) (hc : ∀ c < 16, closeOK TL MT c = true)
    (h : zOK GP CP XP UW TL MT TR z r ZA SW WM = true)
    (hf : ∀ c < 16, zFinOK TL z ZA WM c = true) :
    zCheckG G C X UW T tr z r ann wit = true :=
  z_sound_proved hG hC hX hT htr ha hw ht hc h hf

end CFSG.KC.O8

end

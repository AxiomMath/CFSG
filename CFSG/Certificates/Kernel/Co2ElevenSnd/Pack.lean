module

public import Certificates.Data.Kernel.Co2Eleven
public import CFSG.Certificates.Kernel.Spor.PK.BFS
public import CFSG.Certificates.Kernel.Spor.PK.Enc
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.Co2Eleven.Snd

open CFSG.KC.Enum CFSG.KS CFSG.KC.Co2Eleven CFSG.KS.PK

theorem perm12_facts {p q : Nat} (h : perm12 p q = true) :
    p >>> 27600 = 0 ∧ q >>> 27600 = 0 ∧
      ∀ x < 2300, ap12 p x < 2300 ∧ ap12 q (ap12 p x) = x := by
  unfold perm12 at h
  exact CFSG.KS.Raw.Orb.permOK_facts (n := 2300) (w := 12) h

theorem perm12_isPermN {p q : Nat} (h : perm12 p q = true) : IsPermN 2300 (ap12 p) := by
  obtain ⟨-, -, h3⟩ := perm12_facts h
  refine ⟨fun x hx => (h3 x hx).1, fun x hx y hy e => ?_⟩
  have h1 := (h3 x hx).2
  rw [e, (h3 y hy).2] at h1
  exact h1.symm

theorem perm12_inv {p q : Nat} (h : perm12 p q = true) :
    ∀ y < 2300, ap12 q y < 2300 ∧ ap12 p (ap12 q y) = y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (perm12_isPermN h).surj hy
  rw [((perm12_facts h).2.2 x hx).2]
  exact ⟨hx, rfl⟩

theorem ap12_pcomp (p q : Nat) {x : Nat} (hx : x < 2300) :
    ap12 (pcomp 2300 12 (mask 12) p q) x = ap12 p (ap12 q x) :=
  CFSG.KS.PF.pg_pcomp (n := 2300) (w := 12) (by decide) hx

theorem ap12_pidn {x : Nat} (hx : x < 2300) : ap12 (pidn 2300 12) x = x :=
  CFSG.KS.PF.pg_pidn (n := 2300) (w := 12) (by decide) (by decide) hx

theorem ap12_wordK (A Ai B Bi : Nat) (WV WVI : Nat → Nat) (wd : List Int) {x : Nat}
    (hx : x < 2300) :
    ap12 (wordK A Ai B Bi WV WVI wd) x =
      wd.foldr (fun z y => ap12 (letK A Ai B Bi WV WVI z) y) x := by
  induction wd with
  | nil => exact ap12_pidn hx
  | cons z wd ih =>
    show ap12 (pcomp 2300 12 (mask 12) (letK A Ai B Bi WV WVI z)
      (wordK A Ai B Bi WV WVI wd)) x = _
    rw [ap12_pcomp _ _ hx, ih]
    rfl

theorem ap12_ppow (p : Nat) : ∀ (e : Nat) {x : Nat}, x < 2300 →
    ap12 (ppow 2300 12 (mask 12) (pidn 2300 12) p e) x = itr (ap12 p) e x
  | 0, x, hx => ap12_pidn hx
  | e + 1, x, hx => by
    have h : ppow 2300 12 (mask 12) (pidn 2300 12) p (e + 1) =
        pcomp 2300 12 (mask 12) p (ppow 2300 12 (mask 12) (pidn 2300 12) p e) := by
      show strictN (ppow 2300 12 (mask 12) (pidn 2300 12) p e) (fun q => pcomp 2300 12 (mask 12) p q) = _
      rw [CFSG.KS.PF.strictN_eqP]
    rw [h, ap12_pcomp _ _ hx, ap12_ppow p e hx]
    rfl

theorem eq_pidn_of_fix {p : Nat} (hp : p >>> 27600 = 0) (h : ∀ x < 2300, ap12 p x = x) :
    p = pidn 2300 12 :=
  CFSG.KS.PF.eq_of_fields (n := 2300) (w := 12) (by decide) hp
    (CFSG.KS.PF.pidn_shr (by decide) (by decide)) fun i hi => by
      show ap12 p i = ap12 (pidn 2300 12) i
      rw [h i hi, ap12_pidn hi]

end CFSG.KC.Co2Eleven.Snd

end

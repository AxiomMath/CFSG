module

public import Certificates.Data.Kernel.L34Aut
public import CFSG.Certificates.Kernel.L34FixPowSound
public import CFSG.Certificates.Kernel.L34Scan2Sound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34Aut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34W CFSG.KC.L34FixPow CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem andB_false {a b : Bool} (h : CFSG.KLie.CT.andB a b = false) : a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all [CFSG.KLie.CT.andB]

theorem invBy_eq {r x : Nat} (hr : Cn r) (hx : Cn x) :
    (comp 42 (comp 42 (comp 42 (unpack 42 6 r) (unpack 42 6 x)) (unpack 42 6 r)) (unpack 42 6 x) ==
      idTab 42) = invBy r x := by
  have c1 := canonK_pcomp hr hx
  have c2 := canonK_pcomp c1 hr
  have c3 := canonK_pcomp c2 hx
  rw [comp_unpack' hr hx, comp_unpack' c1 hr, comp_unpack' c2 hx, idTab42, beq_unpack c3 cn_pidn,
    Bool.eq_iff_iff]
  unfold invBy
  rw [CFSG.KS.Raw.Orb.allN_iff]
  have hpt : ∀ p < 42, pg 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6)
      (pcomp 42 6 (mask 6) r x) r) x) p =
      pg 6 (mask 6) r (pg 6 (mask 6) x (pg 6 (mask 6) r (pg 6 (mask 6) x p))) := by
    intro p hp
    rw [pg_pcomp' c2 hp, pg_pcomp' c1 (canon_lt hx hp), pg_pcomp' hr (canon_lt hr (canon_lt hx hp))]
  constructor
  · intro h p hp
    rw [← hpt p hp, Nat.eq_of_beq_eq_true h, pg_pidn' szOK42 hp]
    exact Nat.beq_refl p
  · intro h
    have e : pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) r x) r) x = pidn 42 6 :=
      eq_of_pg c3 cn_pidn fun p hp => by
        rw [hpt p hp, pg_pidn' szOK42 hp]
        exact Nat.eq_of_beq_eq_true (h p hp)
    rw [e]
    exact Nat.beq_refl _

theorem cjP_cn {d di y : Nat} (hd : Cn d) (hdi : Cn di) (hy : Cn y) : Cn (cjP d di y) :=
  canonK_pcomp hy (canonK_pcomp (canonK_pcomp hd hy) hdi)

theorem cjP_eq {d di y : Nat} (hd : Cn d) (hdi : Cn di) (hy : Cn y) :
    comp 42 (unpack 42 6 y) (conjTab 42 (unpack 42 6 d) (unpack 42 6 di) (unpack 42 6 y)) =
      unpack 42 6 (cjP d di y) := by
  unfold conjTab cjP
  rw [comp_unpack' hd hy, comp_unpack' (canonK_pcomp hd hy) hdi,
    comp_unpack' hy (canonK_pcomp (canonK_pcomp hd hy) hdi)]

theorem witK_sound {p m y : Nat} {C CI : Nat → Nat} {D Di : Array Tab} (hy : Cn y)
    (hDs : D.size = m) (hD : ∀ a < m, D[a]! = unpack 42 6 (C a))
    (hDi : ∀ a < m, Di[a]! = unpack 42 6 (CI a)) (hC : ∀ a < m, Cn (C a) ∧ Cn (CI a))
    (h : witK p m C CI y = true) : witness 42 p D Di (unpack 42 6 y) = true := by
  unfold witK at h
  unfold witness
  rw [hDs, Bool.or_eq_true, anyBelow_iff, anyBelow_iff]
  rcases orB_iff.1 h with h | h
  · obtain ⟨a, ha, hf⟩ := CFSG.KC.L34Scan2.ex_of_notB_allN h
    refine Or.inl ⟨a, ha, ?_⟩
    rw [hD a ha, hDi a ha, cjP_eq (hC a ha).1 (hC a ha).2 hy,
      fixPow_eq (cjP_cn (hC a ha).1 (hC a ha).2 hy), hf]
    rfl
  · obtain ⟨a, ha, hf⟩ := CFSG.KC.L34Scan2.ex_of_notB_allN h
    rw [sB] at hf
    obtain ⟨b, hb, hg⟩ := CFSG.KC.L34Scan2.ex_of_notB_allN (notB_iff.2 hf)
    refine Or.inr ⟨a, ha, ?_⟩
    rw [anyBelow_iff]
    refine ⟨b, hb, ?_⟩
    have cu := cjP_cn (hC a ha).1 (hC a ha).2 hy
    have cb := (hC b hb).1
    have cbi := (hC b hb).2
    rw [hD a ha, hDi a ha, cjP_eq (hC a ha).1 (hC a ha).2 hy, hD b hb, hDi b hb]
    unfold conjTab
    rw [comp_unpack' cb hy, comp_unpack' (canonK_pcomp cb hy) cbi,
      comp_unpack' cu (canonK_pcomp (canonK_pcomp cb hy) cbi),
      fixPow_eq (canonK_pcomp cu (canonK_pcomp (canonK_pcomp cb hy) cbi))]
    unfold cjP at hg ⊢
    rw [hg]
    rfl

theorem witPt_sound {e r m x p : Nat} {C CI : Nat → Nat} {ex : Bool} {D Di exc : Array Tab}
    (he : e = pidn 42 6) (hx : Cn x) (hr : Cn r) (hDs : D.size = m)
    (hD : ∀ a < m, D[a]! = unpack 42 6 (C a)) (hDi : ∀ a < m, Di[a]! = unpack 42 6 (CI a))
    (hC : ∀ a < m, Cn (C a) ∧ Cn (CI a)) (hex : ex = true → memTab exc (unpack 42 6 x) = true)
    (h : witPt e r m C CI ex x = true) (hp : p = 3 ∨ p = 5 ∨ p = 7) :
    (!(!(unpack 42 6 x == idTab 42) &&
        comp 42 (comp 42 (comp 42 (unpack 42 6 r) (unpack 42 6 x)) (unpack 42 6 r)) (unpack 42 6 x) ==
          idTab 42 && powTab 42 (unpack 42 6 x) p == idTab 42) ||
      memTab exc (unpack 42 6 x) || witness 42 p D Di (unpack 42 6 x)) = true := by
  subst he
  rw [invBy_eq hr hx, idTab42, beq_unpack hx cn_pidn, ← idTab42, fixPow_eq hx]
  unfold witPt at h
  rcases orB_iff.1 h with h | h
  · rw [notB_iff.1 h]
    simp
  rcases orB_iff.1 h with h | h
  · rw [h]
    simp
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h5, h7⟩ := andB_iff.1 h
  have hw : witP p m C CI ex x = true := by
    rcases hp with rfl | rfl | rfl
    exacts [h3, h5, h7]
  unfold witP at hw
  rcases orB_iff.1 hw with hw | hw
  · rw [notB_iff.1 hw]
    simp
  rcases orB_iff.1 hw with hw | hw
  · rw [hex hw]
    simp
  · rw [witK_sound hx hDs hD hDi hC hw]
    simp

theorem commB {x g : Nat} (hx : Cn x) (hg : Cn g) :
    (comp 42 (unpack 42 6 x) (unpack 42 6 g) == comp 42 (unpack 42 6 g) (unpack 42 6 x)) =
      commPt 42 6 x g := by
  rw [Bool.eq_iff_iff, beq_iff_eq, commPt_iff hx hg]

theorem cenPt_sound {a b l0 l1 l2 l3 l4 l5 x : Nat} {D L : Array Tab} (hx : Cn x) (ha : Cn a)
    (hb : Cn b) (hDa : ∃ i < D.size, D[i]! = unpack 42 6 a)
    (hDb : ∃ i < D.size, D[i]! = unpack 42 6 b)
    (hL : x = l0 ∨ x = l1 ∨ x = l2 ∨ x = l3 ∨ x = l4 ∨ x = l5 → memTab L (unpack 42 6 x) = true)
    (h : cenPt a b l0 l1 l2 l3 l4 l5 x = true) :
    (!(allBelow D.size fun i => comp 42 D[i]! (unpack 42 6 x) == comp 42 (unpack 42 6 x) D[i]!) ||
      memTab L (unpack 42 6 x)) = true := by
  unfold cenPt at h
  rcases orB_iff.1 h with h | h
  · have hf : ∀ c, Cn c → (∃ i < D.size, D[i]! = unpack 42 6 c) → commPt 42 6 x c = false →
        allBelow D.size (fun i => comp 42 D[i]! (unpack 42 6 x) == comp 42 (unpack 42 6 x) D[i]!) =
          false := by
      intro c hc ⟨i, hi, e⟩ hcf
      rw [← Bool.not_eq_true, CFSG.KS.BfsReplay.allBelow_iff]
      intro hall
      have h1 := hall i hi
      rw [e, beq_iff_eq] at h1
      rw [(commPt_iff hx hc).2 h1.symm] at hcf
      exact Bool.noConfusion hcf
    rcases andB_false (notB_iff.1 h) with h | h
    · rw [hf a ha hDa h]
      rfl
    · rw [hf b hb hDb h]
      rfl
  · rw [hL ?_, Bool.or_true]
    rcases orB_iff.1 h with h | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    rcases orB_iff.1 h with h | h
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h))
    rcases orB_iff.1 h with h | h
    · exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h)))
    rcases orB_iff.1 h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h))))
    rcases orB_iff.1 h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true h)))))

theorem expPt_sound {x : Nat} (hx : Cn x) (h : expPt x = true) :
    (!(powTab 42 (unpack 42 6 x) 27 == idTab 42) || powTab 42 (unpack 42 6 x) 3 == idTab 42) =
      true := by
  rw [fixPow_eq hx, fixPow_eq hx]
  unfold expPt at h
  rcases orB_iff.1 h with h | h
  · rw [h]
    simp
  · rw [notB_iff.1 h]
    rfl

end CFSG.KC.L34Aut

end

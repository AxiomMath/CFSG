module

public import Certificates.Data.Kernel.D4FieldK
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.D4Field

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

theorem beq_t {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem blt_t {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rw [Nat.blt_eq] at h
  exact h

theorem beq_f {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, beq_t]

theorem eqPt_iff {f g : Nat → Nat} : eqPt f g = true ↔ ∀ x < 2457, f x = g x := by
  unfold eqPt
  rw [Orb.allN_iff]
  exact ⟨fun h x hx => beq_t.1 (h x hx), fun h x hx => beq_t.2 (h x hx)⟩

theorem not_eqPt {f g : Nat → Nat} (h : (!eqPt f g) = true) : ∃ x < 2457, f x ≠ g x := by
  rw [Bool.not_eq_true', ← Bool.not_eq_true, eqPt_iff] at h
  refine Classical.byContradiction fun hc => h fun x hx => Classical.byContradiction fun hne =>
    hc ⟨x, hx, hne⟩

theorem any_beq_iff {l : List Nat} {x : Nat} : l.any (Nat.beq x) = true ↔ x ∈ l := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨y, hy, e⟩ => beq_t.1 e ▸ hy, fun h => ⟨x, h, Nat.beq_refl x⟩⟩

theorem noFix_iff {P : Nat} : allN (nat_lit 2457) (fun x => !Nat.beq (ap P x) x) = true ↔
    ∀ x < 2457, ap P x ≠ x := by
  rw [Orb.allN_iff]
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have := h x hx
    rw [Bool.not_eq_true', beq_f] at this
    exact this
  · rw [Bool.not_eq_true', beq_f]
    exact h x hx

theorem fOK_sound {sift : Nat → Bool} {T QG : Nat → Nat} {F G0 PHI : Nat} {NJ : List Nat}
    (h : fOK sift T QG F G0 PHI NJ = true) :
    permB 2457 12 F = true ∧ (∀ x < 2457, ap F (ap F (ap F x)) = x) ∧
      permB 2457 12 G0 = true ∧ (∀ x < 2457, ap G0 x = ap F (ap PHI (ap PHI x))) ∧
      sift G0 = true ∧ (∀ x < 2457, ap (T 0) x = x) ∧
      ∀ k < 4, NJ.getD k 0 < 81 ∧
        ∀ x < 2457, ap F (ap (QG k) x) = ap (T (NJ.getD k 0)) (ap F x) := by
  unfold fOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, eqPt_iff.1 h2, h3, eqPt_iff.1 h4, h5, eqPt_iff.1 h6, fun k hk => ?_⟩
  have := h7 k hk
  exact ⟨blt_t this.1, eqPt_iff.1 this.2⟩

theorem zOK_zero {T : Nat → Nat} {F : Nat} {CD : List (List Nat)} {CR : List (Nat × Nat)}
    {i c : Nat} {L C : List Nat} {P : List (Nat × Nat)} (h : zOK T F CD CR i c 0 L C P = true) :
    ∃ x < 2457, zAt T F i c (zAt T F i c (zAt T F i c x)) ≠ x := by
  unfold zOK at h
  rw [Nat.beq_refl, cond_true] at h
  exact not_eqPt h

theorem zOK_sound {T : Nat → Nat} {F : Nat} {CD : List (List Nat)} {CR : List (Nat × Nat)}
    {i c o : Nat} {L C : List Nat} {P : List (Nat × Nat)} (ho : o ≠ 0)
    (h : zOK T F CD CR i c o L C P = true) :
    (∀ j < 81, j ≠ 0 → j ∉ L →
      (∃ x < 2457, ap (T j) (zAt T F i c x) ≠ zAt T F i c (ap (T j) x)) ∨
        ∃ x < 2457, ap (T j) (ap (T j) (ap (T j) x)) ≠ x) ∧
    L.length = C.length ∧
    (∀ wc ∈ L.zip C, (wc.2 = 99 ∧ ∀ x < 2457, ap (T wc.1) x ≠ x) ∨
      (wc.2 < P.length ∧ ∀ x ∈ L, x ∈ CD.getD (P.getD wc.2 (0, 0)).1 [] ∨
        ∃ y < 2457, ap (T x) (ap (T wc.1) y) ≠ ap (T wc.1) (ap (T x) y))) ∧
    ∀ ma ∈ P, ma.1 < 10 ∧ ma.2 ∈ CD.getD ma.1 [] ∧
      ∀ x < 2457, zAt T F i c x = ap (T ma.2) (zAt T F (rep (CR.getD ma.1 (0, 0)) c) c x) := by
  unfold zOK at h
  rw [beq_f.2 ho, cond_false] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun j hj hj0 hjL => ?_, beq_t.1 h2, fun wc hwc => ?_, fun ma hma => ?_⟩
  · have := h1 j hj
    rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at this
    rcases this with ((h | h) | h) | h
    · exact absurd (beq_t.1 h) hj0
    · exact absurd (any_beq_iff.1 h) hjL
    · exact Or.inl (not_eqPt h)
    · exact Or.inr (not_eqPt h)
  · have := h3 wc hwc
    by_cases e : wc.2 = 99
    · rw [e, Nat.beq_refl, cond_true, noFix_iff] at this
      exact Or.inl ⟨e, this⟩
    · rw [beq_f.2 e, cond_false, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true] at this
      refine Or.inr ⟨this.1, fun x hx => ?_⟩
      have h' := this.2 x hx
      rw [Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · exact Or.inl (any_beq_iff.1 h')
      · exact Or.inr (not_eqPt h')
  · have := h4 ma hma
    exact ⟨blt_t this.1.1, any_beq_iff.1 this.1.2, eqPt_iff.1 this.2⟩

theorem cOK_sound {T W : Nat → Nat} {F : Nat} {D : List Nat} {r : Nat × Nat} {N : List Nat}
    {WL : List (Nat × (List Nat × Nat))} (h : cOK T W F D r N WL = true) :
    D.length = 9 ∧ D.getD 0 1 = 0 ∧ N.length = 8 ∧
    (∀ x < 2457, zAt T F r.2 2 (zAt T F r.2 2 x) = zAt T F r.1 1 x) ∧
    (∀ q < 8, (N.getD q 0 = 0 ∧ ∀ x < 2457, ap (T (D.getD (q + 1) 0)) x ≠ x) ∨
      ((∃ e ∈ WL, e.1 = N.getD q 0 - 1) ∧
        (∃ x < 2457, ap (W (N.getD q 0 - 1)) (ap (T (D.getD (q + 1) 0)) x) ≠
          ap (T (D.getD (q + 1) 0)) (ap (W (N.getD q 0 - 1)) x)) ∧
        ∃ x < 2457, ap (W (N.getD q 0 - 1)) (ap (T (D.getD (q + 1) 0)) x) ≠
          ap (T (D.getD (q + 1) 0)) (ap (T (D.getD (q + 1) 0)) (ap (W (N.getD q 0 - 1)) x)))) ∧
    ∀ e ∈ WL, e.1 < 4 ∧ e.2.1.length = 8 ∧
      (∀ q < 8, e.2.1.getD q 0 ∈ D ∧ ∀ x < 2457,
        ap (W e.1) (ap (T (D.getD (q + 1) 0)) x) = ap (T (e.2.1.getD q 0)) (ap (W e.1) x)) ∧
      e.2.2 ∈ D ∧ ∀ x < 2457,
        ap (W e.1) (zAt T F r.1 1 x) = ap (T e.2.2) (zAt T F r.1 1 (ap (W e.1) x)) := by
  unfold cOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨beq_t.1 h1, beq_t.1 h2, beq_t.1 h3, eqPt_iff.1 h4, fun q hq => ?_, fun e he => ?_⟩
  · have := h5 q hq
    by_cases e : N.getD q 0 = 0
    · rw [e, Nat.beq_refl, cond_true, noFix_iff] at this
      exact Or.inl ⟨e, this⟩
    · rw [beq_f.2 e, cond_false, Bool.and_eq_true, Bool.and_eq_true, List.any_eq_true] at this
      obtain ⟨⟨⟨e1, he1, he1'⟩, ha⟩, hb⟩ := this
      exact Or.inr ⟨⟨e1, he1, beq_t.1 he1'⟩, not_eqPt ha, not_eqPt hb⟩
  · have := h6 e he
    obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, hf⟩ := this
    refine ⟨blt_t ha, beq_t.1 hb, fun q hq => ?_, any_beq_iff.1 hd,
      eqPt_iff.1 hf⟩
    have := hc q hq
    exact ⟨any_beq_iff.1 this.1, eqPt_iff.1 this.2⟩

theorem fieldK_parts {sift : Nat → Bool} {T QG W : Nat → Nat} {F G0 PHI : Nat}
    {NJ ZO : List Nat} {ZL ZC : List (List Nat)} {ZP : List (List (Nat × Nat))}
    {CD : List (List Nat)} {CR : List (Nat × Nat)} {CN : List (List Nat)}
    {CW : List (List (Nat × (List Nat × Nat)))}
    (h : fieldK sift T QG W F G0 PHI NJ ZO ZL ZC ZP CD CR CN CW = true) :
    fOK sift T QG F G0 PHI NJ = true ∧
      (∀ k < 4, permB 2457 12 (W k) = true ∧ sift (W k) = true) ∧
      (∀ p < 162, zOK T F CD CR (p / 2) (p % 2 + 1) (ZO.getD p 0) (ZL.getD p []) (ZC.getD p [])
        (ZP.getD p []) = true) ∧
      ∀ m < 10, cOK T W F (CD.getD m []) (CR.getD m (0, 0)) (CN.getD m []) (CW.getD m []) =
        true := by
  unfold fieldK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end CFSG.KC.D4Field

end

module

public import CFSG.Certificates.Kernel.Co1PSound
public import Certificates.Data.Kernel.Co1PPin

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.TreeK

theorem lt_of_blt' {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rw [Nat.blt_eq] at h
  exact h

theorem beq_self' (a : Nat) : Nat.beq a a = true := by
  rw [Nat.beq_eq]

theorem allN_true {f : Nat → Bool} : ∀ {n : Nat}, allN n f = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have h' : CFSG.KLie.CT.andB (f n) (allN n f) = true := h
    obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact allN_true h2 i hi
    · exact h1

theorem orB_true {a b : Bool} (h : CFSG.KLie.CT.orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem chunks_all {f : Nat → Bool} {N nc : Nat} (hN : N ≤ 64 * nc)
    (h : ∀ c < nc, allN (nat_lit 64) (fun k => (fun i => CFSG.KLie.CT.orB (Nat.ble N i) (f i))
      (Nat.add (Nat.mul (nat_lit 64) c) k)) = true) :
    ∀ i < N, f i = true := by
  intro i hi
  have hc : i / 64 < nc := by omega
  have h1 := allN_true (h _ hc) (i % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := Nat.div_add_mod i 64
  have h2 : CFSG.KLie.CT.orB (Nat.ble N i) (f i) = true := by
    rw [← e]
    exact h1
  rcases orB_true h2 with h3 | h3
  · exact absurd (Nat.le_of_ble_eq_true h3) (by omega)
  · exact h3

theorem recsEqK_sound {R : Nat → Nat} : ∀ (rs : List (Nat × Nat)) (i : Nat), recsEqK R rs i = true →
    ∀ j (hj : j < rs.length), rs[j] = (R (i + j) / 8, R (i + j) % 8)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | r :: rs, i, h, j, hj => by
    have h' : CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq r.1 (Nat.div (R i) 8)) (Nat.beq r.2 (Nat.mod (R i) 8)))
        (recsEqK R rs (i + 1)) = true := h
    obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h'
    obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h1
    rcases j with _ | j
    · rw [List.getElem_cons_zero, Nat.add_zero]
      exact Prod.ext (Nat.eq_of_beq_eq_true h3) (Nat.eq_of_beq_eq_true h4)
    · rw [List.getElem_cons_succ, recsEqK_sound rs (i + 1) h2 j (by simpa using hj),
        Nat.add_assoc, Nat.add_comm 1 j]

theorem pin_walk {act : Nat → Nat → Nat} {ng root : Nat} {rs : List (Nat × Nat)} {T R : Nat → Nat}
    (hw : (treePts act ng root rs).2 = true) (hr : recsEqK R rs 0 = true)
    (hp : ∀ i < rs.length + 1, pinAt act root T R i = true) :
    ∀ i < rs.length + 1, T i = walkAt act ng root rs i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | j
    · have h0 : Nat.beq (T 0) root = true := hp 0 hi
      rw [walkAt_zero hw]
      exact Nat.eq_of_beq_eq_true h0
    · have h1 : Nat.beq (T (j + 1)) (act (Nat.mod (R j) 8) (T (Nat.div (R j) 8))) = true :=
        hp (j + 1) hi
      have hj : j < rs.length := by omega
      obtain ⟨hpj, -, he⟩ := walkAt_succ hw hj
      have hrj := recsEqK_sound rs 0 hr j hj
      rw [Nat.zero_add] at hrj
      rw [hrj] at hpj he
      rw [he, Nat.eq_of_beq_eq_true h1]
      change act (R j % 8) (T (R j / 8)) = act (R j % 8) (walkAt act ng root rs (R j / 8))
      rw [ih (R j / 8) (by simp only at hpj; omega) (by simp only at hpj; omega)]

theorem bsK_succ (SK : Nat → Nat) (x d lo hi : Nat) : bsK SK x (d + 1) lo hi =
    if lo < hi then (if SK ((lo + hi) / 2) < x then bsK SK x d ((lo + hi) / 2 + 1) hi
      else bsK SK x d lo ((lo + hi) / 2)) else lo := by
  change Bool.rec (motive := fun _ => Nat) lo ((fun m => Bool.rec (motive := fun _ => Nat)
    (bsK SK x d lo m) (bsK SK x d (Nat.succ m) hi) (Nat.blt (SK m) x)) (Nat.div (Nat.add lo hi) 2))
    (Nat.blt lo hi) = _
  by_cases h1 : lo < hi
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), (by rw [Nat.blt_eq]; exact h1 : Nat.blt lo hi = true)]
    change Bool.rec (motive := fun _ => Nat) (bsK SK x d lo ((lo + hi) / 2))
      (bsK SK x d ((lo + hi) / 2 + 1) hi) (Nat.blt (SK ((lo + hi) / 2)) x) = _
    by_cases h2 : SK ((lo + hi) / 2) < x
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2),
        (by rw [Nat.blt_eq]; exact h2 : Nat.blt (SK ((lo + hi) / 2)) x = true)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2),
        (by rw [← Bool.not_eq_true, Nat.blt_eq]; exact h2 : Nat.blt (SK ((lo + hi) / 2)) x = false)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), (by rw [← Bool.not_eq_true, Nat.blt_eq]; exact h1 : Nat.blt lo hi = false)]

theorem bsK_spec {SK : Nat → Nat} {x N : Nat} (hmono : ∀ s t, s < t → t < N → SK s < SK t) :
    ∀ (d lo hi : Nat), lo ≤ hi → hi ≤ N → hi - lo < 2 ^ d → (∀ t < lo, SK t < x) →
      (∀ t, hi ≤ t → t < N → x ≤ SK t) →
      bsK SK x d lo hi ≤ N ∧ (∀ t < bsK SK x d lo hi, SK t < x) ∧
        (∀ t, bsK SK x d lo hi ≤ t → t < N → x ≤ SK t)
  | 0, lo, hi, h1, h2, h3, h4, h5 => by
    have e : hi = lo := by simp at h3; omega
    subst e
    exact ⟨h2, h4, h5⟩
  | d + 1, lo, hi, h1, h2, h3, h4, h5 => by
    rw [bsK_succ]
    rw [Nat.pow_succ] at h3
    by_cases hlh : lo < hi
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hlh)]
      have hm1 : lo ≤ (lo + hi) / 2 := by omega
      have hm2 : (lo + hi) / 2 < hi := by omega
      by_cases hx : SK ((lo + hi) / 2) < x
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hx)]
        refine bsK_spec hmono d _ hi (by omega) h2 (by omega) (fun t ht => ?_) h5
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · exact Nat.lt_of_lt_of_le (hmono t _ ht (by omega)) (Nat.le_of_lt hx)
        · exact hx
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
        refine bsK_spec hmono d lo _ hm1 (by omega) (by omega) h4 (fun t ht htN => ?_)
        rcases Nat.lt_or_eq_of_le ht with ht | rfl
        · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_of_not_lt hx) (hmono _ t ht htN))
        · exact Nat.le_of_not_lt hx
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hlh)]
      have e : hi = lo := by omega
      subst e
      exact ⟨h2, h4, h5⟩

theorem lowK_eq (kw X : Nat) : lowK kw X = X % 2 ^ kw := by
  unfold lowK
  rw [shiftLeft_one]
  rfl

theorem lowK_of_eqK {kw X Y : Nat} (hkw : kw ≤ 576) (h : eqK X Y = true) : lowK kw X = lowK kw Y := by
  have e := (eqK_iff X Y).1 h
  rw [shiftLeft_one] at e
  have hd : 2 ^ kw ∣ 2 ^ 576 := Nat.pow_dvd_pow 2 hkw
  rw [lowK_eq, lowK_eq, ← Nat.mod_mod_of_dvd X hd, ← Nat.mod_mod_of_dvd Y hd]
  exact congrArg (· % 2 ^ kw) e

section

variable {N kw d : Nat} {SK IX P : Nat → Nat} (hk : ∀ s < N, keyAt N kw SK IX P s = true)

include hk in
theorem keyAt_parts {s : Nat} (hs : s < N) :
    (s + 1 < N → SK s < SK (s + 1)) ∧ IX s < N ∧ SK s = lowK kw (P (IX s)) := by
  have h := hk s hs
  unfold keyAt at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h2
  refine ⟨fun hs1 => ?_, lt_of_blt' h3, Nat.eq_of_beq_eq_true h4⟩
  rcases orB_true h1 with h5 | h5
  · exact absurd (Nat.le_of_ble_eq_true h5) (by omega)
  · exact lt_of_blt' h5

include hk in
theorem keys_mono : ∀ s t, s < t → t < N → SK s < SK t := by
  intro s t hst htN
  induction t with
  | zero => exact absurd hst (Nat.not_lt_zero s)
  | succ t ih =>
    have hstep := (keyAt_parts hk (s := t) (by omega)).1 htN
    rcases Nat.lt_succ_iff_lt_or_eq.1 hst with h | rfl
    · exact Nat.lt_trans (ih h (by omega)) hstep
    · exact hstep

include hk in
theorem ix_surj {i : Nat} (hi : i < N) : ∃ s < N, IX s = i := by
  have hinj : Set.InjOn IX (Finset.range N : Set Nat) := by
    intro s hs t ht e
    simp only [Finset.coe_range, Set.mem_Iio] at hs ht
    have es : SK s = SK t := by
      rw [(keyAt_parts hk hs).2.2, (keyAt_parts hk ht).2.2, e]
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd es (Nat.ne_of_lt (keys_mono hk s t h ht))
    · exact absurd es.symm (Nat.ne_of_lt (keys_mono hk t s h hs))
  have hsub : (Finset.range N).image IX ⊆ Finset.range N := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (keyAt_parts hk (Finset.mem_range.1 hs)).2.1
  have heq : (Finset.range N).image IX = Finset.range N :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  have hm : i ∈ (Finset.range N).image IX := by rw [heq]; exact Finset.mem_range.2 hi
  obtain ⟨s, hs, e⟩ := Finset.mem_image.1 hm
  exact ⟨s, Finset.mem_range.1 hs, e⟩

include hk in
theorem memPin_iff (hkw : kw ≤ 576) (hd : N < 2 ^ d) (X : Nat) :
    memPin N kw d SK IX P X = true ↔ ∃ i < N, eqK X (P i) = true := by
  unfold memPin
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
    obtain ⟨-, h4⟩ := CFSG.KC.TreeK.andB_true h2
    exact ⟨_, (keyAt_parts hk (lt_of_blt' h1)).2.1, h4⟩
  · rintro ⟨i, hi, he⟩
    obtain ⟨s, hs, rfl⟩ := ix_surj hk hi
    have hks : SK s = lowK kw X := by rw [(keyAt_parts hk hs).2.2, lowK_of_eqK hkw he]
    obtain ⟨-, hlt, hge⟩ := bsK_spec (x := lowK kw X) (keys_mono hk) d 0 N (Nat.zero_le N) le_rfl
      (by omega) (fun t ht => absurd ht (Nat.not_lt_zero t)) (fun t ht htN => absurd htN (by omega))
    have hr : bsK SK (lowK kw X) d 0 N = s := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have h1 := hge _ le_rfl (by omega)
        have h2 := keys_mono hk _ s h hs
        rw [hks] at h2
        exact absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)
      · have h1 := hlt s h
        rw [hks] at h1
        exact absurd h1 (Nat.lt_irrefl _)
    rw [hr]
    change CFSG.KLie.CT.andB (Nat.blt s N) (CFSG.KLie.CT.andB (Nat.beq (SK s) (lowK kw X)) (eqK X (P (IX s)))) = true
    rw [(by rw [Nat.blt_eq]; exact hs : Nat.blt s N = true), hks, beq_self' _, he]
    rfl

end

end CFSG.KC.Co1P

end

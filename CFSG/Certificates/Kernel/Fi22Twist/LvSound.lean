module

public import Certificates.Data.Kernel.Fi22Twist.Lv
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

theorem strictB_eqL (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

@[expose] noncomputable def scanStep (F : Nat → Nat) (p : Nat → Bool) (q : Nat → Nat) (k s : Nat) :
    Nat :=
  nIf(Nat.blt s (nat_lit 4096),
    nIf(p k, nIf(bAnd(Nat.blt (nat_lit 0) s, Nat.beq (F s) (q k)), Nat.sub s (nat_lit 1), nat_lit 4096),
      s),
    s)

theorem scan_inv (F : Nat → Nat) : ∀ (n : Nat) (p : Nat → Bool) (q : Nat → Nat) (nc : Nat),
    (List.range n).foldr (scanStep F p q) nc < 4096 →
      (List.range n).foldr (scanStep F p q) nc ≤ nc ∧
      ∀ k < n, p k = true → ∃ t, (List.range n).foldr (scanStep F p q) nc ≤ t ∧ t < nc ∧
        F (t + 1) = q k
  | 0, _, _, _, _ => ⟨Nat.le_refl _, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | n + 1, p, q, nc, hs => by
    rw [CFSG.KS.Raw.Orb.foldr_range_succ] at hs ⊢
    have e : (fun x y => scanStep F p q (Nat.succ x) y) =
        scanStep F (fun k => p (Nat.succ k)) (fun k => q (Nat.succ k)) := rfl
    rw [e] at hs ⊢
    generalize hs' : (List.range n).foldr
      (scanStep F (fun k => p (Nat.succ k)) (fun k => q (Nat.succ k))) nc = s at hs ⊢
    have ih := scan_inv F n (fun k => p (Nat.succ k)) (fun k => q (Nat.succ k)) nc
    rw [hs'] at ih
    have hlt : s < 4096 := by
      cases hb : Nat.blt s 4096
      · have : scanStep F p q 0 s = s := by
          unfold scanStep
          rw [hb]
        rw [this] at hs
        exact hs
      · exact Nat.le_of_ble_eq_true hb
    obtain ⟨ih1, ih2⟩ := ih hlt
    have hb : Nat.blt s 4096 = true := Nat.ble_eq_true_of_le hlt
    have shift : ∀ k < n + 1, p k = true → 0 < k →
        ∃ t, s ≤ t ∧ t < nc ∧ F (t + 1) = q k := by
      intro k hk hp hk0
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ih2 k' (by omega) hp
    cases hp0 : p 0
    · have : scanStep F p q 0 s = s := by
        unfold scanStep
        rw [hb, hp0]
      rw [this]
      refine ⟨ih1, fun k hk hp => ?_⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [hp0] at hp
        exact absurd hp Bool.false_ne_true
      · exact shift k hk hp hk0
    · cases hc : bAnd(Nat.blt (nat_lit 0) s, Nat.beq (F s) (q 0))
      · have : scanStep F p q 0 s = 4096 := by
          unfold scanStep
          rw [hb, hp0, hc]
        rw [this] at hs
        exact absurd hs (Nat.lt_irrefl _)
      · have : scanStep F p q 0 s = s - 1 := by
          unfold scanStep
          rw [hb, hp0, hc]
          rfl
        rw [this]
        obtain ⟨c1, c2⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
        have hs0 : 0 < s := Nat.le_of_ble_eq_true c1
        refine ⟨by omega, fun k hk hp => ?_⟩
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · refine ⟨s - 1, Nat.le_refl _, by omega, ?_⟩
          rw [Nat.sub_add_cancel hs0]
          exact Nat.eq_of_beq_eq_true c2
        · obtain ⟨t, ht1, ht2, ht3⟩ := shift k hk hp hk0
          exact ⟨t, by omega, ht2, ht3⟩

theorem scan_sound {F : Nat → Nat} {p : Nat → Bool} {q : Nat → Nat} {n nc : Nat}
    (h : (List.range n).foldr (scanStep F p q) nc = 0) :
    ∀ k < n, p k = true → ∃ t < nc, F (t + 1) = q k := by
  have hi := scan_inv F n p q nc (by rw [h]; omega)
  intro k hk hp
  obtain ⟨t, _, ht2, ht3⟩ := hi.2 k hk hp
  exact ⟨t, ht2, ht3⟩

theorem nodeK_sound {T TT OF M D GF LF KF : Nat → Nat} {n : Nat}
    (h : nodeK T TT OF M D GF LF KF n = true) :
    fld(LF n, 48, 255) < 3 ∧ fld(LF n, 56, 255) < 5 ∧
    ∀ k < szL (fld(LF n, 48, 255)),
      passL (fun e => D (Nat.add (Nat.mul 27 (fld(LF n, 56, 255))) e))
        (fun x => nIf(Nat.beq (fld(LF n, 48, 255)) 0, x,
          ap (T (fld(LF n, 0, 65535))) (nIf(Nat.beq (fld(LF n, 48, 255)) 1, x,
            ap (T (fld(LF n, 16, 65535))) x))))
        (OF (fld(LF n, 48, 255)))
        (maskL M (fun e => D (Nat.add (Nat.mul 27 (fld(LF n, 56, 255))) e))
          (Nat.land (Nat.lor ((fun x => nIf(Nat.beq (fld(LF n, 48, 255)) 0, x,
              ap (T (fld(LF n, 0, 65535))) (nIf(Nat.beq (fld(LF n, 48, 255)) 1, x,
                ap (T (fld(LF n, 16, 65535))) x)))) (bp 0))
            (Nat.shiftLeft ((fun x => nIf(Nat.beq (fld(LF n, 48, 255)) 0, x,
              ap (T (fld(LF n, 0, 65535))) (nIf(Nat.beq (fld(LF n, 48, 255)) 1, x,
                ap (T (fld(LF n, 16, 65535))) x)))) (bp 1)) 12))
            (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 (fld(LF n, 48, 255)))) 1))
          (fld(LF n, 48, 255)) (fld(LF n, 48, 255)))
        (fld(GF (fld(LF n, 56, 255)), Nat.mul 1024 (fld(LF n, 48, 255)),
          Nat.sub (Nat.shiftLeft 1 1024) 1))
        (Nat.land (Nat.lor ((fun x => nIf(Nat.beq (fld(LF n, 48, 255)) 0, x,
            ap (T (fld(LF n, 0, 65535))) (nIf(Nat.beq (fld(LF n, 48, 255)) 1, x,
              ap (T (fld(LF n, 16, 65535))) x)))) (bp 0))
          (Nat.shiftLeft ((fun x => nIf(Nat.beq (fld(LF n, 48, 255)) 0, x,
            ap (T (fld(LF n, 0, 65535))) (nIf(Nat.beq (fld(LF n, 48, 255)) 1, x,
              ap (T (fld(LF n, 16, 65535))) x)))) (bp 1)) 12))
          (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 (fld(LF n, 48, 255)))) 1))
        (fld(LF n, 48, 255)) k = true →
      ∃ t < fld(LF n, 80, 255), fld(LF n, Nat.add 96 (Nat.mul 12 t), 4095) = k + 1 ∧
        childL TT LF KF (LF n) (fld(LF n, 48, 255)) (fld(LF n, 56, 255)) t = true := by
  unfold nodeK at h
  simp only [strictB_eqL] at h
  obtain ⟨hd, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hj, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hs, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨Nat.le_of_ble_eq_true hd, Nat.le_of_ble_eq_true hj, fun k hk hp => ?_⟩
  unfold scanL at hs
  rw [CFSG.KS.Raw.Orb.foldN_eq] at hs
  obtain ⟨t, ht, hf⟩ := scan_sound (q := Nat.succ) (Nat.eq_of_beq_eq_true hs) k hk hp
  refine ⟨t, ht, ?_, ?_⟩
  · have e : Nat.add 84 (Nat.mul 12 (t + 1)) = Nat.add 96 (Nat.mul 12 t) := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rw [← e]
    exact hf
  · have e := CFSG.KS.allBlk_spec hc t ht
    have e0 : Nat.add 0 t = t := Nat.zero_add t
    rwa [e0] at e

end CFSG.KC.Fi22Twist

end

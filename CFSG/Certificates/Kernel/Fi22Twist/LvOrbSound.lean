module

public import CFSG.Certificates.Kernel.Fi22Twist.LvSound
public import CFSG.Certificates.Kernel.Fi22Twist.SearchSound
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

theorem fixB_spec {x i : Nat} (h : fixB x i = true) : ∀ m < i, ap x (bp m) = bp m := by
  intro m hm
  have e := CFSG.KS.allBlk_spec h m hm
  have e0 : Nat.add 0 m = m := Nat.zero_add m
  rw [e0] at e
  exact Nat.eq_of_beq_eq_true e

theorem fixB_intro {x i : Nat} (h : ∀ m < i, ap x (bp m) = bp m) : fixB x i = true := by
  unfold fixB
  refine allBlk_intro fun m hm => ?_
  have e0 : Nat.add 0 m = m := Nat.zero_add m
  rw [e0, h m hm]
  exact Nat.beq_refl _

theorem div20 (i g : Nat) (hg : g < 20) : Nat.div (20 * i + g) 20 = i := by
  change (20 * i + g) / 20 = i
  omega

theorem mod20 (i g : Nat) (hg : g < 20) : Nat.mod (20 * i + g) 20 = g := by
  change (20 * i + g) % 20 = g
  omega

theorem lv_base {OF PF S : Nat → Nat} {i : Nat} (h : lvK OF PF S (20 * i + 19) = true) :
    ap (OF i) 0 = bp i ∧ ∀ k < szL i, ap (OF i) k < 3510 ∧ ap (PF i) (ap (OF i) k) = k := by
  unfold lvK at h
  simp only [strictB_eqL] at h
  rw [div20 i 19 (by omega), mod20 i 19 (by omega)] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun k hk => ?_⟩
  have e := CFSG.KS.allN_spec h2 k hk
  obtain ⟨e1, e2⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  exact ⟨Nat.le_of_ble_eq_true e1, Nat.eq_of_beq_eq_true e2⟩

theorem lv_gen {OF PF S : Nat → Nat} {i g : Nat} (hg : g < 19)
    (h : lvK OF PF S (20 * i + g) = true) (hfix : ∀ m < i, ap (S g) (bp m) = bp m) :
    ∀ k < szL i, ∃ q < szL i, ap (OF i) q = ap (S g) (ap (OF i) k) := by
  unfold lvK at h
  simp only [strictB_eqL] at h
  rw [div20 i g (by omega), mod20 i g (by omega)] at h
  have hb : Nat.beq g 19 = false := by
    cases e : Nat.beq g 19
    · rfl
    · have := Nat.eq_of_beq_eq_true e
      omega
  rw [hb] at h
  change Bool.rec (motive := fun _ => Bool) true _ (fixB (S g) i) = true at h
  rw [fixB_intro hfix] at h
  intro k hk
  have e := CFSG.KS.allN_spec h k hk
  obtain ⟨e1, e2⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  exact ⟨_, Nat.le_of_ble_eq_true e1, Nat.eq_of_beq_eq_true e2⟩

theorem tfPt_sound {T TT OF : Nat → Nat} {f : Nat} (h : tfPtK T TT OF f = true) :
    fld(TT f, 0, 255) < 3 ∧ fld(TT f, 8, 65535) < szL (fld(TT f, 0, 255)) ∧
      ap (T f) (bp (fld(TT f, 0, 255))) = ap (OF (fld(TT f, 0, 255))) (fld(TT f, 8, 65535)) ∧
      ∀ m < fld(TT f, 0, 255), ap (T f) (bp m) = bp m := by
  unfold tfPtK at h
  simp only [strictB_eqL] at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3,
    fixB_spec h4⟩

end CFSG.KC.Fi22Twist

end

module

public import CFSG.Certificates.Kernel.LocalQTSecLemmas

public section

namespace CFSG.KC.LocalComp.Ops3Snd

open CFSG.KC.LQT CFSG.KS.Ord
open scoped Matrix

@[expose] noncomputable def mat3 (c : Lay) (A : ℕ) : Matrix (Fin c.d) (Fin c.d) (ZMod 3) :=
  ordMat 3 c.d c.w c.S A

@[expose] noncomputable def vec3 (c : Lay) (v : ℕ) : Fin c.d → ZMod 3 :=
  SecS.toVec 3 c.d c.w v

theorem mat3_mul (c : Lay) (hc : c.ok = true) (hp : c.p = 3) {A B : ℕ}
    (hA : Canon c.p c.d c.w A) (hB : Canon c.p c.d c.w B) :
    Canon c.p c.d c.w (c.mul A B) ∧ mat3 c (c.mul A B) = mat3 c A * mat3 c B := by
  obtain ⟨h1, h2⟩ := SecS.mul_sound c hc hA hB
  unfold mat3
  rw [hp] at h1 h2 ⊢
  exact ⟨h1, h2⟩

theorem mat3_one (c : Lay) (hc : c.ok = true) (hp : c.p = 3) :
    Canon c.p c.d c.w c.ONE ∧ mat3 c c.ONE = 1 := by
  obtain ⟨h1, h2⟩ := CFSG.KS.Ord.one_sound hc
  unfold mat3
  rw [hp] at h1 h2 ⊢
  exact ⟨h1, h2⟩

theorem mat3_decode (c : Lay) (hc : c.ok = true) (hp : c.p = 3) {M : ℕ} {l : List Char}
    (h : decOK c M l = true) :
    Canon c.p c.d c.w M ∧
      mat3 c M = CFSG.Blueprint.NativeSporadic.decode 3 c.d 1 (String.ofList l) := by
  obtain ⟨h1, h2⟩ := SecS.decOK_sound c hc h
  unfold mat3
  rw [hp] at h1 h2 ⊢
  exact ⟨h1, h2⟩

private theorem lane_pow_two (w t j : ℕ) (hw : 0 < w) :
    CFSG.KS.Ord.lane w (2 ^ (w * t)) j = if j = t then 1 else 0 := by
  have hw2 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  unfold CFSG.KS.Ord.lane
  rcases lt_trichotomy j t with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, t = j + k + 1 := ⟨t - j - 1, by omega⟩
    rw [if_neg (show j ≠ j + k + 1 by omega)]
    have e : 2 ^ (w * (j + k + 1)) = 2 ^ (w * j) * (2 ^ (w * k) * 2 ^ w) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    rw [e, Nat.mul_div_cancel_left _ (show 0 < 2 ^ (w * j) by positivity)]
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _)
  · rw [if_pos h, h, Nat.div_self (show 0 < 2 ^ (w * t) by positivity), Nat.mod_eq_of_lt hw2]
  · rw [if_neg (show j ≠ t by omega)]
    have hlt : 2 ^ (w * t) < 2 ^ (w * j) :=
      Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]

theorem vec3_unit (c : Lay) (hc : c.ok = true) (hp : c.p = 3) {t : ℕ} (ht : t < c.d) :
    vec3 c (c.unit t) = fun j : Fin c.d => if (j : ℕ) = t then (1 : ZMod 3) else 0 := by
  have hw := SecS.lay_w_pos c hc
  have hu : c.unit t = 2 ^ (c.w * t) := by
    unfold Lay.unit
    change 1 <<< (c.w * t) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  funext j
  simp only [vec3, SecS.toVec]
  rw [hu, lane_pow_two c.w t (j : ℕ) hw]
  split_ifs <;> simp

theorem vec3_vpow (c : Lay) (hc : c.ok = true) (hp : c.p = 3) {X v : ℕ}
    (hX : Canon c.p c.d c.w X) (hv : SecS.VCanon c.p c.d c.w v) (e : ℕ) :
    SecS.VCanon c.p c.d c.w (c.vpow X v e) ∧ vec3 c (c.vpow X v e) = vec3 c v ᵥ* mat3 c X ^ e := by
  obtain ⟨h1, h2⟩ := SecS.vpow_spec c hc hX e hv
  unfold vec3 mat3
  rw [hp] at h1 h2 ⊢
  exact ⟨h1, h2⟩

theorem vec3_inj (c : Lay) (hc : c.ok = true) {u v : ℕ} (hu : SecS.VCanon c.p c.d c.w u)
    (hv : SecS.VCanon c.p c.d c.w v) (hp : c.p = 3) (h : vec3 c u = vec3 c v) : u = v := by
  have h' : SecS.toVec c.p c.d c.w u = SecS.toVec c.p c.d c.w v := by
    rw [hp]
    exact h
  exact SecS.vec_inj (SecS.lay_w_pos c hc) hu hv h'


end CFSG.KC.LocalComp.Ops3Snd

end

module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.LocalQTSecLemmas
public import CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.LocalQTSecLemmas

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.LQT.SecS CFSG.KC.LL.Ly7 CFSG.KC.LyA.DceS

abbrev Mat7 : Type := Matrix (Fin 7) (Fin 7) (ZMod 5)

abbrev Vec7 : Type := Fin 7 → ZMod 5

@[expose] noncomputable def m7 (X : ℕ) : Mat7 := ordMat 5 7 8 56 X

@[expose] noncomputable def v7 (v : ℕ) : Vec7 := toVec 5 7 8 v

@[expose] def C7 (X : ℕ) : Prop := Canon 5 7 8 X

@[expose] def V7 (v : ℕ) : Prop := VCanon 5 7 8 v

theorem andL_iff {a b : Bool} : CFSG.KC.LyA.DceS.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

variable (hc : constsOK7 = true)
include hc

theorem one7 : C7 ONE7 ∧ m7 ONE7 = 1 := one_sound (p := 5) (w := 8) (S := 56) (d := 7) hc

theorem mul7_sound {A B : ℕ} (hA : C7 A) (hB : C7 B) : C7 (mul7 A B) ∧ m7 (mul7 A B) = m7 A * m7 B :=
  mulR_sound hc hA hB

theorem valid7 {X : ℕ} (h : validM7 X = true) : C7 X := validM_canon (d := 7) (S := 56) hc h

omit hc in

theorem m7_inj {A B : ℕ} (hA : C7 A) (hB : C7 B) (h : m7 A = m7 B) : A = B := by
  rw [pk_lane (by norm_num) hA.1, pk_lane (by norm_num) hB.1]
  refine pk_congr fun t ht => ?_
  have hi : t / 7 < 7 := by omega
  have hj : t % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have h3 := congrFun (congrFun h ⟨t / 7, hi⟩) ⟨t % 7, hj⟩
  simp only [m7, ordMat] at h3
  have e : 56 * (t / 7) + 8 * (t % 7) = 8 * t := by omega
  rw [e] at h3
  rw [ZMod.natCast_eq_natCast_iff'] at h3
  have ha := hA.2 t ht
  have hb := hB.2 t ht
  unfold lane at ha hb ⊢
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h3

omit hc in
theorem zero7 : C7 0 ∧ m7 0 = 0 := by
  refine ⟨⟨by positivity, fun t _ => by simp [lane]⟩, ?_⟩
  funext i j
  simp [m7, ordMat]

theorem vec7_sound {v M : ℕ} (hv : V7 v) (hM : C7 M) :
    V7 (vec7 v M) ∧ v7 (vec7 v M) = Matrix.vecMul (v7 v) (m7 M) :=
  vecR_sound hc hv hM

omit hc in
theorem v7_inj {u v : ℕ} (hu : V7 u) (hv : V7 v) (h : v7 u = v7 v) : u = v :=
  vec_inj (by norm_num) hu hv h

omit hc in
theorem zeroV : V7 0 ∧ v7 0 = 0 := by
  refine ⟨⟨by positivity, fun t _ => by simp [lane]⟩, ?_⟩
  funext j
  simp [v7, toVec, lane]

omit hc in
private theorem validM_lanes {p w n nb X : Nat} (hw : 0 < w) (hp2 : p ≤ 2 ^ (w - 1)) (hnb : nb = w * n)
    (hX : validM p nb (pk w n (fun _ => 1)) (pk w n (fun _ => 2 ^ (w - 1))) X = true) :
    X < 2 ^ (w * n) ∧ ∀ t < n, lane w X t < p := by
  unfold validM at hX
  obtain ⟨h1, hX⟩ := andB_true hX
  obtain ⟨h2, h3⟩ := andB_true hX
  have e2 := two_pow_pred hw
  have hlt : X < 2 ^ (w * n) := by
    have h1' : X >>> nb = 0 := Nat.eq_of_beq_eq_true h1
    rw [Nat.shiftRight_eq_div_pow, hnb] at h1'
    rcases Nat.div_eq_zero_iff.1 h1' with h | h
    · exact absurd h (Nat.two_pow_pos _).ne'
    · exact h
  obtain ⟨a, rfl, ha⟩ : ∃ a, X = pk w n a ∧ ∀ t < n, a t < 2 ^ w :=
    ⟨lane w X, pk_lane hw hlt, fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w)⟩
  have h0 := Nat.two_pow_pos (w - 1)
  have hHb : ∀ t < n, (2 : Nat) ^ (w - 1) < 2 ^ w := fun _ _ => by omega
  have htop : ∀ t < n, a t < 2 ^ (w - 1) := by
    intro t ht
    have h2' : pk w n a &&& pk w n (fun _ => 2 ^ (w - 1)) = 0 := Nat.eq_of_beq_eq_true h2
    have hF := fld_and (fld_pk ha) (fld_pk hHb)
    rw [h2'] at hF
    have hb := hF t (w - 1) (by omega)
    rw [Nat.zero_testBit] at hb
    simp only [ht, ↓reduceIte] at hb
    have ha2 : a t < 2 * 2 ^ (w - 1) := by have := ha t ht; omega
    rw [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, testBit_top ha2] at hb
    simpa using hb
  have h3' : ((pk w n a ||| pk w n (fun _ => 2 ^ (w - 1))) -
      p * pk w n (fun _ => 1)) &&& pk w n (fun _ => 2 ^ (w - 1)) = 0 :=
    Nat.eq_of_beq_eq_true h3
  rw [top_H hw htop hp2] at h3'
  unfold pk at h3'
  refine ⟨pk_lt ha, fun t ht => ?_⟩
  rw [lane_pk ha ht]
  by_contra hn
  have hz := Finset.sum_eq_zero_iff.1 h3' t (Finset.mem_range.2 ht)
  have hn' : p ≤ a t := Nat.le_of_not_lt hn
  simp only [hn', ↓reduceIte] at hz
  exact absurd hz (Nat.mul_ne_zero (Nat.two_pow_pos _).ne' (Nat.two_pow_pos _).ne')

private theorem lv7 : LV7 = pk 8 7 (fun _ => 1) ∧ HV7 = pk 8 7 (fun _ => 2 ^ (8 - 1)) :=
  consts_v hc (by norm_num)

theorem validV {v : ℕ} (h : validM (nat_lit 5) (nat_lit 56) LV7 HV7 v = true) : V7 v := by
  rw [(lv7 hc).1, (lv7 hc).2] at h
  exact validM_lanes (by norm_num) (by norm_num) (by norm_num) h

theorem scal_sound {l v : ℕ} (hv : V7 v) (hl : l < 5) :
    V7 (scal l v) ∧ v7 (scal l v) = (l : ZMod 5) • v7 v := by
  obtain ⟨a, rfl, ha⟩ : ∃ a, v = pk 8 7 a ∧ ∀ t < 7, a t < 5 :=
    ⟨lane 8 v, pk_lane (by norm_num) hv.1, hv.2⟩
  have e1 : Nat.mul l (pk 8 7 a) = pk 8 7 (fun t => a t * l) := by
    change l * pk 8 7 a = _
    rw [Nat.mul_comm, pk_mul]
  have hf : ∀ t < 7, a t * l < 2 ^ (8 - 1) := fun t ht => by
    have := ha t ht
    have : a t * l ≤ 4 * 4 := Nat.mul_le_mul (by omega) (by omega)
    norm_num
    omega
  have hf2 : ∀ t < 7, a t * l < 5 * 2 ^ (4 + 1) := fun t ht => by
    have := ha t ht
    have : a t * l ≤ 4 * 4 := Nat.mul_le_mul (by omega) (by omega)
    norm_num
    omega
  have e2 : scal l (pk 8 7 a) = pk 8 7 (fun t => a t * l % 5) := by
    unfold scal
    rw [e1, (lv7 hc).1, (lv7 hc).2]
    exact redP_pk (by norm_num) (by norm_num) hf hf2
  have hc : ∀ t < 7, a t * l % 5 < 5 := fun t _ => Nat.mod_lt _ (by norm_num)
  rw [e2]
  refine ⟨vcanon_pk hc (by norm_num), ?_⟩
  funext j
  have ha' : ∀ t < 7, a t < 2 ^ 8 := fun t ht => by have := ha t ht; omega
  have hc' : ∀ t < 7, a t * l % 5 < 2 ^ 8 := fun t ht => by have := hc t ht; omega
  simp only [v7, toVec, Pi.smul_apply, smul_eq_mul]
  rw [lane_pk hc' j.isLt, lane_pk ha' j.isLt, ZMod.natCast_mod, Nat.cast_mul, mul_comm]

theorem normV_spec {v : ℕ} (h : normV v = true) :
    V7 v ∧ 0 < v ∧ ∀ l, 2 ≤ l → l < 5 → v < scal l v := by
  unfold normV at h
  obtain ⟨h0, h⟩ := andL_iff.1 h
  obtain ⟨hV, h⟩ := andL_iff.1 h
  obtain ⟨h2, h⟩ := andL_iff.1 h
  obtain ⟨h3, h4⟩ := andL_iff.1 h
  refine ⟨validV hc hV, Nat.blt_eq.mp h0, fun l hl1 hl2 => ?_⟩
  have : l = 2 ∨ l = 3 ∨ l = 4 := by omega
  rcases this with rfl | rfl | rfl
  · exact Nat.blt_eq.mp h2
  · exact Nat.blt_eq.mp h3
  · exact Nat.blt_eq.mp h4

end CFSG.Certificates.DS5

end

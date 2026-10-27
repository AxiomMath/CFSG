module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.CGT.Stroth77.Arch76

abbrev Co : Type := ZMod 2 × ZMod 4 × ZMod 4

structure Config (X : Type*) [Group X] where
  A : Subgroup X
  w : X
  x : X
  y : X
  uv : X
  t : X
  u : X
  ρ : X
  hA : A = Subgroup.closure {w, x, y}
  hAc : IsMulCommutative A
  hAcard : Nat.card A = 32
  hw : w ^ 2 = 1
  hx : x ^ 4 = 1
  hy : y ^ 4 = 1
  huv_w : uv⁻¹ * w * uv = w * (x * y) ^ 2
  huv_x : uv⁻¹ * x * uv = x * y ^ 2
  huv_y : uv⁻¹ * y * uv = y * x ^ 2
  ht_w : t⁻¹ * w * t = w * x ^ 2
  ht_x : t⁻¹ * x * t = x⁻¹
  ht_y : t⁻¹ * y * t = x ^ 2 * y⁻¹
  hu_w : u⁻¹ * w * u = w
  hu_x : u⁻¹ * x * u = y
  hρ_w : ρ⁻¹ * w * ρ = w
  hρ_x : ρ⁻¹ * x * ρ = y
  hρ_y : ρ⁻¹ * y * ρ = x⁻¹ * y⁻¹
  huv2 : uv ^ 2 = 1
  ht2 : t ^ 2 = 1
  hu2 : u ^ 2 = 1
  huvt : uv * t = t * uv
  huvu : uv * u = u * uv
  htu : u⁻¹ * t * u = uv * t
  hρuv : ρ⁻¹ * uv * ρ = t
  hρt : ρ⁻¹ * t * ρ = uv * t
  hρu : u⁻¹ * ρ * u = ρ⁻¹

theorem pow_mod_of_pow_eq_one {X : Type*} [Monoid X] {g : X} {n : ℕ} (h : g ^ n = 1) (m : ℕ) :
    g ^ (m % n) = g ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, h, one_pow, one_mul]

theorem pow_val_add {X : Type*} [Monoid X] {g : X} {n : ℕ} [NeZero n] (h : g ^ n = 1)
    (a b : ZMod n) : g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, pow_mod_of_pow_eq_one h, pow_add]

namespace Config

variable {X : Type*} [Group X] (C : Config X)

theorem w_mem : C.w ∈ C.A := by rw [C.hA]; exact Subgroup.subset_closure (by simp)
theorem x_mem : C.x ∈ C.A := by rw [C.hA]; exact Subgroup.subset_closure (by simp)
theorem y_mem : C.y ∈ C.A := by rw [C.hA]; exact Subgroup.subset_closure (by simp)

theorem comm {a b : X} (ha : a ∈ C.A) (hb : b ∈ C.A) : a * b = b * a := by
  haveI := C.hAc
  exact Subgroup.mul_comm_of_mem_isMulCommutative C.A ha hb

@[expose] def evA (v : Co) : C.A :=
  ⟨C.w, C.w_mem⟩ ^ v.1.val * ⟨C.x, C.x_mem⟩ ^ v.2.1.val * ⟨C.y, C.y_mem⟩ ^ v.2.2.val

@[expose] def ev (v : Co) : X := C.w ^ v.1.val * C.x ^ v.2.1.val * C.y ^ v.2.2.val

theorem coe_evA (v : Co) : (C.evA v : X) = C.ev v := by
  simp [evA, ev]

theorem ev_mem (v : Co) : C.ev v ∈ C.A := by
  rw [← coe_evA]; exact (C.evA v).2

theorem evA_add (v v' : Co) : C.evA (v + v') = C.evA v * C.evA v' := by
  haveI := C.hAc
  have hw : (⟨C.w, C.w_mem⟩ : C.A) ^ 2 = 1 := Subtype.ext (by simpa using C.hw)
  have hx : (⟨C.x, C.x_mem⟩ : C.A) ^ 4 = 1 := Subtype.ext (by simpa using C.hx)
  have hy : (⟨C.y, C.y_mem⟩ : C.A) ^ 4 = 1 := Subtype.ext (by simpa using C.hy)
  simp only [evA, Prod.fst_add, Prod.snd_add, pow_val_add hw, pow_val_add hx, pow_val_add hy]
  ac_rfl

theorem ev_add (v v' : Co) : C.ev (v + v') = C.ev v * C.ev v' := by
  rw [← coe_evA, ← coe_evA, ← coe_evA, evA_add, Subgroup.coe_mul]

@[simp] theorem ev_zero : C.ev 0 = 1 := by simp [ev]

theorem ev_neg (v : Co) : C.ev (-v) = (C.ev v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ev_add, neg_add_cancel, ev_zero]

theorem ev_sub (v v' : Co) : C.ev (v - v') = C.ev v * (C.ev v')⁻¹ := by
  rw [sub_eq_add_neg, ev_add, ev_neg]

theorem ev_nsmul (n : ℕ) (v : Co) : C.ev (n • v) = C.ev v ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ev_add, ih, pow_succ]

theorem ev_w : C.ev (1, 0, 0) = C.w := by simp [ev, show (1 : ZMod 2).val = 1 from rfl]
theorem ev_x : C.ev (0, 1, 0) = C.x := by simp [ev, show (1 : ZMod 4).val = 1 from rfl]
theorem ev_y : C.ev (0, 0, 1) = C.y := by simp [ev, show (1 : ZMod 4).val = 1 from rfl]

theorem exists_ev {a : X} (ha : a ∈ C.A) : ∃ v : Co, C.ev v = a := by
  rw [C.hA] at ha
  induction ha using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    exacts [⟨_, C.ev_w⟩, ⟨_, C.ev_x⟩, ⟨_, C.ev_y⟩]
  | one => exact ⟨0, C.ev_zero⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨v, rfl⟩ := ihg
    obtain ⟨v', rfl⟩ := ihh
    exact ⟨v + v', C.ev_add v v'⟩
  | inv g _ ih =>
    obtain ⟨v, rfl⟩ := ih
    exact ⟨-v, C.ev_neg v⟩

theorem evA_surjective : Function.Surjective C.evA := by
  rintro ⟨a, ha⟩
  obtain ⟨v, hv⟩ := C.exists_ev ha
  exact ⟨v, Subtype.ext (by rw [coe_evA, hv])⟩

theorem evA_bijective : Function.Bijective C.evA :=
  C.evA_surjective.bijective_of_nat_card_le (by
    rw [C.hAcard, Nat.card_eq_fintype_card]
    rfl)

theorem ev_injective : Function.Injective C.ev := by
  intro v v' h
  apply C.evA_bijective.1
  apply Subtype.ext
  rw [coe_evA, coe_evA, h]

theorem ev_eq_one_iff (v : Co) : C.ev v = 1 ↔ v = 0 := by
  rw [← C.ev_zero]
  exact C.ev_injective.eq_iff


end Config

@[expose] def lin (a b c : Co) (v : Co) : Co := v.1.val • a + v.2.1.val • b + v.2.2.val • c

@[expose] def fuv : Co → Co := lin (1, 2, 2) (0, 1, 2) (0, 2, 1)

@[expose] def ft : Co → Co := lin (1, 2, 0) (0, 3, 0) (0, 2, 3)

@[expose] def fu : Co → Co := lin (1, 0, 0) (0, 0, 1) (0, 1, 0)

@[expose] def fρ : Co → Co := lin (1, 0, 0) (0, 0, 1) (0, 3, 3)

namespace Config

variable {X : Type*} [Group X] (C : Config X)

theorem conj_mul_eq {g a b : X} : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by
  group

theorem conj_pow_eq {g a : X} (n : ℕ) : g⁻¹ * a ^ n * g = (g⁻¹ * a * g) ^ n := by
  have h := conj_pow (i := n) (a := g⁻¹) (b := a)
  rw [inv_inv] at h
  exact h.symm

theorem conj_ev_of {g : X} {a b c : Co} (ha : g⁻¹ * C.w * g = C.ev a)
    (hb : g⁻¹ * C.x * g = C.ev b) (hc : g⁻¹ * C.y * g = C.ev c) (v : Co) :
    g⁻¹ * C.ev v * g = C.ev (lin a b c v) := by
  simp only [ev, lin]
  rw [conj_mul_eq, conj_mul_eq, conj_pow_eq, conj_pow_eq, conj_pow_eq, ha, hb, hc]
  simp only [← ev_nsmul, ← ev_add]
  rfl

theorem xy_sq : (C.x * C.y) ^ 2 = C.x ^ 2 * C.y ^ 2 := by
  have h := C.comm C.x_mem C.y_mem
  rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc C.y C.x, ← h, mul_assoc, mul_assoc]

theorem x_inv_eq : C.x⁻¹ = C.x ^ 3 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', C.hx]

theorem y_inv_eq : C.y⁻¹ = C.y ^ 3 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', C.hy]

theorem ev_122 : C.ev (1, 2, 2) = C.w * (C.x * C.y) ^ 2 := by
  rw [xy_sq]; simp [ev, show (1 : ZMod 2).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl,
    mul_assoc]

theorem ev_012 : C.ev (0, 1, 2) = C.x * C.y ^ 2 := by
  simp [ev, show (1 : ZMod 4).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl]

theorem ev_021 : C.ev (0, 2, 1) = C.y * C.x ^ 2 := by
  simp [ev, show (1 : ZMod 4).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl]
  exact C.comm (Subgroup.pow_mem _ C.x_mem 2) C.y_mem

theorem ev_120 : C.ev (1, 2, 0) = C.w * C.x ^ 2 := by
  simp [ev, show (1 : ZMod 2).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl]

theorem ev_030 : C.ev (0, 3, 0) = C.x⁻¹ := by
  rw [x_inv_eq]; simp [ev, show (3 : ZMod 4).val = 3 from rfl]

theorem ev_023 : C.ev (0, 2, 3) = C.x ^ 2 * C.y⁻¹ := by
  rw [y_inv_eq]; simp [ev, show (2 : ZMod 4).val = 2 from rfl, show (3 : ZMod 4).val = 3 from rfl]

theorem ev_033 : C.ev (0, 3, 3) = C.x⁻¹ * C.y⁻¹ := by
  rw [x_inv_eq, y_inv_eq]; simp [ev, show (3 : ZMod 4).val = 3 from rfl]

theorem hu_y : C.u⁻¹ * C.y * C.u = C.x := by
  have hu : C.u⁻¹ = C.u := by rw [inv_eq_iff_mul_eq_one, ← pow_two, C.hu2]
  rw [← C.hu_x, hu]
  calc C.u * (C.u * C.x * C.u) * C.u = (C.u * C.u) * C.x * (C.u * C.u) := by group
    _ = C.x := by rw [← pow_two, C.hu2]; group

theorem conj_uv_ev (v : Co) : C.uv⁻¹ * C.ev v * C.uv = C.ev (fuv v) :=
  C.conj_ev_of (by rw [C.huv_w, ev_122]) (by rw [C.huv_x, ev_012]) (by rw [C.huv_y, ev_021]) v

theorem conj_t_ev (v : Co) : C.t⁻¹ * C.ev v * C.t = C.ev (ft v) :=
  C.conj_ev_of (by rw [C.ht_w, ev_120]) (by rw [C.ht_x, ev_030]) (by rw [C.ht_y, ev_023]) v

theorem conj_u_ev (v : Co) : C.u⁻¹ * C.ev v * C.u = C.ev (fu v) :=
  C.conj_ev_of (by rw [C.hu_w, ev_w]) (by rw [C.hu_x, ev_y]) (by rw [C.hu_y, ev_x]) v

theorem conj_ρ_ev (v : Co) : C.ρ⁻¹ * C.ev v * C.ρ = C.ev (fρ v) :=
  C.conj_ev_of (by rw [C.hρ_w, ev_w]) (by rw [C.hρ_x, ev_y]) (by rw [C.hρ_y, ev_033]) v

end Config

end CFSG.CGT.Stroth77.Arch76

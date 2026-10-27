module

public import Mathlib.Algebra.Group.MinimalAxioms
public import CFSG.CGT.Foote81L6.Dihedral
public import CFSG.GH74.GLS.IVK.Lifted.DihedralOuter

public section

namespace CFSG.CGT.Foote81L6.Bridge

theorem zmod_two_pow_zero_eq (a b : ZMod (2 ^ 0)) : a = b :=
  Subsingleton.elim (α := ZMod 1) a b

theorem zmod_two_eq_zero_or_one (j : ZMod 2) : j = 0 ∨ j = 1 := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl

@[expose] def hf (n : ℕ) : ZMod (2 ^ n) := 2 * 2 ^ (n - 2)

@[expose] def θ (n : ℕ) : ZMod (2 ^ n) := hf n - 1

theorem two_mul_hf (n : ℕ) : 2 * hf n = 0 := by
  rcases n with _ | _ | n
  · exact zmod_two_pow_zero_eq _ _
  · decide
  · have h : (2 : ZMod (2 ^ (n + 2))) * hf (n + 2) = ((2 ^ (n + 2) : ℕ) : ZMod (2 ^ (n + 2))) := by
      simp only [hf, Nat.add_sub_cancel]
      push_cast
      ring
    rw [h, ZMod.natCast_self]

theorem hf_add_hf (n : ℕ) : hf n + hf n = 0 := by
  rw [← two_mul, two_mul_hf]

theorem neg_hf (n : ℕ) : -hf n = hf n :=
  neg_eq_of_add_eq_zero_left (hf_add_hf n)

theorem hf_mul_hf (n : ℕ) : hf n * hf n = 0 := by
  rcases n with _ | _ | n
  · exact zmod_two_pow_zero_eq _ _
  · decide
  · have h : hf (n + 2) * hf (n + 2) =
        ((2 ^ (n + 2) : ℕ) : ZMod (2 ^ (n + 2))) * 2 ^ n := by
      simp only [hf, Nat.add_sub_cancel]
      push_cast
      ring
    rw [h, ZMod.natCast_self, zero_mul]

theorem θ_mul_θ (n : ℕ) : θ n * θ n = 1 := by
  unfold θ
  linear_combination hf_mul_hf n - two_mul_hf n

theorem hf_eq {n : ℕ} (hn : 2 ≤ n) : hf n = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [hf, Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
  push_cast
  ring

theorem hf_val {n : ℕ} (hn : 2 ≤ n) : (hf n).val = 2 ^ (n - 1) := by
  rw [hf_eq hn, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]

theorem θ_val {n : ℕ} (hn : 2 ≤ n) : (θ n).val = 2 ^ (n - 1) - 1 := by
  have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [θ, hf_eq hn, show ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) - 1 =
      ((2 ^ (n - 1) - 1 : ℕ) : ZMod (2 ^ n)) by rw [Nat.cast_sub h1, Nat.cast_one],
    ZMod.val_natCast, Nat.mod_eq_of_lt (show 2 ^ (n - 1) - 1 < 2 ^ n by omega)]

theorem hf_ne_zero {n : ℕ} (hn : 2 ≤ n) : hf n ≠ 0 := by
  rw [hf_eq hn, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have h1 := Nat.le_of_dvd (by positivity) h
  have h2 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem hf_ne_two {n : ℕ} (hn : 3 ≤ n) : hf n ≠ 2 := by
  rw [hf_eq (by omega), show (2 : ZMod (2 ^ n)) = ((2 : ℕ) : ZMod (2 ^ n)) by norm_cast,
    Ne, ZMod.natCast_eq_natCast_iff']
  have h1 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : 4 ≤ 2 ^ (n - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (show 2 < 2 ^ n by omega)]
  omega

theorem θ_ne_one {n : ℕ} (hn : 3 ≤ n) : θ n ≠ 1 := by
  intro h
  apply hf_ne_two hn
  have : hf n = θ n + 1 := by rw [θ]; ring
  rw [this, h]
  norm_num

theorem eq_zero_or_hf_of_two_mul {n : ℕ} (hn : 2 ≤ n) {k : ZMod (2 ^ n)} (h : 2 * k = 0) :
    k = 0 ∨ k = hf n := by
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  rcases CFSG.CGT.Foote81L6.eq_zero_or_half (b := b) (by rw [← two_mul]; exact h) with h0 | h1
  · exact Or.inl h0
  · right
    rw [h1, hf_eq hn, Nat.add_sub_cancel]

@[expose] def par {n : ℕ} (k : ZMod (2 ^ n)) : ZMod 2 := (k.val : ZMod 2)

theorem par_zero_eq (k : ZMod (2 ^ 0)) : par k = 0 := by
  rw [zmod_two_pow_zero_eq k 0, par, ZMod.val_zero, Nat.cast_zero]

theorem par_add {n : ℕ} (a b : ZMod (2 ^ n)) : par (a + b) = par a + par b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [par_zero_eq, add_zero]
  · unfold par
    rw [ZMod.val_add, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
    exact Nat.mod_mod_of_dvd _ (dvd_pow_self 2 hn.ne')

theorem par_mul {n : ℕ} (a b : ZMod (2 ^ n)) : par (a * b) = par a * par b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [par_zero_eq, mul_zero]
  · unfold par
    rw [ZMod.val_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
    exact Nat.mod_mod_of_dvd _ (dvd_pow_self 2 hn.ne')

@[simp] theorem par_zero {n : ℕ} : par (0 : ZMod (2 ^ n)) = 0 := by
  rw [par, ZMod.val_zero, Nat.cast_zero]

theorem par_neg {n : ℕ} (a : ZMod (2 ^ n)) : par (-a) = par a := by
  have h := par_add (-a) a
  rw [neg_add_cancel, par_zero] at h
  rw [eq_neg_of_add_eq_zero_left h.symm, ZMod.neg_eq_self_mod_two]

theorem par_sub {n : ℕ} (a b : ZMod (2 ^ n)) : par (a - b) = par a + par b := by
  rw [sub_eq_add_neg, par_add, par_neg]

theorem par_natCast {n : ℕ} (hn : 1 ≤ n) (m : ℕ) : par (m : ZMod (2 ^ n)) = (m : ZMod 2) := by
  rw [par, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff']
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))

theorem par_one {n : ℕ} (hn : 1 ≤ n) : par (1 : ZMod (2 ^ n)) = 1 := by
  simpa using par_natCast hn 1

theorem par_two_mul {n : ℕ} (hn : 1 ≤ n) (a : ZMod (2 ^ n)) : par (2 * a) = 0 := by
  rw [par_mul, show (2 : ZMod (2 ^ n)) = ((2 : ℕ) : ZMod (2 ^ n)) by norm_cast, par_natCast hn,
    ZMod.natCast_self, zero_mul]

theorem par_hf (n : ℕ) : par (hf n) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact par_zero_eq _
  · exact par_two_mul hn _

theorem par_θ {n : ℕ} (hn : 1 ≤ n) : par (θ n) = 1 := by
  have h1 := par_add (θ n) 1
  rw [show θ n + 1 = hf n by rw [θ]; ring, par_hf, par_one hn] at h1
  rw [eq_neg_of_add_eq_zero_left h1.symm, ZMod.neg_eq_self_mod_two]

theorem par_θ_mul {n : ℕ} (k : ZMod (2 ^ n)) : par (θ n * k) = par k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [par_zero_eq]
  · rw [par_mul, par_θ hn, one_mul]

@[expose] def tw {n : ℕ} (j : ZMod 2) (k : ZMod (2 ^ n)) : ZMod (2 ^ n) :=
  if j = 0 then k else θ n * k

section Twist

variable {n : ℕ}

@[simp] theorem tw_zero (k : ZMod (2 ^ n)) : tw 0 k = k := rfl

@[simp] theorem tw_one (k : ZMod (2 ^ n)) : tw 1 k = θ n * k := rfl

theorem tw_tw (j : ZMod 2) (k : ZMod (2 ^ n)) : tw j (tw j k) = k := by
  rcases zmod_two_eq_zero_or_one j with rfl | rfl
  · rfl
  · rw [tw_one, tw_one, ← mul_assoc, θ_mul_θ, one_mul]

theorem tw_add_left (j l : ZMod 2) (k : ZMod (2 ^ n)) : tw (j + l) k = tw j (tw l k) := by
  rcases zmod_two_eq_zero_or_one j with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one l with rfl | rfl
  · rfl
  · rfl
  · rfl
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, tw_zero, tw_tw]

theorem tw_add (j : ZMod 2) (k m : ZMod (2 ^ n)) : tw j (k + m) = tw j k + tw j m := by
  rcases zmod_two_eq_zero_or_one j with rfl | rfl
  · rfl
  · simp only [tw_one, mul_add]

theorem tw_neg (j : ZMod 2) (k : ZMod (2 ^ n)) : tw j (-k) = -tw j k := by
  rcases zmod_two_eq_zero_or_one j with rfl | rfl
  · rfl
  · simp only [tw_one, mul_neg]

@[simp] theorem tw_zero_right (j : ZMod 2) : tw j (0 : ZMod (2 ^ n)) = 0 := by
  rcases zmod_two_eq_zero_or_one j with rfl | rfl
  · rfl
  · simp only [tw_one, mul_zero]

theorem par_tw (j : ZMod 2) (k : ZMod (2 ^ n)) : par (tw j k) = par k := by
  rcases zmod_two_eq_zero_or_one j with rfl | rfl
  · rfl
  · exact par_θ_mul k

theorem θ_mul_hf : θ n * hf n = hf n := by
  rw [θ, sub_mul, hf_mul_hf, one_mul, zero_sub, neg_hf]

theorem tw_hf (j : ZMod 2) : tw j (hf n) = hf n := by
  rcases zmod_two_eq_zero_or_one j with rfl | rfl
  · rfl
  · exact θ_mul_hf

end Twist

@[ext] structure SD (n : ℕ) where
  i : ZMod (2 ^ n)
  j : ZMod 2
deriving DecidableEq

namespace SD

variable {n : ℕ}

instance : Mul (SD n) := ⟨fun x y => ⟨x.i + tw x.j y.i, x.j + y.j⟩⟩

instance : One (SD n) := ⟨⟨0, 0⟩⟩

instance : Inv (SD n) := ⟨fun x => ⟨-tw x.j x.i, x.j⟩⟩

@[simp] theorem mul_i (x y : SD n) : (x * y).i = x.i + tw x.j y.i := rfl

@[simp] theorem mul_j (x y : SD n) : (x * y).j = x.j + y.j := rfl

@[simp] theorem one_i : (1 : SD n).i = 0 := rfl

@[simp] theorem one_j : (1 : SD n).j = 0 := rfl

@[simp] theorem inv_i (x : SD n) : x⁻¹.i = -tw x.j x.i := rfl

@[simp] theorem inv_j (x : SD n) : x⁻¹.j = x.j := rfl

instance : Group (SD n) :=
  Group.ofLeftAxioms
    (fun x y z => by
      ext
      · simp only [mul_i, mul_j, tw_add, tw_add_left, add_assoc]
      · simp only [mul_j, add_assoc])
    (fun x => by ext <;> simp)
    (fun x => by
      ext
      · simp only [mul_i, inv_i, inv_j, tw_tw, neg_add_cancel, one_i]
      · simp only [mul_j, inv_j, CharTwo.add_self_eq_zero, one_j])

@[expose] def ω : SD n := ⟨1, 0⟩

@[expose] def σ : SD n := ⟨0, 1⟩

@[expose] def z : SD n := ⟨hf n, 0⟩

@[expose] def rotHom : Multiplicative (ZMod (2 ^ n)) →* SD n where
  toFun k := ⟨k.toAdd, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp

theorem rotHom_apply (k : Multiplicative (ZMod (2 ^ n))) : rotHom k = ⟨k.toAdd, 0⟩ := rfl

theorem rotHom_injective : Function.Injective (rotHom (n := n)) := fun a b h =>
  congrArg Multiplicative.ofAdd (congrArg SD.i h)

theorem mk_zero_pow (a : ZMod (2 ^ n)) (k : ℕ) : (⟨a, 0⟩ : SD n) ^ k = ⟨k * a, 0⟩ := by
  rw [show (⟨a, 0⟩ : SD n) = rotHom (Multiplicative.ofAdd a) from rfl, ← map_pow, rotHom_apply]
  ext
  · simp [nsmul_eq_mul]
  · rfl

theorem orderOf_mk_zero (a : ZMod (2 ^ n)) : orderOf (⟨a, 0⟩ : SD n) = addOrderOf a := by
  rw [show (⟨a, 0⟩ : SD n) = rotHom (Multiplicative.ofAdd a) from rfl,
    orderOf_injective _ rotHom_injective, orderOf_ofAdd_eq_addOrderOf]

theorem orderOf_ω : orderOf (ω : SD n) = 2 ^ n := by
  rw [ω, orderOf_mk_zero, ZMod.addOrderOf_one]

theorem ω_pow (k : ℕ) : (ω : SD n) ^ k = ⟨k, 0⟩ := by
  rw [ω, mk_zero_pow, mul_one]

theorem σ_sq : (σ : SD n) ^ 2 = 1 := by
  rw [pow_two]
  ext
  · simp [σ]
  · simp only [σ, mul_j, one_j]
    rfl

theorem σ_mul_ω_mul_σ_inv : (σ : SD n) * ω * σ⁻¹ = ω ^ (θ n).val := by
  rw [ω_pow, ZMod.natCast_zmod_val]
  ext
  · simp [σ, ω]
  · simp only [σ, ω, mul_j, inv_j]
    rfl

theorem z_mul_self : (z : SD n) * z = 1 := by
  ext
  · simp [z, hf_add_hf]
  · simp [z]

theorem z_comm (x : SD n) : x * z = z * x := by
  ext
  · simp only [mul_i, z, tw_hf, tw_zero]
    ring
  · simp [z]

theorem z_ne_one (hn : 2 ≤ n) : (z : SD n) ≠ 1 := fun h => hf_ne_zero hn (congrArg SD.i h)

theorem ω_pow_hf : (ω : SD n) ^ (hf n).val = z := by
  rw [ω_pow, ZMod.natCast_zmod_val, z]

@[expose] def det (x : SD n) : ZMod 2 := par x.i + x.j

theorem det_mul (x y : SD n) : (x * y).det = x.det + y.det := by
  simp only [det, mul_i, mul_j, par_add, par_tw]
  ring

@[simp] theorem det_one : (1 : SD n).det = 0 := by
  simp [det]

theorem det_inv (x : SD n) : x⁻¹.det = x.det := by
  simp only [det, inv_i, inv_j, par_neg, par_tw]

theorem det_z : (z : SD n).det = 0 := by
  simp [det, z, par_hf]

theorem det_σ : (σ : SD n).det = 1 := by
  simp [det, σ]

theorem det_ω (hn : 1 ≤ n) : (ω : SD n).det = 1 := by
  simp [det, ω, par_one hn]

@[expose] def detHom : SD n →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd x.det
  map_one' := by simp
  map_mul' x y := by rw [det_mul, ofAdd_add]

@[expose] def equivProd : SD n ≃ ZMod (2 ^ n) × ZMod 2 where
  toFun x := (x.i, x.j)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (SD n) := Fintype.ofEquiv _ equivProd.symm

instance : Finite (SD n) := Finite.of_equiv _ equivProd.symm

theorem card : Nat.card (SD n) = 2 ^ (n + 1) := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_zmod, Nat.card_zmod, pow_succ]

section Lift

variable {G : Type*} [Group G] {w s : G}

theorem pow_val_add (hw : w ^ 2 ^ n = 1) (a b : ZMod (2 ^ n)) :
    w ^ (a + b).val = w ^ a.val * w ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hw, pow_add]

theorem pow_val_add_two (hs : s ^ 2 = 1) (j l : ZMod 2) :
    s ^ (j + l).val = s ^ j.val * s ^ l.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hs, pow_add]

theorem pow_val_tw (hw : w ^ 2 ^ n = 1) (hsw : s * w * s⁻¹ = w ^ (θ n).val)
    (j : ZMod 2) (k : ZMod (2 ^ n)) : s ^ j.val * w ^ k.val = w ^ (tw j k).val * s ^ j.val := by
  rcases zmod_two_eq_zero_or_one j with rfl | rfl
  · simp
  · have hconj : s * w ^ k.val * s⁻¹ = w ^ ((θ n).val * k.val) := by
      rw [← conj_pow, hsw, pow_mul]
    have hval : w ^ (θ n * k).val = w ^ ((θ n).val * k.val) := by
      rw [ZMod.val_mul, ← pow_eq_pow_mod _ hw]
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, tw_one, hval, ← hconj, inv_mul_cancel_right]

@[expose] def lift (hw : w ^ 2 ^ n = 1) (hs : s ^ 2 = 1) (hsw : s * w * s⁻¹ = w ^ (θ n).val) :
    SD n →* G where
  toFun x := w ^ x.i.val * s ^ x.j.val
  map_one' := by simp
  map_mul' x y := by
    simp only [mul_i, mul_j]
    rw [pow_val_add hw, pow_val_add_two hs]
    simp only [mul_assoc]
    rw [← mul_assoc (s ^ x.j.val), pow_val_tw hw hsw, mul_assoc]

theorem lift_apply (hw : w ^ 2 ^ n = 1) (hs : s ^ 2 = 1) (hsw : s * w * s⁻¹ = w ^ (θ n).val)
    (x : SD n) : lift hw hs hsw x = w ^ x.i.val * s ^ x.j.val := rfl

theorem lift_ω (hn : 1 ≤ n) (hw : w ^ 2 ^ n = 1) (hs : s ^ 2 = 1)
    (hsw : s * w * s⁻¹ = w ^ (θ n).val) : lift hw hs hsw ω = w := by
  haveI : Fact (1 < 2 ^ n) := ⟨Nat.one_lt_two_pow (by omega)⟩
  change w ^ (1 : ZMod (2 ^ n)).val * s ^ (0 : ZMod 2).val = w
  rw [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, mul_one]

theorem lift_σ (hw : w ^ 2 ^ n = 1) (hs : s ^ 2 = 1) (hsw : s * w * s⁻¹ = w ^ (θ n).val) :
    lift hw hs hsw σ = s := by
  change w ^ (0 : ZMod (2 ^ n)).val * s ^ (1 : ZMod 2).val = s
  rw [ZMod.val_zero, pow_zero, one_mul, show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem lift_injective (hw : w ^ 2 ^ n = 1) (hs : s ^ 2 = 1) (hsw : s * w * s⁻¹ = w ^ (θ n).val)
    (hword : orderOf w = 2 ^ n) (hsn : s ∉ Subgroup.zpowers w) :
    Function.Injective (lift hw hs hsw) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [lift_apply] at hx
  rcases zmod_two_eq_zero_or_one x.j with hj | hj
  · rw [hj, ZMod.val_zero, pow_zero, mul_one] at hx
    have h1 : orderOf w ∣ x.i.val := orderOf_dvd_of_pow_eq_one hx
    rw [hword] at h1
    have h2 : x.i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt x.i)
    ext
    · exact (ZMod.val_eq_zero x.i).1 h2
    · exact hj
  · exfalso
    apply hsn
    rw [hj, show (1 : ZMod 2).val = 1 from rfl, pow_one] at hx
    rw [eq_inv_of_mul_eq_one_right hx]
    exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers w _)

end Lift

theorem eq_one_or_eq_z_of_comm (hn : 3 ≤ n) {x : SD n} (hω : x * ω = ω * x)
    (hσ : x * σ = σ * x) : x = 1 ∨ x = z := by
  have hj : x.j = 0 := by
    rcases zmod_two_eq_zero_or_one x.j with h | h
    · exact h
    · exfalso
      have h1 := congrArg SD.i hω
      simp only [mul_i, ω, h, tw_one, tw_zero, mul_one] at h1
      exact θ_ne_one hn (by linear_combination h1)
  have h2 : hf n * x.i = 2 * x.i := by
    have h1 := congrArg SD.i hσ
    simp only [mul_i, σ, hj, tw_zero, tw_one, add_zero, zero_add] at h1
    rw [θ] at h1
    linear_combination -h1
  obtain ⟨a, ha | ha⟩ := CFSG.GH74.GLS.IVK.Lifted.zmod_exists_two_mul (2 ^ n) x.i
  ·
    have h3 : 2 * x.i = 0 := by
      rw [← h2, ha, ← mul_assoc, mul_comm (hf n) 2, two_mul_hf, zero_mul]
    rcases eq_zero_or_hf_of_two_mul (by omega) h3 with h4 | h4
    · left
      ext
      · exact h4
      · exact hj
    · right
      ext
      · exact h4
      · exact hj
  ·
    exfalso
    have h3 : 2 * x.i = hf n := by
      rw [← h2, ha, mul_add, ← mul_assoc, mul_comm (hf n) 2, two_mul_hf, zero_mul, zero_add,
        mul_one]
    have h4 : 2 * (2 * a + 1 - 2 ^ (n - 2)) = 0 := by
      rw [ha, hf] at h3
      linear_combination h3
    have hpar : par (2 * a + 1 - 2 ^ (n - 2) : ZMod (2 ^ n)) = 1 := by
      have h5 : (2 : ZMod (2 ^ n)) ^ (n - 2) = 2 * 2 ^ (n - 3) := by
        rw [← pow_succ', show n - 3 + 1 = n - 2 by omega]
      rw [par_sub, par_add, par_two_mul (by omega), par_one (by omega), h5,
        par_two_mul (by omega)]
      ring
    rcases eq_zero_or_hf_of_two_mul (by omega) h4 with h5 | h5
    · rw [h5, par_zero] at hpar
      exact zero_ne_one hpar
    · rw [h5, par_hf] at hpar
      exact zero_ne_one hpar

end SD

end CFSG.CGT.Foote81L6.Bridge

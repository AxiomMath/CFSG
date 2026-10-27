module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Model
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup

structure Setting (G : Type) [Group G] [Finite G] where
  t : G
  L : Subgroup G
  a : G
  b : G
  g : G
  simple : IsSimpleGroup G
  nonabelian : ∃ x y : G, x * y ≠ y * x
  t_sq : t * t = 1
  t_ne : t ≠ 1
  comm : ∀ ℓ ∈ L, t * ℓ = ℓ * t
  t_not_mem : t ∉ L
  centralizer_eq : centralizer ({t} : Set G) = L ⊔ zpowers t
  a_mem : a ∈ L
  b_mem : b ∈ L
  g_mem : g ∈ L
  a8 : a ^ 8 = 1
  b_sq : b * b = 1
  rel : b * a * b⁻¹ = a ^ 3
  a4 : a ^ 4 ≠ 1
  b_not_pow : ∀ j : ℕ, b ≠ a ^ j
  g_z : g * a ^ 4 * g⁻¹ = b
  g_b : g * b * g⁻¹ = a ^ 4 * b
  card_L : Nat.card L = 7920
  card_inv : Nat.card {u : L // orderOf u = 2} = 165
  conj_inv : ∀ u v : L, orderOf u = 2 → orderOf v = 2 → IsConj u v

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem t_pow (n : ℕ) : H.t ^ n = H.t ^ (n % 2) :=
  pow_eq_pow_mod n (by rw [pow_two]; exact H.t_sq)

theorem b_pow (n : ℕ) : H.b ^ n = H.b ^ (n % 2) :=
  pow_eq_pow_mod n (by rw [pow_two]; exact H.b_sq)

theorem a_pow (n : ℕ) : H.a ^ n = H.a ^ (n % 8) := pow_eq_pow_mod n H.a8

theorem b_inv : H.b⁻¹ = H.b := inv_eq_of_mul_eq_one_right H.b_sq

theorem t_comm_a : H.t * H.a = H.a * H.t := H.comm _ H.a_mem

theorem t_comm_b : H.t * H.b = H.b * H.t := H.comm _ H.b_mem

theorem a_pow_mul_b (n : ℕ) : H.a ^ n * H.b = H.b * H.a ^ (3 * n) := by
  have h : H.b * H.a ^ n * H.b⁻¹ = H.a ^ (3 * n) := by
    have := congrArg (fun x => x ^ n) H.rel
    simp only [conj_pow, ← pow_mul] at this
    exact this
  rw [H.b_inv] at h
  calc H.a ^ n * H.b = H.b * (H.b * H.a ^ n * H.b) := by
        rw [← mul_assoc, ← mul_assoc, H.b_sq, one_mul]
    _ = H.b * H.a ^ (3 * n) := by rw [h]

theorem orderOf_a : orderOf H.a = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := H.a) (by simpa using H.a4)
    (by simpa using H.a8)
  simpa using h

@[expose] def psiN (k i j : ℕ) : G := H.t ^ k * H.b ^ i * H.a ^ j

theorem a_pow_mul_b_pow (j i : ℕ) : H.a ^ j * H.b ^ i = H.b ^ i * H.a ^ (j * 3 ^ i) := by
  induction i with
  | zero => simp
  | succ n ih =>
    calc H.a ^ j * H.b ^ (n + 1) = (H.a ^ j * H.b ^ n) * H.b := by rw [pow_succ, mul_assoc]
      _ = H.b ^ n * H.a ^ (j * 3 ^ n) * H.b := by rw [ih]
      _ = H.b ^ n * (H.a ^ (j * 3 ^ n) * H.b) := by rw [mul_assoc]
      _ = H.b ^ n * (H.b * H.a ^ (3 * (j * 3 ^ n))) := by rw [H.a_pow_mul_b]
      _ = H.b ^ (n + 1) * H.a ^ (j * 3 ^ (n + 1)) := by
        rw [← mul_assoc, ← pow_succ]
        congr 2
        ring

theorem psiN_mul (k i j k' i' j' : ℕ) :
    H.psiN k i j * H.psiN k' i' j' = H.psiN (k + k') (i + i') (j * 3 ^ i' + j') := by
  unfold psiN
  have hat : Commute (H.a ^ j) (H.t ^ k') :=
    Commute.pow_pow (Commute.symm (show Commute H.t H.a from H.t_comm_a)) j k'
  have hbt : Commute (H.b ^ i) (H.t ^ k') :=
    Commute.pow_pow (Commute.symm (show Commute H.t H.b from H.t_comm_b)) i k'
  calc H.t ^ k * H.b ^ i * H.a ^ j * (H.t ^ k' * H.b ^ i' * H.a ^ j')
      = H.t ^ k * (H.b ^ i * (H.a ^ j * (H.t ^ k' * (H.b ^ i' * H.a ^ j')))) := by
        simp only [mul_assoc]
    _ = H.t ^ k * (H.b ^ i * (H.t ^ k' * (H.a ^ j * (H.b ^ i' * H.a ^ j')))) := by
        rw [hat.left_comm]
    _ = H.t ^ k * (H.t ^ k' * (H.b ^ i * (H.a ^ j * (H.b ^ i' * H.a ^ j')))) := by
        rw [hbt.left_comm]
    _ = H.t ^ (k + k') * (H.b ^ i * ((H.a ^ j * H.b ^ i') * H.a ^ j')) := by
        rw [pow_add]; simp only [mul_assoc]
    _ = H.t ^ (k + k') * (H.b ^ i * ((H.b ^ i' * H.a ^ (j * 3 ^ i')) * H.a ^ j')) := by
        rw [H.a_pow_mul_b_pow]
    _ = H.t ^ (k + k') * H.b ^ (i + i') * H.a ^ (j * 3 ^ i' + j') := by
        rw [pow_add H.t, pow_add H.b, pow_add H.a]; simp only [mul_assoc]

theorem psiN_reduce (k i j : ℕ) : H.psiN k i j = H.psiN (k % 2) (i % 2) (j % 8) := by
  unfold psiN
  rw [← H.t_pow, ← H.b_pow, ← H.a_pow]

theorem psiN_congr {k i j k' i' j' : ℕ} (hk : k % 2 = k' % 2) (hi : i % 2 = i' % 2)
    (hj : j % 8 = j' % 8) : H.psiN k i j = H.psiN k' i' j' := by
  rw [psiN_reduce, psiN_reduce (k := k'), hk, hi, hj]

@[expose] def psi (x : SMod) : G := H.psiN x.1.val x.2.1.val x.2.2.val

theorem three_val (i : Fin 2) : (SMod.three i).val = 3 ^ i.val := by
  fin_cases i <;> simp [SMod.three]

theorem psi_mul (x y : SMod) : H.psi (SMod.mul x y) = H.psi x * H.psi y := by
  unfold psi
  rw [psiN_mul]
  apply psiN_congr
  · simp [SMod.mul, Fin.val_add, Nat.add_mod]
  · simp [SMod.mul, Fin.val_add, Nat.add_mod]
  · simp [SMod.mul, Fin.val_add, Fin.val_mul, three_val, Nat.add_mod, Nat.mul_mod]

theorem psi_def (x : SMod) :
    H.psi x = H.t ^ x.1.val * (H.b ^ x.2.1.val * H.a ^ x.2.2.val) := by
  unfold psi psiN; rw [mul_assoc]

theorem mem_L_ba (i j : ℕ) : H.b ^ i * H.a ^ j ∈ H.L :=
  H.L.mul_mem (H.L.pow_mem H.b_mem i) (H.L.pow_mem H.a_mem j)

theorem tpow_mul_inj {k k' : ℕ} (hk : k < 2) (hk' : k' < 2) {u u' : G} (hu : u ∈ H.L)
    (hu' : u' ∈ H.L) (h : H.t ^ k * u = H.t ^ k' * u') : k = k' ∧ u = u' := by
  have hk1 : k = 0 ∨ k = 1 := by omega
  have hk1' : k' = 0 ∨ k' = 1 := by omega
  rcases hk1 with rfl | rfl <;> rcases hk1' with rfl | rfl
  · simpa using h
  · exfalso
    apply H.t_not_mem
    have : H.t = u * u'⁻¹ := by
      simp only [pow_zero, pow_one, one_mul] at h
      rw [h]; group
    rw [this]; exact H.L.mul_mem hu (H.L.inv_mem hu')
  · exfalso
    apply H.t_not_mem
    have : H.t = u' * u⁻¹ := by
      simp only [pow_zero, pow_one, one_mul] at h
      rw [← h]; group
    rw [this]; exact H.L.mul_mem hu' (H.L.inv_mem hu)
  · simpa using h

theorem ba_inj {i i' j j' : ℕ} (hi : i < 2) (hi' : i' < 2) (hj : j < 8) (hj' : j' < 8)
    (h : H.b ^ i * H.a ^ j = H.b ^ i' * H.a ^ j') : i = i' ∧ j = j' := by
  have hi1 : i = 0 ∨ i = 1 := by omega
  have hi1' : i' = 0 ∨ i' = 1 := by omega
  have hord := H.orderOf_a
  have hinj : ∀ {m n : ℕ}, m < 8 → n < 8 → H.a ^ m = H.a ^ n → m = n := fun hm hn hmn =>
    pow_injOn_Iio_orderOf (x := H.a) (by rw [hord]; exact hm) (by rw [hord]; exact hn) hmn
  have key : ∀ {m n : ℕ}, m < 8 → n < 8 → H.b * H.a ^ m = H.a ^ n → False := by
    intro m n hm hn hmn
    apply H.b_not_pow (n + (8 - m))
    have h8 : H.a ^ m * H.a ^ (8 - m) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hm.le]; exact H.a8
    calc H.b = H.b * (H.a ^ m * H.a ^ (8 - m)) := by rw [h8, mul_one]
      _ = (H.b * H.a ^ m) * H.a ^ (8 - m) := by rw [mul_assoc]
      _ = H.a ^ (n + (8 - m)) := by rw [hmn, pow_add]
  rcases hi1 with rfl | rfl <;> rcases hi1' with rfl | rfl
  · exact ⟨rfl, hinj hj hj' (by simpa using h)⟩
  · exfalso
    exact key hj' hj (by simpa using h.symm)
  · exfalso
    exact key hj hj' (by simpa using h)
  · exact ⟨rfl, hinj hj hj' (by simpa using mul_left_cancel h)⟩

theorem psi_injective : Function.Injective H.psi := by
  intro x y hxy
  rw [psi_def, psi_def] at hxy
  obtain ⟨hk, hu⟩ := tpow_mul_inj H x.1.isLt y.1.isLt (mem_L_ba H _ _) (mem_L_ba H _ _) hxy
  obtain ⟨hi, hj⟩ := ba_inj H x.2.1.isLt y.2.1.isLt x.2.2.isLt y.2.2.isLt hu
  exact Prod.ext (Fin.ext hk) (Prod.ext (Fin.ext hi) (Fin.ext hj))

theorem psi_one : H.psi SMod.one = 1 := by
  simp [psi, psiN, SMod.one]

theorem psi_inv (x : SMod) : H.psi (SMod.inv x) = (H.psi x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← psi_mul, SMod.inv_mul', psi_one]

end Setting

end CFSG.EvenSporadicStandard.M11Std

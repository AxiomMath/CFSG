module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEBasic
import CFSG.ClassicalInvolution.Q3.TL4SepTwoD

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

@[expose] def IsHyp (Ω : Set (Subgroup G)) (H : Subgroup G) : Prop :=
  H ≤ zGroup Ω ∧ Nat.card H = 4

theorem det_tw_isUniqueInvolution_conjSub_iff {K : Subgroup G} {z g : G} :
    IsUniqueInvolution (conjSub g K) z ↔ IsUniqueInvolution K (g⁻¹ * z * g) := by
  constructor
  · intro hz
    have := hz.conj g⁻¹
    rwa [conjSub_inv_conjSub, inv_inv] at this
  · intro hz
    have := hz.conj g
    rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at this

theorem det_tw_q8_central {M : Subgroup G} {v i j : G} (hQ : Q8Data M v i j) {x : G}
    (hx : x ∈ M) : v * x = x * v := by
  have hiv : i * v = v * i := by
    calc i * v = i * (i * i) := by rw [hQ.sq_i]
      _ = (i * i) * i := by group
      _ = v * i := by rw [hQ.sq_i]
  have hjv : j * v = v * j := by
    calc j * v = j * (j * j) := by rw [hQ.sq_j]
      _ = (j * j) * j := by group
      _ = v * j := by rw [hQ.sq_j]
  have hijv : (i * j) * v = v * (i * j) := by
    calc (i * j) * v = i * (j * v) := by group
      _ = i * (v * j) := by rw [hjv]
      _ = (i * v) * j := by group
      _ = (v * i) * j := by rw [hiv]
      _ = v * (i * j) := by group
  rcases hQ.nf x hx with h | h | h | h | h | h | h | h <;> rw [h]
  · simp
  · exact hiv.symm
  · calc v * (v * i) = v * (i * v) := by rw [hiv]
      _ = (v * i) * v := by group
  · exact hjv.symm
  · calc v * (v * j) = v * (j * v) := by rw [hjv]
      _ = (v * j) * v := by group
  · exact hijv.symm
  · calc v * (v * (i * j)) = v * ((i * j) * v) := by rw [hijv]
      _ = (v * (i * j)) * v := by group

theorem det_tw_q8_ij_sq {M : Subgroup G} {v i j : G} (hQ : Q8Data M v i j) :
    (i * j) * (i * j) = v := by
  have hiv : i * v = v * i := by
    calc i * v = i * (i * i) := by rw [hQ.sq_i]
      _ = (i * i) * i := by group
      _ = v * i := by rw [hQ.sq_i]
  have hvv : v * v = 1 := hQ.inv.sq
  calc (i * j) * (i * j) = i * (j * i) * j := by group
    _ = i * (v * (i * j)) * j := by rw [hQ.comm]
    _ = (i * v) * (i * j * j) := by group
    _ = (v * i) * (i * j * j) := by rw [hiv]
    _ = v * (i * i) * (j * j) := by group
    _ = v := by rw [hQ.sq_i, hQ.sq_j, hvv, one_mul]

theorem det_tw_q8_sq {M : Subgroup G} {v i j : G} (hQ : Q8Data M v i j) {x : G} (hx : x ∈ M)
    (hxv : x ∉ Subgroup.zpowers v) : x * x = v := by
  have hiv : i * v = v * i := by
    calc i * v = i * (i * i) := by rw [hQ.sq_i]
      _ = (i * i) * i := by group
      _ = v * i := by rw [hQ.sq_i]
  have hjv : j * v = v * j := by
    calc j * v = j * (j * j) := by rw [hQ.sq_j]
      _ = (j * j) * j := by group
      _ = v * j := by rw [hQ.sq_j]
  have hijv : (i * j) * v = v * (i * j) := by
    calc (i * j) * v = i * (j * v) := by group
      _ = i * (v * j) := by rw [hjv]
      _ = (i * v) * j := by group
      _ = (v * i) * j := by rw [hiv]
      _ = v * (i * j) := by group
  have hvv : v * v = 1 := hQ.inv.sq
  have hij := det_tw_q8_ij_sq hQ
  have h1 : x ≠ 1 := fun h => hxv (h ▸ Subgroup.one_mem _)
  have h2 : x ≠ v := fun h => hxv (h ▸ Subgroup.mem_zpowers v)
  rcases hQ.nf x hx with h | h | h | h | h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · rw [h]; exact hQ.sq_i
  · rw [h]
    calc (v * i) * (v * i) = v * (i * v) * i := by group
      _ = v * (v * i) * i := by rw [hiv]
      _ = (v * v) * (i * i) := by group
      _ = v := by rw [hvv, hQ.sq_i, one_mul]
  · rw [h]; exact hQ.sq_j
  · rw [h]
    calc (v * j) * (v * j) = v * (j * v) * j := by group
      _ = v * (v * j) * j := by rw [hjv]
      _ = (v * v) * (j * j) := by group
      _ = v := by rw [hvv, hQ.sq_j, one_mul]
  · rw [h]; exact hij
  · rw [h]
    calc (v * (i * j)) * (v * (i * j)) = v * ((i * j) * v) * (i * j) := by group
      _ = v * (v * (i * j)) * (i * j) := by rw [hijv]
      _ = (v * v) * ((i * j) * (i * j)) := by group
      _ = v := by rw [hvv, hij, one_mul]

theorem det_tw_q8_noncomm {M : Subgroup G} {v i j : G} (hQ : Q8Data M v i j) {x : G}
    (hx : x ∈ M) (hxv : x ∉ Subgroup.zpowers v) : ∃ w ∈ M, x * w ≠ w * x := by
  have hv1 : v ≠ 1 := hQ.inv.ne_one
  have hcomm : j * i = v * (i * j) := hQ.comm
  have hiv : i * v = v * i := by
    calc i * v = i * (i * i) := by rw [hQ.sq_i]
      _ = (i * i) * i := by group
      _ = v * i := by rw [hQ.sq_i]
  have hjv : j * v = v * j := by
    calc j * v = j * (j * j) := by rw [hQ.sq_j]
      _ = (j * j) * j := by group
      _ = v * j := by rw [hQ.sq_j]
  have hvv : v * v = 1 := hQ.inv.sq
  have key : ∀ a : G, v * a = a → False := fun a ha => hv1 (by simpa using ha)
  have h1 : x ≠ 1 := fun h => hxv (h ▸ Subgroup.one_mem _)
  have h2 : x ≠ v := fun h => hxv (h ▸ Subgroup.mem_zpowers v)
  rcases hQ.nf x hx with h | h | h | h | h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  ·
    refine ⟨j, hQ.mem_j, fun heq => key (i * j) ?_⟩
    rw [h, hcomm] at heq
    exact heq.symm
  ·
    refine ⟨j, hQ.mem_j, fun heq => key (i * j) ?_⟩
    rw [h] at heq
    have e1 : v * i * j = v * (i * j) := by group
    have e2 : j * (v * i) = v * (v * (i * j)) := by
      calc j * (v * i) = (j * v) * i := by group
        _ = (v * j) * i := by rw [hjv]
        _ = v * (j * i) := by group
        _ = v * (v * (i * j)) := by rw [hcomm]
    rw [e1, e2] at heq
    exact (mul_left_cancel heq).symm
  ·
    refine ⟨i, hQ.mem_i, fun heq => key (i * j) ?_⟩
    rw [h, hcomm] at heq
    exact heq
  ·
    refine ⟨i, hQ.mem_i, fun heq => key (i * j) ?_⟩
    rw [h] at heq
    have e1 : i * (v * j) = v * (i * j) := by
      calc i * (v * j) = (i * v) * j := by group
        _ = (v * i) * j := by rw [hiv]
        _ = v * (i * j) := by group
    have e2 : v * j * i = v * (v * (i * j)) := by
      calc v * j * i = v * (j * i) := by group
        _ = v * (v * (i * j)) := by rw [hcomm]
    rw [e1, e2] at heq
    exact mul_left_cancel heq
  ·
    refine ⟨i, hQ.mem_i, fun heq => key j ?_⟩
    rw [h] at heq
    have e1 : i * j * i = j := by
      calc i * j * i = i * (j * i) := by group
        _ = i * (v * (i * j)) := by rw [hcomm]
        _ = (i * v) * (i * j) := by group
        _ = (v * i) * (i * j) := by rw [hiv]
        _ = (v * (i * i)) * j := by group
        _ = (v * v) * j := by rw [hQ.sq_i]
        _ = j := by rw [hvv, one_mul]
    have e2 : i * (i * j) = v * j := by
      calc i * (i * j) = (i * i) * j := by group
        _ = v * j := by rw [hQ.sq_i]
    rw [e1, e2] at heq
    exact heq.symm
  ·
    refine ⟨i, hQ.mem_i, fun heq => key j ?_⟩
    rw [h] at heq
    have e1 : v * (i * j) * i = v * j := by
      calc v * (i * j) * i = v * ((i * j) * i) := by group
        _ = v * j := by
          congr 1
          calc i * j * i = i * (j * i) := by group
            _ = i * (v * (i * j)) := by rw [hcomm]
            _ = (i * v) * (i * j) := by group
            _ = (v * i) * (i * j) := by rw [hiv]
            _ = (v * (i * i)) * j := by group
            _ = (v * v) * j := by rw [hQ.sq_i]
            _ = j := by rw [hvv, one_mul]
    have e2 : i * (v * (i * j)) = v * (v * j) := by
      calc i * (v * (i * j)) = (i * v) * (i * j) := by group
        _ = (v * i) * (i * j) := by rw [hiv]
        _ = v * (i * i) * j := by group
        _ = v * v * j := by rw [hQ.sq_i]
        _ = v * (v * j) := by group
    rw [e1, e2] at heq
    exact (mul_left_cancel heq).symm

theorem det_tw_eq_one_or_of_mem_zpowers {v x : G} (hvv : v * v = 1) (hv1 : v ≠ 1)
    (hx : x ∈ Subgroup.zpowers v) : x = 1 ∨ x = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ho : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvv) hv1
  rw [← zpow_mod_orderOf, ho]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> simp [hk]

def det_tw_tau (v : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun r k => (if r = k then 1 else 0) + v r * (![0, v 2, v 1] : Fin 3 → ZMod 2) k

theorem det_tw_tau_mulVec (v w : Fin 3 → ZMod 2) :
    (det_tw_tau v).mulVec w = w + (v 2 * w 1 + v 1 * w 2) • v := by
  funext r
  fin_cases r <;> simp [det_tw_tau, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem det_tw_finite : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det ≠ 0 →
    A.mulVec ![1, 0, 0] = ![1, 0, 0] → ∃ a b c : Fin 3 → ZMod 2,
      A = det_tw_tau a * det_tw_tau b * det_tw_tau c := by
  decide +kernel

theorem det_tw_sq_mem {K : Subgroup G} {u i j : G} (hQ : Q8Data K u i j) {x : G} (hx : x ∈ K) :
    x * x = 1 ∨ x * x = u := by
  by_cases hxu : x ∈ Subgroup.zpowers u
  · rcases det_tw_eq_one_or_of_mem_zpowers hQ.inv.sq hQ.inv.ne_one hxu with h1 | h1
    · left; rw [h1, one_mul]
    · left; rw [h1]; exact hQ.inv.sq
  · right; exact det_tw_q8_sq hQ hx hxu

theorem det_tw_comm_mod {K : Subgroup G} {u i j : G} (hQ : Q8Data K u i j) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) : b * a = a * b ∨ b * a = u * (a * b) := by
  have hcen : ∀ x ∈ K, x * u = u * x := fun x hx => (det_tw_q8_central hQ hx).symm
  have hab : a * b ∈ K := K.mul_mem ha hb
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hQ.inv.sq
  have key : b * a = a * ((a * a)⁻¹ * ((a * b) * (a * b)) * (b * b)⁻¹) * b := by group
  have hPQ : (a * a)⁻¹ * ((a * b) * (a * b)) * (b * b)⁻¹ = 1 ∨
      (a * a)⁻¹ * ((a * b) * (a * b)) * (b * b)⁻¹ = u := by
    rcases det_tw_sq_mem hQ ha with hp | hp <;> rcases det_tw_sq_mem hQ hab with hr | hr <;>
      rcases det_tw_sq_mem hQ hb with hq | hq <;>
      simp only [hp, hq, hr, hu_inv, inv_one, mul_one, one_mul, hQ.inv.sq, mul_assoc]
    all_goals first
      | (left; simp [hQ.inv.sq, hu_inv, mul_assoc])
      | (right; simp [hQ.inv.sq, hu_inv, mul_assoc])
  rcases hPQ with h1 | h1
  · left
    rw [key, h1, mul_one]
  · right
    rw [key, h1]
    calc a * u * b = a * (u * b) := by group
      _ = a * (b * u) := by rw [← hcen b hb]
      _ = (a * b) * u := by group
      _ = u * (a * b) := hcen (a * b) hab

theorem det_tw_mid {K : Subgroup G} {u i j : G} (hQ : Q8Data K u i j) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) : b * a⁻¹ * b = a⁻¹ ∨ b * a⁻¹ * b = u * a⁻¹ := by
  have hcen : ∀ x ∈ K, x * u = u * x := fun x hx => (det_tw_q8_central hQ hx).symm
  have ha' : a⁻¹ ∈ K := K.inv_mem ha
  have hbb := det_tw_sq_mem hQ hb
  rcases det_tw_comm_mod hQ ha' hb with h1 | h1
  · rw [h1, mul_assoc]
    rcases hbb with h2 | h2
    · left; rw [h2, mul_one]
    · right; rw [h2, hcen a⁻¹ ha']
  · rw [h1]
    rcases hbb with h2 | h2
    · right
      calc u * (a⁻¹ * b) * b = u * (a⁻¹ * (b * b)) := by group
        _ = u * a⁻¹ := by rw [h2, mul_one]
    · left
      calc u * (a⁻¹ * b) * b = u * (a⁻¹ * (b * b)) := by group
        _ = u * (a⁻¹ * u) := by rw [h2]
        _ = u * (u * a⁻¹) := by rw [hcen a⁻¹ ha']
        _ = (u * u) * a⁻¹ := by group
        _ = a⁻¹ := by rw [hQ.inv.sq, one_mul]

theorem det_tw_inv_mem {K : Subgroup G} {u i j : G} (hQ : Q8Data K u i j) {a : G} (ha : a ∈ K) :
    a⁻¹ = a ∨ a⁻¹ = u * a := by
  have hcen : ∀ x ∈ K, x * u = u * x := fun x hx => (det_tw_q8_central hQ hx).symm
  rcases det_tw_sq_mem hQ ha with h1 | h1
  · left; exact inv_eq_of_mul_eq_one_right h1
  · right
    apply inv_eq_of_mul_eq_one_right
    calc a * (u * a) = (a * u) * a := by group
      _ = (u * a) * a := by rw [hcen a ha]
      _ = u * (a * a) := by group
      _ = u * u := by rw [h1]
      _ = 1 := hQ.inv.sq

theorem det_tw_zpowers_sq {K : Subgroup G} {u x : G} (hu : IsUniqueInvolution K u) {hxx : x * x = u}
    (hx1 : x ∈ K) (hxu : x ∉ Subgroup.zpowers u) :
    ∀ z ∈ Subgroup.zpowers x, z = 1 ∨ z = x ∨ z = u ∨ z = u * x := by
  have hord : orderOf x = 4 := by
    have hnot : ¬ x ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, hxx]; exact hu.ne_one
    have hfin : x ^ 2 ^ (1 + 1) = 1 := by
      show x ^ 4 = 1
      rw [show x ^ 4 = (x * x) * (x * x) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two],
        hxx, hu.sq]
    have := orderOf_eq_prime_pow hnot hfin
    simpa using this
  intro z hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hm := zpow_mod_orderOf x m
  rw [hord] at hm
  have hr0 : 0 ≤ m % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have hr4 : m % ((4 : ℕ) : ℤ) < ((4 : ℕ) : ℤ) := Int.emod_lt_of_pos _ (by norm_num)
  rw [← hm]
  generalize m % ((4 : ℕ) : ℤ) = r at hr0 hr4 ⊢
  interval_cases r
  · left; simp
  · right; left; simp
  · right; right; left
    rw [zpow_two, hxx]
  · right; right; right
    rw [show (3 : ℤ) = 2 + 1 from rfl, zpow_add, zpow_two, zpow_one, hxx]

private theorem det_geo_zmod_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
  decide

private theorem det_geo_zmod_add_add : ∀ x y : ZMod 2, x + (x + y) = y := by
  decide

private theorem det_geo_add_left_eq : ∀ a b : Fin 3 → ZMod 2, a + b = a → b = 0 := by
  decide

private theorem det_geo_add_right_eq : ∀ a b : Fin 3 → ZMod 2, a + b = b → a = 0 := by
  decide

private theorem det_geo_add_eq_zero : ∀ a b : Fin 3 → ZMod 2, a + b = 0 → a = b := by
  decide

private def det_geo_cross (a b : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

private theorem det_geo_cross_dot_left (a b : Fin 3 → ZMod 2) :
    dotProduct (det_geo_cross a b) a = 0 := by
  simp [det_geo_cross, dotProduct, Fin.sum_univ_three] <;> ring

private theorem det_geo_cross_dot_right (a b : Fin 3 → ZMod 2) :
    dotProduct (det_geo_cross a b) b = 0 := by
  simp [det_geo_cross, dotProduct, Fin.sum_univ_three] <;> ring

private theorem det_geo_cross_ne :
    ∀ a b : Fin 3 → ZMod 2, a ≠ 0 → b ≠ 0 → a ≠ b → det_geo_cross a b ≠ 0 := by
  decide

private theorem det_geo_cross_zero_mem :
    ∀ a b w : Fin 3 → ZMod 2, a ≠ 0 → b ≠ 0 → a ≠ b →
      dotProduct (det_geo_cross a b) w = 0 → w ∈ ({0, a, b, a + b} : Finset (Fin 3 → ZMod 2)) := by
  decide

private theorem det_geo_cross_zero {a b w : Fin 3 → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hw : dotProduct (det_geo_cross a b) w = 0) :
    w = 0 ∨ w = a ∨ w = b ∨ w = a + b := by
  have := det_geo_cross_zero_mem a b w ha hb hab hw
  simpa only [Finset.mem_insert, Finset.mem_singleton] using this

private theorem det_geo_dot_one_pair :
    ∀ p q : Fin 3 → ZMod 2, p ≠ 0 → q ≠ 0 → p ≠ q →
      ∃ x : Fin 3 → ZMod 2, dotProduct p x = 1 ∧ dotProduct q x = 1 := by
  decide

private theorem det_geo_phi_zero_one :
    ∀ a w : Fin 3 → ZMod 2, a ≠ 0 → w ≠ 0 → a ≠ w →
      ∃ φ : Fin 3 → ZMod 2, dotProduct φ a = 0 ∧ dotProduct φ w = 1 := by
  decide

private theorem det_geo_card_ker :
    ∀ f : Fin 3 → ZMod 2, f ≠ 0 →
      Fintype.card {v : Fin 3 → ZMod 2 // dotProduct f v = 0} = 4 := by
  decide

private theorem det_geo_card_fiber :
    ∀ p : Fin 3 → ZMod 2, p ≠ 0 →
      Fintype.card {f : Fin 3 → ZMod 2 // dotProduct f p = 1} = 4 := by
  decide

private theorem det_geo_card_nonzero :
    Fintype.card {f : Fin 3 → ZMod 2 // f ≠ 0} = 7 := by
  decide

private theorem det_geo_eq_of_zero_iff :
    ∀ f f' : Fin 3 → ZMod 2, f ≠ 0 → f' ≠ 0 →
      (∀ w : Fin 3 → ZMod 2, dotProduct f w = 0 ↔ dotProduct f' w = 0) → f = f' := by
  decide

private def det_geo_T (a φ : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  1 + Matrix.of fun r k => a r * φ k

private theorem det_geo_outer (a φ : Fin 3 → ZMod 2) :
    (Matrix.of fun r k => a r * φ k) = Matrix.replicateCol Unit a * Matrix.replicateRow Unit φ := by
  ext r k
  simp [Matrix.replicateCol, Matrix.replicateRow, Matrix.mul_apply]

private theorem det_geo_T_mulVec (a φ v : Fin 3 → ZMod 2) :
    Matrix.mulVec (det_geo_T a φ) v = v + dotProduct φ v • a := by
  unfold det_geo_T
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  funext r
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  ring

private theorem det_geo_T_det (a φ : Fin 3 → ZMod 2) (h : dotProduct φ a = 0) :
    (det_geo_T a φ).det = 1 := by
  unfold det_geo_T
  rw [det_geo_outer, Matrix.det_one_add_replicateCol_mul_replicateRow, h, add_zero]

private theorem det_geo_T_mul_self (a φ : Fin 3 → ZMod 2) (h : dotProduct φ a = 0) :
    det_geo_T a φ * det_geo_T a φ = 1 := by
  refine TL4.matrix_ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  simp only [det_geo_T_mulVec, dotProduct_add, dotProduct_smul, h, smul_zero, add_zero,
    smul_eq_mul, mul_zero]
  rw [add_assoc, TL4.vec_add_self, add_zero]

private theorem det_geo_card_le {E : Subgroup G} (S : Finset G) (hS : ∀ w ∈ S, w ∈ E) :
    S.card ≤ Nat.card E := by
  have := Set.ncard_le_ncard (fun w hw => hS w (Finset.mem_coe.mp hw) :
    (S : Set G) ⊆ (E : Set G)) (Set.toFinite _)
  rwa [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at this

private theorem det_geo_four {E : Subgroup G} (hE : Nat.card E = 4) {x y z : G}
    (hx : x ∈ E) (hy : y ∈ E) (hz : z ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hxy1 : x * y ≠ 1) (hxxy : x ≠ x * y) (hyxy : y ≠ x * y) :
    z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hz1, hzx, hzy, hzxy⟩ := hcon
  have hsub : ∀ w ∈ ({1, x, y, x * y, z} : Finset G), w ∈ E := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact hx
    · exact hy
    · exact E.mul_mem hx hy
    · exact hz
  have hcard := det_geo_card_le _ hsub
  have n1 : (1 : G) ∉ ({x, y, x * y, z} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hx1.symm, hy1.symm, hxy1.symm, fun h' => hz1 h'.symm⟩
  have n2 : x ∉ ({y, x * y, z} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hxy, hxxy, fun h' => hzx h'.symm⟩
  have n3 : y ∉ ({x * y, z} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hyxy, fun h' => hzy h'.symm⟩
  have n4 : x * y ∉ ({z} : Finset G) := by
    simp only [Finset.mem_singleton]
    exact fun h' => hzxy h'.symm
  have h5 : ({1, x, y, x * y, z} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_insert_of_notMem n4, Finset.card_singleton]
  omega

private theorem det_geo_mem_zpowers {K : Subgroup G} {z x : G} (hz : IsUniqueInvolution K z)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  have hxK : x ∈ K := (Subgroup.zpowers_le.mpr hz.mem) hx
  have hxx : x * x = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← _root_.zpow_add, show k + k = 2 * k by ring, _root_.zpow_mul, zpow_two, hz.sq,
      _root_.one_zpow]
  exact hz.unique x hxK hxx

private theorem det_geo_conjSub_eq_of_mem {H : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) : conjSub n H = H := by
  ext x
  rw [mem_conjSub_iff]
  have h1 := Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (H : Set G)).inv_mem hn) x
  rw [inv_inv] at h1
  exact h1.symm

private theorem det_geo_mem_normalizer_of_conjSub_eq {H : Subgroup G} {n : G}
    (hn : conjSub n H = H) : n ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h2 : conjSub n⁻¹ H = H := by
    calc conjSub n⁻¹ H = conjSub n⁻¹ (conjSub n H) := by rw [hn]
      _ = H := conjSub_inv_conjSub n H
  have h3 := mem_conjSub_iff (n := n⁻¹) (K := H) (x := y)
  rw [h2, inv_inv] at h3
  exact h3

private theorem det_geo_card_conjSub (H : Subgroup G) (g : G) :
    Nat.card (conjSub g H) = Nat.card H := by
  unfold conjSub
  rw [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))]

section Coord

variable {Ω : Set (Subgroup G)} {e : Fin 3 → G}

private theorem det_geo_conj_coord (hN : (zGroup Ω).Normal) (he : TL4.E8Basis (zGroup Ω) e)
    (g : G) (v : Fin 3 → ZMod 2) :
    g * TL4.e8Coord e v * g⁻¹ = TL4.e8Coord e (Matrix.mulVec (TL4.conjMat he g) v) :=
  TL4.conj_e8Coord he (fun y hy => hN.conj_mem y hy g) v

private theorem det_geo_ext (he : TL4.E8Basis (zGroup Ω) e) {H H' : Subgroup G}
    (hH : H ≤ zGroup Ω) (hH' : H' ≤ zGroup Ω)
    (hiff : ∀ w : Fin 3 → ZMod 2, TL4.e8Coord e w ∈ H ↔ TL4.e8Coord e w ∈ H') : H = H' := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, rfl⟩ := TL4.exists_e8Coord_eq he (hH hx)
    exact (hiff w).mp hx
  · intro hx
    obtain ⟨w, rfl⟩ := TL4.exists_e8Coord_eq he (hH' hx)
    exact (hiff w).mpr hx

private theorem det_geo_not_mem_iff (hN : (zGroup Ω).Normal) {H : Subgroup G}
    (hH : H ≤ zGroup Ω) {g y : G} (hy : y ∉ zGroup Ω) : y ∈ H ↔ g * y * g⁻¹ ∈ H := by
  constructor
  · intro hyH
    exact absurd (hH hyH) hy
  · intro hgy
    exfalso
    apply hy
    have hc := hN.conj_mem _ (hH hgy) g⁻¹
    have e' : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e'] at hc

private theorem det_geo_normalizer_of_centralizes (hN : (zGroup Ω).Normal) {H : Subgroup G}
    (hH : H ≤ zGroup Ω) {g : G} (hg : ∀ y ∈ zGroup Ω, g * y * g⁻¹ = y) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ zGroup Ω
  · rw [hg y hy]
  · exact det_geo_not_mem_iff hN hH hy

private theorem det_geo_norm (hN : (zGroup Ω).Normal) (he : TL4.E8Basis (zGroup Ω) e)
    {H : Subgroup G} (hH : H ≤ zGroup Ω) {f : Fin 3 → ZMod 2}
    (hf : ∀ w : Fin 3 → ZMod 2, TL4.e8Coord e w ∈ H ↔ dotProduct f w = 0)
    {M : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hM : ∀ v : Fin 3 → ZMod 2, dotProduct f (Matrix.mulVec M v) = 0 ↔ dotProduct f v = 0)
    {g : G} (hg : TL4.conjMat he g = M) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ zGroup Ω
  · obtain ⟨w, rfl⟩ := TL4.exists_e8Coord_eq he hy
    rw [det_geo_conj_coord hN he g w, hg, hf w, hf (Matrix.mulVec M w), hM w]
  · exact det_geo_not_mem_iff hN hH hy

private theorem det_geo_conjSub_le (hN : (zGroup Ω).Normal) {H : Subgroup G}
    (hH : H ≤ zGroup Ω) (g : G) : conjSub g H ≤ zGroup Ω := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have hc := hN.conj_mem _ (hH hx) g
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hc

private theorem det_geo_coord_ne_one (he : TL4.E8Basis (zGroup Ω) e) {w : Fin 3 → ZMod 2} :
    TL4.e8Coord e w ≠ 1 ↔ w ≠ 0 := by
  constructor
  · intro h1 h0
    exact h1 (by rw [h0, TL4.e8Coord_zero])
  · intro h0 h1
    exact h0 (TL4.e8Coord_injective he (by rw [h1, TL4.e8Coord_zero]))

private theorem det_geo_hyp_fun (he : TL4.E8Basis (zGroup Ω) e) {H : Subgroup G}
    (hH : IsHyp Ω H) :
    ∃ f : Fin 3 → ZMod 2, f ≠ 0 ∧
      ∀ w : Fin 3 → ZMod 2, TL4.e8Coord e w ∈ H ↔ dotProduct f w = 0 := by
  classical
  obtain ⟨x, hxH, hx1⟩ := TL4.exists_mem_not_mem (E := H) ({1} : Finset G)
    (by rw [hH.2]; simp)
  obtain ⟨y, hyH, hy⟩ := TL4.exists_mem_not_mem (E := H) ({1, x} : Finset G)
    (by rw [hH.2]; exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
  simp only [Finset.mem_singleton] at hx1
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hy1, hyx⟩ := hy
  obtain ⟨a, ha⟩ := TL4.exists_e8Coord_eq he (hH.1 hxH)
  obtain ⟨b, hb⟩ := TL4.exists_e8Coord_eq he (hH.1 hyH)
  have ha0 : a ≠ 0 := fun h0 => hx1 (by rw [← ha, h0, TL4.e8Coord_zero])
  have hb0 : b ≠ 0 := fun h0 => hy1 (by rw [← hb, h0, TL4.e8Coord_zero])
  have hab : a ≠ b := fun h0 => hyx (by rw [← ha, ← hb, h0])
  have hxy : x * y = TL4.e8Coord e (a + b) := by
    rw [TL4.e8Coord_add he, ha, hb]
  have hxy1 : x * y ≠ 1 := by
    intro h1
    have h2 : TL4.e8Coord e (a + b) = TL4.e8Coord e 0 := by
      rw [TL4.e8Coord_zero, ← hxy]
      exact h1
    exact hab (det_geo_add_eq_zero a b (TL4.e8Coord_injective he h2))
  have hxxy : x ≠ x * y := by
    intro h1
    have h2 : TL4.e8Coord e a = TL4.e8Coord e (a + b) := by
      rw [ha, ← hxy]
      exact h1
    exact hb0 (det_geo_add_left_eq a b (TL4.e8Coord_injective he h2).symm)
  have hyxy : y ≠ x * y := by
    intro h1
    have h2 : TL4.e8Coord e b = TL4.e8Coord e (a + b) := by
      rw [hb, ← hxy]
      exact h1
    exact ha0 (det_geo_add_right_eq a b (TL4.e8Coord_injective he h2).symm)
  refine ⟨det_geo_cross a b, det_geo_cross_ne a b ha0 hb0 hab,
    fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rcases det_geo_four hH.2 hxH hyH hw hx1 hy1 (fun h' => hyx h'.symm) hxy1 hxxy hyxy
      with h1 | h1 | h1 | h1
    · have h0 : w = 0 := TL4.e8Coord_injective he (by rw [h1, TL4.e8Coord_zero])
      rw [h0, dotProduct_zero]
    · have h0 : w = a := TL4.e8Coord_injective he (by rw [h1, ha])
      rw [h0]
      exact det_geo_cross_dot_left a b
    · have h0 : w = b := TL4.e8Coord_injective he (by rw [h1, hb])
      rw [h0]
      exact det_geo_cross_dot_right a b
    · have h0 : w = a + b := TL4.e8Coord_injective he (by rw [h1, hxy])
      rw [h0, dotProduct_add, det_geo_cross_dot_left, det_geo_cross_dot_right, add_zero]
  · rcases det_geo_cross_zero ha0 hb0 hab hw with h0 | h0 | h0 | h0
    · rw [h0, TL4.e8Coord_zero]
      exact H.one_mem
    · rw [h0, ha]
      exact hxH
    · rw [h0, hb]
      exact hyH
    · rw [h0, TL4.e8Coord_add he, ha, hb]
      exact H.mul_mem hxH hyH

private theorem det_geo_hyp_construct (he : TL4.E8Basis (zGroup Ω) e) {f : Fin 3 → ZMod 2}
    (hf : f ≠ 0) : ∃ H : Subgroup G, IsHyp Ω H ∧
      ∀ w : Fin 3 → ZMod 2, TL4.e8Coord e w ∈ H ↔ dotProduct f w = 0 := by
  classical
  let H : Subgroup G :=
    { carrier := {x | ∃ w : Fin 3 → ZMod 2, TL4.e8Coord e w = x ∧ dotProduct f w = 0}
      mul_mem' := by
        rintro _ _ ⟨v, rfl, hv⟩ ⟨w, rfl, hw⟩
        exact ⟨v + w, TL4.e8Coord_add he v w, by rw [dotProduct_add, hv, hw, add_zero]⟩
      one_mem' := ⟨0, TL4.e8Coord_zero, by rw [dotProduct_zero]⟩
      inv_mem' := by
        rintro _ ⟨v, rfl, hv⟩
        refine ⟨v, ?_, hv⟩
        have hsq : TL4.e8Coord e v * TL4.e8Coord e v = 1 := by
          rw [← TL4.e8Coord_add he, TL4.vec_add_self, TL4.e8Coord_zero]
        exact (inv_eq_of_mul_eq_one_right hsq).symm }
  have hmem : ∀ w : Fin 3 → ZMod 2, TL4.e8Coord e w ∈ H ↔ dotProduct f w = 0 := by
    intro w
    constructor
    · rintro ⟨v, hv, hfv⟩
      rw [← TL4.e8Coord_injective he hv]
      exact hfv
    · intro hw
      exact ⟨w, rfl, hw⟩
  refine ⟨H, ⟨?_, ?_⟩, hmem⟩
  · rintro _ ⟨v, rfl, _⟩
    exact TL4.e8Coord_mem he v
  · let φ : {v : Fin 3 → ZMod 2 // dotProduct f v = 0} → H := fun v =>
      ⟨TL4.e8Coord e v.1, v.1, rfl, v.2⟩
    have hφ : Function.Bijective φ := by
      refine ⟨fun v v' hvv' => Subtype.ext (TL4.e8Coord_injective he (congrArg Subtype.val hvv')),
        fun x => ?_⟩
      obtain ⟨w, hw, hfw⟩ := x.2
      exact ⟨⟨w, hfw⟩, Subtype.ext hw⟩
    rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card,
      det_geo_card_ker f hf]

end Coord

namespace DEHyp

variable {Ω : Set (Subgroup G)} (h : DEHyp Ω)
include h

theorem det_tw_basis {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) :
    ∃ e : Fin 3 → G, TL4.E8Basis (zGroup Ω) e ∧ e 0 = u := by
  classical
  obtain ⟨b, hb, hb1⟩ := TL4.exists_mem_not_mem (E := zGroup Ω) ({1, u} : Finset G)
    (lt_of_le_of_lt Finset.card_le_two (by rw [h.card_zGroup]; norm_num))
  obtain ⟨c, hc, hc1⟩ := TL4.exists_mem_not_mem (E := zGroup Ω) ({1, u, b, u * b} : Finset G)
    (lt_of_le_of_lt Finset.card_le_four (by rw [h.card_zGroup]; norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb1 hc1
  refine ⟨![u, b, c], ⟨h.zGroup_mul_self, h.card_zGroup, fun k => ?_, hu1, ⟨hb1.1, hb1.2⟩,
    ⟨hc1.1, hc1.2.1, hc1.2.2.1, hc1.2.2.2⟩⟩, rfl⟩
  fin_cases k
  exacts [hu, hb, hc]

theorem det_tw_conjMat_formula {M : Subgroup G} (hM : M ∈ Ω) {c : G}
    (hMc : IsUniqueInvolution M c) {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {v : Fin 3 → ZMod 2} (hc : c = TL4.e8Coord e v) (hv : v 1 ≠ 0 ∨ v 2 ≠ 0)
    {x : G} (hxM : x ∈ M) (hx0 : x * e 0 = e 0 * x) (hxc : x ∉ Subgroup.zpowers c) :
    TL4.conjMat he x = det_tw_tau v := by
  classical
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hMc (h.isQuatSub_of_mem hM) (h.card M hM)
  have hQ : Q8Data M c i j := ⟨hMc, hi, hj, hii, hjj, hji, hNF⟩
  have hcmem : c ∈ zGroup Ω := hc ▸ TL4.e8Coord_mem he v
  have hcD : ∀ w : Fin 3 → ZMod 2, TL4.e8Coord e w ∈ zGroup Ω := fun w => TL4.e8Coord_mem he w
  have hxN : ∀ y ∈ zGroup Ω, x * y * x⁻¹ ∈ zGroup Ω := fun y hy => h.zGroup_normal.conj_mem y hy x
  have hdich : ∀ d ∈ zGroup Ω, dComm d x = 1 ∨ dComm d x = c := fun d hd =>
    det_tw_eq_one_or_of_mem_zpowers hMc.sq hMc.ne_one (h.dComm_mem_zpowers hM hMc hd hxM)
  let g : G → ZMod 2 := fun y => if y = 1 then 0 else 1
  have hg : ∀ a b : G, (a = 1 ∨ a = c) → (b = 1 ∨ b = c) → g (b * a) = g a + g b := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · simp [g]
    · simp [g, hMc.ne_one]
    · simp [g, hMc.ne_one]
    · simp [g, hMc.ne_one, hMc.sq]
      decide
  let ψ : (Fin 3 → ZMod 2) → ZMod 2 := fun w => g (dComm (TL4.e8Coord e w) x)
  have hψ0 : ψ 0 = 0 := by simp [ψ, g, TL4.e8Coord_zero, dComm]
  have hadd : ∀ w1 w2, ψ (w1 + w2) = ψ w1 + ψ w2 := by
    intro w1 w2
    have hdc : dComm (TL4.e8Coord e (w1 + w2)) x =
        dComm (TL4.e8Coord e w2) x * dComm (TL4.e8Coord e w1) x := by
      rw [TL4.e8Coord_add he]
      exact dComm_mul_left hMc (h.dNorm M hM (hcD w1)) (hdich _ (hcD w2))
    simp only [ψ]
    rw [hdc]
    exact hg _ _ (hdich _ (hcD w1)) (hdich _ (hcD w2))
  have hsing : ∀ (a : ZMod 2) (k : Fin 3), ψ (a • Pi.single k 1) = a * ψ (Pi.single k 1) := by
    intro a k
    rcases TL4.zmod_two_cases a with rfl | rfl
    · simp [hψ0]
    · simp
  have hψe0 : ψ (Pi.single 0 1) = 0 := by
    have h1 : dComm (TL4.e8Coord e (Pi.single 0 1)) x = 1 := by
      rw [TL4.e8Coord_single, dComm_eq_one_iff]
      exact hx0.symm
    simp [ψ, h1, g]
  have hψv : ψ v = 0 := by
    have h1 : dComm (TL4.e8Coord e v) x = 1 := by
      rw [← hc, dComm_eq_one_iff]
      exact det_tw_q8_central hQ hxM
    simp [ψ, h1, g]
  have hψne : ∃ w, ψ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hxC : x ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
      obtain ⟨w, rfl⟩ := TL4.exists_e8Coord_eq he hd
      have h1 : g (dComm (TL4.e8Coord e w) x) = 0 := hcon w
      have h2 : dComm (TL4.e8Coord e w) x = 1 := by
        by_contra hne
        simp [g, hne] at h1
      rw [dComm_eq_one_iff] at h2
      exact h2
    have hmem : x ∈ M ⊓ Subgroup.centralizer (zGroup Ω : Set G) := ⟨hxM, hxC⟩
    rw [h.inf_centralizer_zGroup hM hMc] at hmem
    exact hxc hmem
  have hformula : ∀ w : Fin 3 → ZMod 2,
      ψ w = ψ (Pi.single 1 1) * w 1 + ψ (Pi.single 2 1) * w 2 := by
    intro w
    have hdecomp : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 + w 2 • Pi.single 2 1 := by
      funext k
      fin_cases k <;> simp
    conv_lhs => rw [hdecomp]
    rw [hadd, hadd, hsing, hsing, hsing, hψe0]
    ring
  have hω : ψ (Pi.single 1 1) ≠ 0 ∨ ψ (Pi.single 2 1) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨w, hw⟩ := hψne
    exact hw (by rw [hformula w, hcon.1, hcon.2]; ring)
  have hψv' := hformula v
  rw [hψv, eq_comm] at hψv'
  have hfin : ∀ a b p q : ZMod 2, (a ≠ 0 ∨ b ≠ 0) → p * a + q * b = 0 →
      (p ≠ 0 ∨ q ≠ 0) → p = b ∧ q = a := by decide
  obtain ⟨hp, hq⟩ := hfin (v 1) (v 2) _ _ hv hψv' hω
  have hψform : ∀ w : Fin 3 → ZMod 2, ψ w = v 2 * w 1 + v 1 * w 2 := by
    intro w
    rw [hformula w, hp, hq]
  have hconj : ∀ w : Fin 3 → ZMod 2,
      x * TL4.e8Coord e w * x⁻¹ = TL4.e8Coord e (w + ψ w • v) := by
    intro w
    have hxd : x * TL4.e8Coord e w * x⁻¹ = (dComm (TL4.e8Coord e w) x)⁻¹ * TL4.e8Coord e w := by
      unfold dComm; group
    rcases hdich _ (hcD w) with h1 | h1
    · have h0 : ψ w = 0 := by simp [ψ, h1, g]
      rw [hxd, h1, inv_one, one_mul, h0, zero_smul, add_zero]
    · have h0 : ψ w = 1 := by
        have hne : ψ w ≠ 0 := by
          intro h0
          have h2 : dComm (TL4.e8Coord e w) x = 1 := by
            by_contra hne'
            simp [ψ, g, hne'] at h0
          rw [h1] at h2
          exact hMc.ne_one (hc ▸ h2)
        revert hne
        generalize ψ w = a
        revert a
        decide
      rw [hxd, h1, inv_eq_of_mul_eq_one_right hMc.sq, h0, one_smul, TL4.e8Coord_add he, hc]
      exact h.zGroup_comm _ (hcD v) _ (hcD w)
  apply TL4.matrix_ext_mulVec
  intro w
  rw [det_tw_tau_mulVec]
  apply TL4.e8Coord_injective he
  rw [← TL4.conj_e8Coord he hxN w, hconj w, hψform w]

open scoped commutatorElement in
theorem commutes_of_mem_twinSet {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ twinSet Ω K)
    (hne : J ≠ K) : Commutes K J := by
  obtain ⟨hJΩ, z, hz, hzJ⟩ := hJ
  have hzKJ : z ∈ K ⊓ J := ⟨hz.mem, hzJ.mem⟩
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
    have h2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    have := Subgroup.orderOf_dvd_natCard (K ⊓ J) hzKJ
    rwa [h2] at this
  have hv1 : 1 ≤ padicValNat 2 (Nat.card ↥(K ⊓ J)) :=
    one_le_padicValNat_of_dvd (Nat.card_pos.ne') hdvd
  obtain ⟨h41, h42⟩ := h.hyp.omega4 K hK J hJΩ hne.symm
  have hval : padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 := le_antisymm h41 hv1
  have hcomm := h42 hval
  rw [TL4.oddCoreOf_eq_bot_of_isPGroup (h.two K hK),
    TL4.oddCoreOf_eq_bot_of_isPGroup (h.two J hJΩ), inf_idem] at hcomm
  intro x hx y hy
  have hxy : ⁅x, y⁆ ∈ (⊥ : Subgroup G) :=
    hcomm (Subgroup.commutator_mem_commutator hx hy)
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hxy)

theorem inf_eq_zpowers_of_mem_twinSet {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ twinSet Ω K)
    (hne : J ≠ K) {z : G} (hz : IsUniqueInvolution K z) : K ⊓ J = Subgroup.zpowers z := by
  obtain ⟨hJΩ, z', hz', hzJ⟩ := hJ
  have hzz : z = z' := hz.eq hz'
  subst hzz
  have hle : Subgroup.zpowers z ≤ K ⊓ J := Subgroup.zpowers_le.mpr ⟨hz.mem, hzJ.mem⟩
  have hcard2 : Nat.card (Subgroup.zpowers z) = 2 := card_zpowers_of_involution hz.sq hz.ne_one
  have hcardle : Nat.card ↥(K ⊓ J) ≤ 2 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp ((h.two K hK).to_le inf_le_left)
    have hle' := (h.hyp.omega4 K hK J hJΩ hne.symm).1
    rw [hn, padicValNat.prime_pow] at hle'
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle'
      _ = 2 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem det_tw_mem_twinSet_conjSub {K J : Subgroup G} (g : G) :
    conjSub g J ∈ twinSet Ω (conjSub g K) ↔ J ∈ twinSet Ω K := by
  have hconj : ∀ n : G, ∀ L ∈ Ω, conjSub n L ∈ Ω := fun n L hL => h.hyp.conjInvariant n L hL
  constructor
  · rintro ⟨hJΩ, z, hz, hzJ⟩
    refine ⟨?_, g⁻¹ * z * g, det_tw_isUniqueInvolution_conjSub_iff.mp hz,
      det_tw_isUniqueInvolution_conjSub_iff.mp hzJ⟩
    have := hconj g⁻¹ _ hJΩ
    rwa [conjSub_inv_conjSub] at this
  · rintro ⟨hJΩ, z, hz, hzJ⟩
    exact ⟨hconj g J hJΩ, g * z * g⁻¹, hz.conj g, hzJ.conj g⟩

theorem det_tw_image_twinSet (g : G) (K : Subgroup G) :
    conjSub g '' twinSet Ω K = twinSet Ω (conjSub g K) := by
  ext L
  constructor
  · rintro ⟨J, hJ, rfl⟩
    exact (det_tw_mem_twinSet_conjSub (h := h) g).mpr hJ
  · intro hL
    have hL' : conjSub g (conjSub g⁻¹ L) ∈ twinSet Ω (conjSub g K) := by
      rwa [conjSub_conjSub_inv]
    exact ⟨conjSub g⁻¹ L, (det_tw_mem_twinSet_conjSub (h := h) g).mp hL',
      conjSub_conjSub_inv g L⟩

theorem twinSet_ncard_eq {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) :
    (twinSet Ω K).ncard = (twinSet Ω L).ncard := by
  obtain ⟨g, rfl⟩ := h.trans K hK L hL
  rw [← det_tw_image_twinSet h g K, Set.ncard_image_of_injective _ (conjSub_injective g)]

theorem ncard_eq_seven_mul {K : Subgroup G} (hK : K ∈ Ω) :
    Ω.ncard = 7 * (twinSet Ω K).ncard := by
  classical
  let inv : Subgroup G → G :=
    fun L => if hL : ∃ z : G, IsUniqueInvolution L z then hL.choose else 1
  have inv_spec : ∀ L ∈ Ω, IsUniqueInvolution L (inv L) := by
    intro L hL
    have hex := h.exists_isUniqueInvolution hL
    simp only [inv, dif_pos hex]
    exact hex.choose_spec
  let T : Finset G := (Set.toFinite {x : G | x ∈ zGroup Ω ∧ x ≠ 1}).toFinset
  have hT : T.card = 7 := by
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _), ← Nat.card_coe_set_eq,
      ← h.card_zGroup_ne_one]
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h1 => x.2.2 (congrArg Subtype.val h1)⟩
      invFun := fun x => ⟨x.1.1, x.1.2, fun h1 => x.2 (Subtype.ext h1)⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have hmaps : ∀ L ∈ (Set.toFinite Ω).toFinset, inv L ∈ T := by
    intro L hL
    rw [Set.Finite.mem_toFinset] at hL
    have hspec := inv_spec L hL
    refine (Set.Finite.mem_toFinset _).mpr ⟨Subgroup.subset_closure ⟨L, hL, hspec⟩, hspec.ne_one⟩
  have hfib : ∀ x ∈ T, ((Set.toFinite Ω).toFinset.filter (fun L => inv L = x)).card =
      (twinSet Ω K).ncard := by
    intro x hx
    have hxD : x ∈ {x : G | x ∈ zGroup Ω ∧ x ≠ 1} := (Set.Finite.mem_toFinset _).mp hx
    obtain ⟨hxD1, hxD2⟩ := hxD
    obtain ⟨L₀, hL₀, hx₀⟩ : ∃ L₀ ∈ Ω, IsUniqueInvolution L₀ x := by
      rcases (h.mem_zGroup_iff).mp hxD1 with h1 | h1
      · exact absurd h1 hxD2
      · exact h1
    have hset : {L | L ∈ Ω ∧ inv L = x} = twinSet Ω L₀ := by
      ext L
      constructor
      · rintro ⟨hLΩ, hLx⟩
        exact ⟨hLΩ, x, hx₀, hLx ▸ inv_spec L hLΩ⟩
      · rintro ⟨hLΩ, z, hz₀, hzL⟩
        have hzx : x = z := hx₀.eq hz₀
        exact ⟨hLΩ, by rw [(inv_spec L hLΩ).eq hzL, hzx]⟩
    rw [← Set.ncard_coe_finset]
    have hcoe : ((Set.toFinite Ω).toFinset.filter (fun L => inv L = x) : Set (Subgroup G)) =
        {L | L ∈ Ω ∧ inv L = x} := by
      ext L
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [hcoe, hset]
    exact (h.twinSet_ncard_eq hK hL₀).symm
  rw [Set.ncard_eq_toFinset_card Ω (Set.toFinite Ω),
    Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_const, hT,
    smul_eq_mul]

theorem exists_swap_of_mem_twinSet {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ twinSet Ω K) {u : G}
    (hu : IsUniqueInvolution K u) :
    ∃ g ∈ Subgroup.centralizer ({u} : Set G), conjSub g K = J := by
  obtain ⟨g, hg⟩ := h.trans K hK J hJ.1
  refine ⟨g, ?_, hg⟩
  obtain ⟨_, z, hz, hzJ⟩ := hJ
  have hzu : u = z := hu.eq hz
  have hJu : IsUniqueInvolution J u := by rw [hzu]; exact hzJ
  have hc := hu.conj g
  rw [hg] at hc
  have hgu : g * u * g⁻¹ = u := hc.eq hJu
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * u = (g * u * g⁻¹) * g := by group
    _ = u * g := by rw [hgu]

theorem det_tw_core {M : Subgroup G} (hM : M ∈ Ω) {v u : G} (hv : IsUniqueInvolution M v)
    (hu : u ∈ zGroup Ω) (huv : u ∉ Subgroup.zpowers v) :
    Nat.card ↥(M ⊓ Subgroup.centralizer ({u} : Set G)) = 4 ∧
      IsCyclic ↥(M ⊓ Subgroup.centralizer ({u} : Set G)) ∧
      ∀ J ∈ Ω, J ≠ M → IsUniqueInvolution J u →
        M ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hv (h.isQuatSub_of_mem hM) (h.card M hM)
  have hQ : Q8Data M v i j := ⟨hv, hi, hj, hii, hjj, hji, hNF⟩
  have hvZ : Subgroup.zpowers v ≤ zGroup Ω :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨M, hM, hv⟩)
  have hv1 : v ≠ 1 := hv.ne_one
  have hvv : v * v = 1 := hv.sq
  have hdN : u ∈ Subgroup.normalizer (M : Set G) := h.dNorm M hM hu
  have h1k : ∀ k : G, dComm 1 k = 1 := fun k => by unfold dComm; group
  let f : M →* Subgroup.zpowers v :=
    MonoidHom.mk' (fun m => ⟨dComm u (m : G), h.dComm_mem_zpowers hM hv hu m.2⟩) (by
      intro m1 m2
      apply Subtype.ext
      have hc : dComm u (m2 : G) = 1 ∨ dComm u (m2 : G) = v :=
        det_tw_eq_one_or_of_mem_zpowers hvv hv1 (h.dComm_mem_zpowers hM hv hu m2.2)
      exact dComm_mul_right hv m1.2 m2.2 hdN hc)
  have hex : ∃ m ∈ M, dComm u m ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hd := h.eq_of_dComm_eq hM hv hu (Subgroup.one_mem _)
      (fun k hk => (hcon k hk).trans (h1k k).symm)
    exact huv (by simpa using hd)
  obtain ⟨m, hmM, hmne⟩ := hex
  have hmv : dComm u m = v :=
    (det_tw_eq_one_or_of_mem_zpowers hvv hv1 (h.dComm_mem_zpowers hM hv hu hmM)).resolve_left
      hmne
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rcases det_tw_eq_one_or_of_mem_zpowers hvv hv1 hy with h1 | h1
    · exact ⟨1, Subtype.ext (by simp [f, h1, dComm])⟩
    · exact ⟨⟨m, hmM⟩, Subtype.ext (by simp [f, hmv, h1])⟩
  have hker : Nat.card f.ker * 2 = 8 := by
    have h8 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hfsurj, Subgroup.card_top,
      card_zpowers_of_involution hvv hv1, h.card M hM] at h8
    exact h8
  have hmap : f.ker.map M.subtype = M ⊓ Subgroup.centralizer ({u} : Set G) := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hm' : f m = 1 := hm
      have hd : dComm u (m : G) = 1 := by
        have := congrArg Subtype.val hm'
        simpa [f] using this
      exact ⟨m.2, Subgroup.mem_centralizer_singleton_iff.mpr (dComm_eq_one_iff.mp hd).symm⟩
    · rintro ⟨hxM, hxc⟩
      refine ⟨⟨x, hxM⟩, ?_, rfl⟩
      show f ⟨x, hxM⟩ = 1
      apply Subtype.ext
      show dComm u x = 1
      rw [dComm_eq_one_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
  have hU4 : Nat.card ↥(M ⊓ Subgroup.centralizer ({u} : Set G)) = 4 := by
    rw [← hmap, Subgroup.card_map_of_injective (f := M.subtype) Subtype.val_injective]
    omega
  refine ⟨hU4, ?_, ?_⟩
  ·
    have hnot : ¬ (M ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.zpowers v) := fun hle => by
      have hc := Subgroup.card_le_of_le hle
      rw [hU4, card_zpowers_of_involution hvv hv1] at hc
      omega
    obtain ⟨x, hxU, hxv⟩ : ∃ x ∈ M ⊓ Subgroup.centralizer ({u} : Set G),
        x ∉ Subgroup.zpowers v := by
      by_contra hcon
      push_neg at hcon
      exact hnot hcon
    have hxM : x ∈ M := hxU.1
    have hxx : x * x = v := det_tw_q8_sq hQ hxM hxv
    have hord : orderOf x = 4 := by
      have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x)
        (by rw [pow_one, pow_two, hxx]; exact hv1)
        (by
          show x ^ 4 = 1
          rw [show x ^ 4 = (x * x) * (x * x) by
            rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two],
            hxx, hvv])
      simpa using this
    have hle : Subgroup.zpowers x ≤ M ⊓ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.zpowers_le.mpr hxU
    have heq : Subgroup.zpowers x = M ⊓ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hU4, Nat.card_zpowers, hord])
    rw [← heq]
    infer_instance
  · intro J hJ hJM hJu y hy
    have hyM : y ∈ M := hy.1
    have hyc : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    by_cases hyv : y ∈ Subgroup.zpowers v
    · exact h.dNorm J hJ (hvZ hyv)
    · obtain ⟨w, hw, hne⟩ := det_tw_q8_noncomm hQ hyM hyv
      have hpg : IsPGroup 2 (Subgroup.zpowers y) :=
        (h.two M hM).to_le (Subgroup.zpowers_le.mpr hyM)
      exact h.hyp.omega5 J hJ M hM hJM u hJu y hyM (fun hall => hne (hall w hw)) hpg hyc

theorem card_inf_centralizer_of_not_mem_twinSet {K M : Subgroup G} (hK : K ∈ Ω) (hM : M ∈ Ω)
    (hnot : M ∉ twinSet Ω K) {u : G} (hu : IsUniqueInvolution K u) :
    Nat.card ↥(M ⊓ Subgroup.centralizer ({u} : Set G)) = 4 ∧
      IsCyclic ↥(M ⊓ Subgroup.centralizer ({u} : Set G)) ∧
      ∀ J ∈ twinSet Ω K,
        M ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨v, hv⟩ := h.exists_isUniqueInvolution hM
  have huv : u ∉ Subgroup.zpowers v := by
    intro hmem
    have huv' : u = v :=
      (det_tw_eq_one_or_of_mem_zpowers hv.sq hv.ne_one hmem).resolve_left hu.ne_one
    exact hnot ⟨hM, u, hu, huv' ▸ hv⟩
  have hzu : u ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hu⟩
  obtain ⟨hU4, hcyc, hnorm⟩ := h.det_tw_core hM hv hzu huv
  refine ⟨hU4, hcyc, ?_⟩
  rintro J ⟨hJΩ, z, hz, hzJ⟩
  have hzu' : u = z := hu.eq hz
  have hJu : IsUniqueInvolution J u := by rw [hzu']; exact hzJ
  have hJM : J ≠ M := by
    intro hJM
    subst hJM
    exact hnot ⟨hJΩ, z, hz, hzJ⟩
  exact hnorm J hJΩ hJM hJu

theorem det_tw_exists_tau {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u)
    {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) (he0 : e 0 = u)
    {v : Fin 3 → ZMod 2} (hv0 : v ≠ 0) (hv1 : v ≠ ![1, 0, 0]) :
    ∃ n ∈ Subgroup.normalizer (K : Set G), TL4.conjMat he n = det_tw_tau v := by
  classical
  have hv' : v 1 ≠ 0 ∨ v 2 ≠ 0 := by
    have key : ∀ w : Fin 3 → ZMod 2, w ≠ 0 → w ≠ ![1, 0, 0] → w 1 ≠ 0 ∨ w 2 ≠ 0 := by
      decide
    exact key v hv0 hv1
  have hcD : TL4.e8Coord e v ∈ zGroup Ω := TL4.e8Coord_mem he v
  have hc1 : TL4.e8Coord e v ≠ 1 := by
    intro h1
    apply hv0
    apply TL4.e8Coord_injective he
    rw [h1, TL4.e8Coord_zero]
  have hE0 : TL4.e8Coord e ![1, 0, 0] = u := by
    rw [show (![1, 0, 0] : Fin 3 → ZMod 2) = Pi.single 0 1 from by
      funext k; fin_cases k <;> simp, TL4.e8Coord_single, he0]
  have hcu : TL4.e8Coord e v ≠ u := by
    intro h1
    apply hv1
    apply TL4.e8Coord_injective he
    rw [hE0, h1]
  obtain ⟨M, hM, hMc⟩ : ∃ M ∈ Ω, IsUniqueInvolution M (TL4.e8Coord e v) := by
    rcases (h.mem_zGroup_iff).mp hcD with h1 | h1
    · exact absurd h1 hc1
    · exact h1
  have hMnot : M ∉ twinSet Ω K := by
    rintro ⟨_, z, hz, hzM⟩
    have hzu : u = z := hu.eq hz
    rw [← hzu] at hzM
    exact hcu (hMc.eq hzM)
  obtain ⟨hU4, _, hnorm⟩ := h.card_inf_centralizer_of_not_mem_twinSet hK hM hMnot hu
  have hnot : ¬ (M ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.zpowers (TL4.e8Coord e v)) := fun hle => by
    have hc := Subgroup.card_le_of_le hle
    rw [hU4, card_zpowers_of_involution hMc.sq hc1] at hc
    omega
  obtain ⟨x, hxU, hxc⟩ : ∃ x ∈ M ⊓ Subgroup.centralizer ({u} : Set G),
      x ∉ Subgroup.zpowers (TL4.e8Coord e v) := by
    by_contra hcon
    push_neg at hcon
    exact hnot hcon
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxU.2
  refine ⟨x, hnorm K ⟨hK, u, hu, hu⟩ hxU, ?_⟩
  exact det_tw_conjMat_formula h hM hMc he rfl hv' hxU.1 (by rw [he0]; exact hxu) hxc

theorem det_tw_stab {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u)
    {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) (he0 : e 0 = u) :
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det ≠ 0 → A.mulVec ![1, 0, 0] = ![1, 0, 0] →
      ∃ n ∈ Subgroup.normalizer (K : Set G), TL4.conjMat he n = A := by
  have hxN : ∀ g : G, ∀ y ∈ zGroup Ω, g * y * g⁻¹ ∈ zGroup Ω :=
    fun g y hy => h.zGroup_normal.conj_mem y hy g
  have htau : ∀ a : Fin 3 → ZMod 2, ∃ n ∈ Subgroup.normalizer (K : Set G),
      TL4.conjMat he n = det_tw_tau a := by
    intro a
    by_cases ha0 : a = 0
    · subst ha0
      exact ⟨1, Subgroup.one_mem _, (TL4.conjMat_one he).trans (by decide)⟩
    by_cases ha1 : a = ![1, 0, 0]
    · subst ha1
      exact ⟨1, Subgroup.one_mem _, (TL4.conjMat_one he).trans (by decide)⟩
    exact h.det_tw_exists_tau hK hu he he0 ha0 ha1
  have hstab : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det ≠ 0 →
      A.mulVec ![1, 0, 0] = ![1, 0, 0] →
      ∃ n ∈ Subgroup.normalizer (K : Set G), TL4.conjMat he n = A := by
    intro A hA hA0
    obtain ⟨a, b, c, rfl⟩ := det_tw_finite A hA hA0
    obtain ⟨na, hna, hna'⟩ := htau a
    obtain ⟨nb, hnb, hnb'⟩ := htau b
    obtain ⟨nc, hnc, hnc'⟩ := htau c
    refine ⟨na * nb * nc, mul_mem (mul_mem hna hnb) hnc, ?_⟩
    rw [TL4.conjMat_mul he (hxN _) (hxN _), TL4.conjMat_mul he (hxN _) (hxN _), hna', hnb', hnc']
  exact hstab

theorem centralizer_eq_sup {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u) :
    Subgroup.centralizer ({u} : Set G) =
      Subgroup.normalizer (K : Set G) ⊔ Subgroup.centralizer (zGroup Ω : Set G) := by
  have huD : u ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hu⟩
  obtain ⟨e, he, he0⟩ := det_tw_basis h huD hu.ne_one
  have hE0 : TL4.e8Coord e ![1, 0, 0] = u := by
    rw [show (![1, 0, 0] : Fin 3 → ZMod 2) = Pi.single 0 1 from by
      funext k; fin_cases k <;> simp, TL4.e8Coord_single, he0]
  have hxN : ∀ g : G, ∀ y ∈ zGroup Ω, g * y * g⁻¹ ∈ zGroup Ω :=
    fun g y hy => h.zGroup_normal.conj_mem y hy g
  have hstab := h.det_tw_stab hK hu he he0
  apply le_antisymm
  · intro g hg
    have hgu : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgu' : g * u * g⁻¹ = u := by rw [hgu]; group
    have hfix : (TL4.conjMat he g).mulVec ![1, 0, 0] = ![1, 0, 0] := by
      apply TL4.e8Coord_injective he
      rw [← TL4.conj_e8Coord he (hxN g) ![1, 0, 0], hE0, hgu']
    have hdet : (TL4.conjMat he g).det ≠ 0 := by
      rw [TL4.det_conjMat he (hxN g) (fun z hz => h.zGroup_normal.conj_mem z hz g⁻¹)]
      exact one_ne_zero
    obtain ⟨n, hn, hnr⟩ := hstab _ hdet hfix
    have hker : n⁻¹ * g ∈ (h.rhoD he).ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show TL4.conjMat he (n⁻¹ * g) = 1
      have hnn : TL4.conjMat he n⁻¹ * TL4.conjMat he n = 1 := by
        rw [← TL4.conjMat_mul he (hxN n⁻¹) (hxN n), inv_mul_cancel, TL4.conjMat_one he]
      rw [TL4.conjMat_mul he (hxN n⁻¹) (hxN g), ← hnr, hnn]
    rw [h.rhoD_ker he] at hker
    have hg' : g = n * (n⁻¹ * g) := by group
    rw [hg']
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hker)
  · refine sup_le (fun x hx => ?_) (fun g hg => ?_)
    · have hxu : x * u * x⁻¹ = u := hu.conj_eq (mem_normalizer_iff_conjSub_eq.mp hx)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hxu)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hg) u huD).symm

theorem member_le_commutator {K : Subgroup G} (hK : K ∈ Ω) :
    K ≤ commutator G := by
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  have huD : u ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hu⟩
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hu (h.isQuatSub_of_mem hK) (h.card K hK)
  have hQ : Q8Data K u i j := ⟨hu, hi, hj, hii, hjj, hji, hNF⟩
  obtain ⟨e, he, he0⟩ := det_tw_basis h huD hu.ne_one
  have hxN : ∀ g : G, ∀ y ∈ zGroup Ω, g * y * g⁻¹ ∈ zGroup Ω :=
    fun g y hy => h.zGroup_normal.conj_mem y hy g
  have hconjK : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K :=
    fun g hg k hk => (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  obtain ⟨n, hn, hnr⟩ := h.det_tw_stab hK hu he he0
    (det_tw_tau ![0, 0, 1] * det_tw_tau ![0, 1, 0]) (by decide) (by decide)
  have hA3cube : det_tw_tau ![0, 0, 1] * det_tw_tau ![0, 1, 0] *
      (det_tw_tau ![0, 0, 1] * det_tw_tau ![0, 1, 0]) *
      (det_tw_tau ![0, 0, 1] * det_tw_tau ![0, 1, 0]) = 1 := by decide
  have hA3sq : det_tw_tau ![0, 0, 1] * det_tw_tau ![0, 1, 0] *
      (det_tw_tau ![0, 0, 1] * det_tw_tau ![0, 1, 0]) ≠ 1 := by decide
  have hnn : TL4.conjMat he (n * n) = (det_tw_tau ![0, 0, 1] * det_tw_tau ![0, 1, 0]) *
      (det_tw_tau ![0, 0, 1] * det_tw_tau ![0, 1, 0]) := by
    rw [TL4.conjMat_mul he (hxN n) (hxN n), hnr]
  have hn3 : TL4.conjMat he (n * n * n) = 1 := by
    rw [TL4.conjMat_mul he (hxN (n * n)) (hxN n), hnn, hnr, hA3cube]
  have hnu : n * u * n⁻¹ = u := hu.conj_eq (mem_normalizer_iff_conjSub_eq.mp hn)
  have hnu' : n⁻¹ * u * n = u := by
    have := hu.conj_eq (mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ hn))
    rwa [inv_inv] at this
  have hconjc : ∀ c : G, (c = 1 ∨ c = u) → n * c * n⁻¹ = c := by
    rintro c (rfl | rfl)
    · group
    · exact hnu
  have hconjc' : ∀ c : G, (c = 1 ∨ c = u) → n⁻¹ * c * n = c := by
    rintro c (rfl | rfl)
    · group
    · exact hnu'
  have hkey : ∃ k₀ ∈ K, ¬ (n * k₀ * n⁻¹ = k₀ ∨ n * k₀ * n⁻¹ = u * k₀) := by
    by_contra hcon
    push_neg at hcon
    have hinv : ∀ k ∈ K, n⁻¹ * k * n = k ∨ n⁻¹ * k * n = u * k := by
      intro k hk
      have hk'' : n⁻¹ * k * n ∈ K := by
        have := hconjK n⁻¹ (Subgroup.inv_mem _ hn) k hk
        rwa [inv_inv] at this
      have hk1 : n * (n⁻¹ * k * n) * n⁻¹ = k := by group
      rcases hcon _ hk'' with h1 | h1
      · left; exact (hk1.symm.trans h1).symm
      · right
        have hk2 : k = u * (n⁻¹ * k * n) := hk1.symm.trans h1
        calc n⁻¹ * k * n = (u * u) * (n⁻¹ * k * n) := by rw [hu.sq, one_mul]
          _ = u * (u * (n⁻¹ * k * n)) := by rw [mul_assoc]
          _ = u * k := by rw [← hk2]
    have hdk : ∀ d ∈ zGroup Ω, ∀ k ∈ K, dComm d (n⁻¹ * k * n) = dComm d k := by
      intro d hd k hk
      rcases hinv k hk with h1 | h1
      · rw [h1]
      · rw [h1, dComm_mul_right hu hu.mem hk (h.dNorm K hK hd)
          (det_tw_eq_one_or_of_mem_zpowers hu.sq hu.ne_one (h.dComm_mem_zpowers hK hu hd hk)),
          dComm_z hu (h.dNorm K hK hd), one_mul]
    have hdcomm : ∀ d ∈ zGroup Ω, ∀ k ∈ K, dComm (n * d * n⁻¹) k = dComm d k := by
      intro d hd k hk
      have hid : dComm (n * d * n⁻¹) k = n * dComm d (n⁻¹ * k * n) * n⁻¹ := by
        unfold dComm; group
      rw [hid, hdk d hd k hk]
      exact hconjc _
        (det_tw_eq_one_or_of_mem_zpowers hu.sq hu.ne_one (h.dComm_mem_zpowers hK hu hd hk))
    have hcl : ∀ d ∈ zGroup Ω, n * d * n⁻¹ = d ∨ n * d * n⁻¹ = u * d := by
      intro d hd
      have hz := h.eq_of_dComm_eq hK hu (hxN n d hd) hd (fun k hk => hdcomm d hd k hk)
      rcases det_tw_eq_one_or_of_mem_zpowers hu.sq hu.ne_one hz with h1 | h1
      · left; exact (mul_inv_eq_one.mp h1).symm
      · right
        have h2 : (n * d * n⁻¹)⁻¹ = d⁻¹ * u := by rw [← h1]; group
        calc n * d * n⁻¹ = ((n * d * n⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
          _ = (d⁻¹ * u)⁻¹ := by rw [h2]
          _ = u⁻¹ * d := by group
          _ = u * d := by rw [inv_eq_of_mul_eq_one_right hu.sq]
    have hnn1 : ∀ d ∈ zGroup Ω, (n * n) * d * (n * n)⁻¹ = d := by
      intro d hd
      have e1 : (n * n) * d * (n * n)⁻¹ = n * (n * d * n⁻¹) * n⁻¹ := by group
      rw [e1]
      rcases hcl d hd with h1 | h1
      · rw [h1]; exact h1
      · rw [h1]
        calc n * (u * d) * n⁻¹ = (n * u * n⁻¹) * (n * d * n⁻¹) := by group
          _ = u * (u * d) := by rw [hnu, h1]
          _ = d := by rw [← mul_assoc, hu.sq, one_mul]
    have hconjnn : TL4.conjMat he (n * n) = 1 := by
      apply TL4.matrix_ext_mulVec
      intro w
      rw [Matrix.one_mulVec]
      apply TL4.e8Coord_injective he
      rw [← TL4.conj_e8Coord he (hxN (n * n)) w, hnn1 _ (TL4.e8Coord_mem he w)]
    exact hA3sq (hnn.symm.trans hconjnn)
  obtain ⟨k₀, hk₀K, hk₀⟩ := hkey
  have hcomm_gen : ∀ g : G, (h.rhoD he) g = 1 → ∀ k : G,
      g * k * g⁻¹ * k⁻¹ ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
    intro g hg k
    rw [← h.rhoD_ker he, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hg]
    simp
  have hF : ∀ k ∈ K, n * n * n * k * (n * n * n)⁻¹ = k ∨
      n * n * n * k * (n * n * n)⁻¹ = u * k := by
    intro k hk
    have hgN : n * n * n ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hn) hn
    have hcK : n * n * n * k * (n * n * n)⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem (hconjK _ hgN k hk) (K.inv_mem hk)
    have hρ : (h.rhoD he) (n * n * n) = 1 := Subtype.ext hn3
    have hcC : n * n * n * k * (n * n * n)⁻¹ * k⁻¹ ∈
        Subgroup.centralizer (zGroup Ω : Set G) := hcomm_gen _ hρ k
    have hmem : n * n * n * k * (n * n * n)⁻¹ * k⁻¹ ∈
        K ⊓ Subgroup.centralizer (zGroup Ω : Set G) := ⟨hcK, hcC⟩
    rw [h.inf_centralizer_zGroup hK hu] at hmem
    rcases det_tw_eq_one_or_of_mem_zpowers hu.sq hu.ne_one hmem with h1 | h1
    · left
      calc n * n * n * k * (n * n * n)⁻¹
          = (n * n * n * k * (n * n * n)⁻¹ * k⁻¹) * k := by group
        _ = k := by rw [h1, one_mul]
    · right
      calc n * n * n * k * (n * n * n)⁻¹
          = (n * n * n * k * (n * n * n)⁻¹ * k⁻¹) * k := by group
        _ = u * k := by rw [h1]
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : G, k₁ = n * k₀ * n⁻¹ := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k₂ : G, k₂ = n * k₁ * n⁻¹ := ⟨_, rfl⟩
  have hk₁K : k₁ ∈ K := hk₁ ▸ hconjK n hn k₀ hk₀K
  have hk₂K : k₂ ∈ K := hk₂ ▸ hconjK n hn k₁ hk₁K
  have hk₀' : ¬ (k₁ = k₀ ∨ k₁ = u * k₀) := by rw [hk₁]; exact hk₀
  have hk₀1 : k₁ ≠ k₀ := fun h => hk₀' (Or.inl h)
  have hk₀2 : k₁ ≠ u * k₀ := fun h => hk₀' (Or.inr h)
  have hn1 : n⁻¹ * k₁ * n = k₀ := by rw [hk₁]; group
  have hiii : ¬ (k₂ = k₁ ∨ k₂ = u * k₁) := by
    have hc : ∀ c : G, (c = 1 ∨ c = u) → n * k₁ * n⁻¹ = c * k₁ → k₁ = c * k₀ := by
      intro c hc h2
      calc k₁ = n⁻¹ * (n * k₁ * n⁻¹) * n := by group
        _ = n⁻¹ * (c * k₁) * n := by rw [h2]
        _ = (n⁻¹ * c * n) * (n⁻¹ * k₁ * n) := by group
        _ = c * k₀ := by rw [hconjc' c hc, hn1]
    rintro (h2 | h2)
    · have h3 : n * k₁ * n⁻¹ = 1 * k₁ := by rw [one_mul, ← hk₂, h2]
      have h4 := hc 1 (Or.inl rfl) h3
      rw [one_mul] at h4
      exact hk₀1 h4
    · have h3 : n * k₁ * n⁻¹ = u * k₁ := by rw [← hk₂, h2]
      exact hk₀2 (hc u (Or.inr rfl) h3)
  have hiv : ¬ (k₂ = k₀ ∨ k₂ = u * k₀) := by
    have hk3 : n * n * n * k₀ * (n * n * n)⁻¹ = n * k₂ * n⁻¹ := by
      rw [hk₂, hk₁]; group
    have hF0 := hF k₀ hk₀K
    rw [hk3] at hF0
    rintro (h2 | h2)
    · rw [h2, ← hk₁] at hF0
      rcases hF0 with h4 | h4
      · exact hk₀1 h4
      · exact hk₀2 h4
    · have h4 : n * k₂ * n⁻¹ = u * k₁ := by
        rw [h2]
        calc n * (u * k₀) * n⁻¹ = (n * u * n⁻¹) * (n * k₀ * n⁻¹) := by group
          _ = u * k₁ := by rw [hnu, hk₁]
      rw [h4] at hF0
      rcases hF0 with h5 | h5
      · apply hk₀2
        calc k₁ = u * (u * k₁) := by rw [← mul_assoc, hu.sq, one_mul]
          _ = u * k₀ := by rw [h5]
      · exact hk₀1 (mul_left_cancel h5)
  have hxK : k₁ * k₀⁻¹ ∈ K := K.mul_mem hk₁K (K.inv_mem hk₀K)
  have hyK : k₂ * k₁⁻¹ ∈ K := K.mul_mem hk₂K (K.inv_mem hk₁K)
  have hxc : k₁ * k₀⁻¹ ∈ commutator G := by
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top n) (Subgroup.mem_top k₀)
    rw [commutatorElement_def] at this
    rw [hk₁]; exact this
  have hyc : k₂ * k₁⁻¹ ∈ commutator G := by
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top n) (Subgroup.mem_top k₁)
    rw [commutatorElement_def] at this
    rw [hk₂]; exact this
  have hxu : k₁ * k₀⁻¹ ∉ Subgroup.zpowers u := by
    intro hx
    rcases det_tw_eq_one_or_of_mem_zpowers hu.sq hu.ne_one hx with h1 | h1
    · exact hk₀1 (mul_inv_eq_one.mp h1)
    · apply hk₀2
      calc k₁ = (k₁ * k₀⁻¹) * k₀ := by group
        _ = u * k₀ := by rw [h1]
  have hxx : (k₁ * k₀⁻¹) * (k₁ * k₀⁻¹) = u := det_tw_q8_sq hQ hxK hxu
  have hxord : orderOf (k₁ * k₀⁻¹) = 4 := by
    have hnot : ¬ (k₁ * k₀⁻¹) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, hxx]; exact hu.ne_one
    have hfin : (k₁ * k₀⁻¹) ^ 2 ^ (1 + 1) = 1 := by
      show (k₁ * k₀⁻¹) ^ 4 = 1
      rw [show (k₁ * k₀⁻¹) ^ 4 = ((k₁ * k₀⁻¹) * (k₁ * k₀⁻¹)) * ((k₁ * k₀⁻¹) * (k₁ * k₀⁻¹)) by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two], hxx, hu.sq]
    have := orderOf_eq_prime_pow hnot hfin
    simpa using this
  have hyx : k₂ * k₁⁻¹ ∉ Subgroup.zpowers (k₁ * k₀⁻¹) := by
    intro hy
    have hk2inv : k₂ = k₀⁻¹ ∨ k₂ = u * k₀⁻¹ → False := by
      intro hh
      apply hiv
      rcases det_tw_inv_mem hQ hk₀K with h4 | h4
      · rcases hh with h5 | h5
        · left; rw [h5, h4]
        · right; rw [h5, h4]
      · rcases hh with h5 | h5
        · right; rw [h5, h4]
        · left; rw [h5, h4, ← mul_assoc, hu.sq, one_mul]
    rcases det_tw_zpowers_sq hu (hxx := hxx) hxK hxu _ hy with h1 | h1 | h1 | h1
    ·
      exact hiii (Or.inl (mul_inv_eq_one.mp h1))
    ·
      apply hk2inv
      have hk2 : k₂ = k₁ * k₀⁻¹ * k₁ := by
        calc k₂ = (k₂ * k₁⁻¹) * k₁ := by group
          _ = (k₁ * k₀⁻¹) * k₁ := by rw [h1]
      rw [hk2]
      exact det_tw_mid hQ hk₀K hk₁K
    ·
      apply hiii
      right
      calc k₂ = (k₂ * k₁⁻¹) * k₁ := by group
        _ = u * k₁ := by rw [h1]
    ·
      apply hk2inv
      have hk2 : k₂ = u * (k₁ * k₀⁻¹ * k₁) := by
        calc k₂ = (k₂ * k₁⁻¹) * k₁ := by group
          _ = (u * (k₁ * k₀⁻¹)) * k₁ := by rw [h1]
          _ = u * (k₁ * k₀⁻¹ * k₁) := by group
      rw [hk2]
      rcases det_tw_mid hQ hk₀K hk₁K with h3 | h3
      · right; rw [h3]
      · left
        rw [h3, ← mul_assoc, hu.sq, one_mul]
  have hsub : ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G) ⊆ commutator G :=
    Set.insert_subset_iff.mpr ⟨hxc, Set.singleton_subset_iff.mpr hyc⟩
  have hHK : Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G) ≤ K :=
    (Subgroup.closure_le K).mpr (Set.insert_subset_iff.mpr ⟨hxK, Set.singleton_subset_iff.mpr hyK⟩)
  have hxH : k₁ * k₀⁻¹ ∈ Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hyH : k₂ * k₁⁻¹ ∈ Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hzH : Subgroup.zpowers (k₁ * k₀⁻¹) ≤ Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G) :=
    Subgroup.zpowers_le.mpr hxH
  have hcardx : Nat.card (Subgroup.zpowers (k₁ * k₀⁻¹)) = 4 := by
    rw [Nat.card_zpowers, hxord]
  have hdvd1 : 4 ∣ Nat.card (Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G)) := by
    rw [← hcardx]; exact Subgroup.card_dvd_of_le hzH
  have hdvd2 : Nat.card (Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G)) ∣ 8 := by
    rw [← h.card K hK]; exact Subgroup.card_dvd_of_le hHK
  have hpos : 0 < Nat.card (Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G)) := Nat.card_pos
  have hHcard : Nat.card (Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G)) = 8 := by
    have hne4 : Nat.card (Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G)) ≠ 4 := by
      intro h4
      apply hyx
      have heq : Subgroup.zpowers (k₁ * k₀⁻¹) = Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G) :=
        Subgroup.eq_of_le_of_card_ge hzH (le_of_eq (by rw [h4, hcardx]))
      rw [heq]; exact hyH
    have hle : Nat.card (Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G)) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hdvd2
    omega
  have hHeq : Subgroup.closure ({k₁ * k₀⁻¹, k₂ * k₁⁻¹} : Set G) = K :=
    Subgroup.eq_of_le_of_card_ge hHK (le_of_eq (by rw [h.card K hK, hHcard]))
  rw [← hHeq]
  exact (Subgroup.closure_le _).mpr hsub

theorem commutator_eq_top : commutator G = ⊤ := by
  have hle : pSpan Ω ≤ commutator G := pSpan_le fun L hL => h.member_le_commutator hL
  rw [h.gen] at hle
  exact top_le_iff.mp hle

private theorem det_geo_realize {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {M : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hM : M.det ≠ 0) :
    ∃ g : G, TL4.conjMat he g = M := by
  have hdet : M.det = 1 := det_geo_zmod_ne_zero _ hM
  have hall : ∀ N : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), N ∈ (h.rhoD he).range := by
    intro N
    rw [h.rhoD_range he]
    exact Subgroup.mem_top N
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hall ⟨M, hdet⟩)
  exact ⟨g, congrArg Subtype.val hg⟩

theorem card_isHyp : Set.ncard {H : Subgroup G | IsHyp Ω H} = 7 := by
  classical
  obtain ⟨e, he⟩ := h.exists_basis
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : {L : Subgroup G // IsHyp Ω L} → {f : Fin 3 → ZMod 2 // f ≠ 0},
      ∀ L, (Φ L).1 = Classical.choose (det_geo_hyp_fun he L.2) :=
    ⟨fun L => ⟨Classical.choose (det_geo_hyp_fun he L.2),
      (Classical.choose_spec (det_geo_hyp_fun he L.2)).1⟩, fun L => rfl⟩
  have hΦ : ∀ (L : {L : Subgroup G // IsHyp Ω L}) (w : Fin 3 → ZMod 2),
      TL4.e8Coord e w ∈ L.1 ↔
        dotProduct (Classical.choose (det_geo_hyp_fun he L.2)) w = 0 :=
    fun L w => (Classical.choose_spec (det_geo_hyp_fun he L.2)).2 w
  have hinj : Function.Injective Φ := by
    intro L L' hLL
    have hc : Classical.choose (det_geo_hyp_fun he L.2) =
        Classical.choose (det_geo_hyp_fun he L'.2) := by
      rw [← hΦdef L, ← hΦdef L', hLL]
    apply Subtype.ext
    apply det_geo_ext he L.2.1 L'.2.1
    intro w
    rw [hΦ L w, hΦ L' w, hc]
  have hsurj : Function.Surjective Φ := by
    rintro ⟨f, hf⟩
    obtain ⟨H, hHyp, hHf⟩ := det_geo_hyp_construct he hf
    refine ⟨⟨H, hHyp⟩, Subtype.ext ?_⟩
    rw [hΦdef]
    refine det_geo_eq_of_zero_iff _ _ (Classical.choose_spec (det_geo_hyp_fun he hHyp)).1 hf ?_
    intro w
    rw [← (Classical.choose_spec (det_geo_hyp_fun he hHyp)).2 w, hHf w]
  rw [← Nat.card_coe_set_eq]
  refine (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).trans ?_
  rw [Nat.card_eq_fintype_card, det_geo_card_nonzero]

theorem exists_conj_hyp {H H' : Subgroup G} (hH : IsHyp Ω H) (hH' : IsHyp Ω H') :
    ∃ g : G, conjSub g H = H' := by
  classical
  obtain ⟨e, he⟩ := h.exists_basis
  have hN := h.zGroup_normal
  obtain ⟨f, hf0, hf⟩ := det_geo_hyp_fun he hH
  obtain ⟨f', hf0', hf'⟩ := det_geo_hyp_fun he hH'
  by_cases hff : f = f'
  · subst hff
    refine ⟨1, ?_⟩
    rw [conjSub_one]
    exact det_geo_ext he hH.1 hH'.1 fun w => by rw [hf w, hf' w]
  · obtain ⟨a, hfa, hfa'⟩ := det_geo_dot_one_pair f f' hf0 hf0' hff
    have hφa : dotProduct (f + f') a = 0 := by
      rw [add_dotProduct, hfa, hfa']
      decide
    obtain ⟨g, hg⟩ := h.det_geo_realize he (M := det_geo_T a (f + f'))
      (by rw [det_geo_T_det a (f + f') hφa]; decide)
    have key : ∀ w : Fin 3 → ZMod 2,
        dotProduct f (Matrix.mulVec (det_geo_T a (f + f')) w) = dotProduct f' w := by
      intro w
      rw [det_geo_T_mulVec, dotProduct_add, dotProduct_smul, hfa, smul_eq_mul, mul_one,
        add_dotProduct]
      exact det_geo_zmod_add_add _ _
    have hxg : ∀ z ∈ zGroup Ω, g⁻¹ * z * g⁻¹⁻¹ ∈ zGroup Ω := fun z hz => hN.conj_mem z hz g⁻¹
    have hgg : ∀ z ∈ zGroup Ω, g * z * g⁻¹ ∈ zGroup Ω := fun z hz => hN.conj_mem z hz g
    have hconjinv : TL4.conjMat he g⁻¹ * det_geo_T a (f + f') = 1 := by
      rw [← hg, ← TL4.conjMat_mul he hxg hgg, inv_mul_cancel, TL4.conjMat_one he]
    have hinvT : TL4.conjMat he g⁻¹ = det_geo_T a (f + f') := by
      calc TL4.conjMat he g⁻¹
          = TL4.conjMat he g⁻¹ * (det_geo_T a (f + f') * det_geo_T a (f + f')) := by
            rw [det_geo_T_mul_self a (f + f') hφa, mul_one]
        _ = (TL4.conjMat he g⁻¹ * det_geo_T a (f + f')) * det_geo_T a (f + f') := by
            rw [mul_assoc]
        _ = det_geo_T a (f + f') := by rw [hconjinv, one_mul]
    have hcoord : ∀ w : Fin 3 → ZMod 2,
        g⁻¹ * TL4.e8Coord e w * g = TL4.e8Coord e (Matrix.mulVec (TL4.conjMat he g⁻¹) w) := by
      intro w
      have := det_geo_conj_coord hN he g⁻¹ w
      rwa [inv_inv] at this
    refine ⟨g, det_geo_ext he (det_geo_conjSub_le hN hH.1 g) hH'.1 fun w => ?_⟩
    rw [mem_conjSub_iff, hcoord w, hf, hinvT, key w, hf' w]

theorem isHyp_conjSub {H : Subgroup G} (hH : IsHyp Ω H) (g : G) : IsHyp Ω (conjSub g H) := by
  refine ⟨det_geo_conjSub_le h.zGroup_normal hH.1 g, ?_⟩
  rw [det_geo_card_conjSub]
  exact hH.2

theorem eq_one_of_forall_normalizer_hyp {H : Subgroup G} (hH : IsHyp Ω H) {d : G}
    (hd : d ∈ zGroup Ω) (hfix : ∀ g ∈ Subgroup.normalizer (H : Set G), g * d * g⁻¹ = d) :
    d = 1 := by
  classical
  obtain ⟨e, he⟩ := h.exists_basis
  have hN := h.zGroup_normal
  obtain ⟨f, hf0, hf⟩ := det_geo_hyp_fun he hH
  obtain ⟨w, rfl⟩ := TL4.exists_e8Coord_eq he hd
  by_contra hne
  have hw0 : w ≠ 0 := (det_geo_coord_ne_one he).mp hne
  obtain ⟨x, hxH, hx⟩ := TL4.exists_mem_not_mem (E := H)
    ({1, TL4.e8Coord e w} : Finset G)
    (by rw [hH.2]; exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨hx1, hxd⟩ := hx
  obtain ⟨a, ha⟩ := TL4.exists_e8Coord_eq he (hH.1 hxH)
  have ha0 : a ≠ 0 := fun h0 => hx1 (by rw [← ha, h0, TL4.e8Coord_zero])
  have haw : a ≠ w := fun h0 => hxd (by rw [← ha, h0])
  have hfa : dotProduct f a = 0 := (hf a).mp (by rw [ha]; exact hxH)
  obtain ⟨φ, hφa, hφw⟩ := det_geo_phi_zero_one a w ha0 hw0 haw
  obtain ⟨g, hg⟩ := h.det_geo_realize he (M := det_geo_T a φ)
    (by rw [det_geo_T_det a φ hφa]; decide)
  have hgN : g ∈ Subgroup.normalizer (H : Set G) :=
    det_geo_norm hN he hH.1 hf
      (fun v => by rw [det_geo_T_mulVec, dotProduct_add, dotProduct_smul, hfa, smul_zero,
        add_zero]) hg
  have hgd := hfix g hgN
  rw [det_geo_conj_coord hN he g w, hg, det_geo_T_mulVec, hφw, one_smul] at hgd
  have h2 := TL4.e8Coord_injective he hgd
  exact ha0 (det_geo_add_left_eq w a h2)

theorem inf_normalizer_hyp_of_not_mem {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) {H : Subgroup G} (hH : IsHyp Ω H) (huH : u ∉ H) :
    K ⊓ Subgroup.normalizer (H : Set G) = Subgroup.zpowers u := by
  classical
  obtain ⟨e, he⟩ := h.exists_basis
  have hu' : u ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K, hK, hu⟩)
  obtain ⟨f, hf0, hf⟩ := det_geo_hyp_fun he hH
  obtain ⟨p, hp⟩ := TL4.exists_e8Coord_eq he hu'
  have hfp : dotProduct f p = 1 := by
    have h0 : dotProduct f p ≠ 0 := fun h0 => huH (by rw [← hp]; exact (hf p).mpr h0)
    exact det_geo_zmod_ne_zero _ h0
  have hcov : ∀ d ∈ zGroup Ω, d ∈ H ∨ d * u ∈ H := by
    intro d hd
    obtain ⟨w, rfl⟩ := TL4.exists_e8Coord_eq he hd
    by_cases hw : dotProduct f w = 0
    · exact Or.inl ((hf w).mpr hw)
    · right
      have hw1 : dotProduct f w = 1 := det_geo_zmod_ne_zero _ hw
      have hmem : TL4.e8Coord e (w + p) ∈ H :=
        (hf (w + p)).mpr (by rw [dotProduct_add, hw1, hfp]; decide)
      rwa [TL4.e8Coord_add he, hp] at hmem
  have hconjU : ∀ k ∈ K, k * u * k⁻¹ = u := fun k hk =>
    hu.conj_eq (conjSub_eq_self_of_mem hk)
  have hcomm_u : ∀ y ∈ zGroup Ω, u * y * u⁻¹ = y := fun y hy => by
    rw [h.zGroup_comm u hu' y hy]
    group
  apply le_antisymm
  · intro k hk
    rw [Subgroup.mem_inf] at hk
    obtain ⟨hkK, hkN⟩ := hk
    have hA : ∀ y ∈ H, k * y * k⁻¹ = y := by
      intro y hy
      have hρ : dComm y k ∈ Subgroup.zpowers u := h.dComm_mem_zpowers hK hu (hH.1 hy) hkK
      rcases det_geo_mem_zpowers hu hρ with h1 | h1
      · have hc : y * k = k * y := dComm_eq_one_iff.mp h1
        rw [← hc, mul_inv_cancel_right]
      · exfalso
        apply huH
        have hkN' : k * y * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hkN y).mp hy
        have e1 : k * y * k⁻¹ * y⁻¹ = (dComm y k)⁻¹ := by
          unfold dComm
          group
        rw [h1, inv_eq_of_mul_eq_one_right hu.sq] at e1
        rw [← e1]
        exact H.mul_mem hkN' (H.inv_mem hy)
    have hcommutes : ∀ d ∈ zGroup Ω, d * k = k * d := by
      intro d hd
      rcases hcov d hd with hdH | hduH
      · have hkd : k * d = d * k := by
          calc k * d = (k * d * k⁻¹) * k := by group
            _ = d * k := by rw [hA d hdH]
        exact hkd.symm
      · have hkdu : k * (d * u) = d * u * k := by
          calc k * (d * u) = (k * (d * u) * k⁻¹) * k := by group
            _ = d * u * k := by rw [hA (d * u) hduH]
        have hku : k * u = u * k := by
          calc k * u = (k * u * k⁻¹) * k := by group
            _ = u * k := by rw [hconjU k hkK]
        have hkd : k * d = d * k := by
          calc k * d = k * d * (u * u) := by rw [hu.sq, mul_one]
            _ = k * (d * u) * u := by group
            _ = d * u * k * u := by rw [hkdu]
            _ = d * (u * k * u) := by group
            _ = d * (k * u * u) := by rw [← hku]
            _ = d * k * (u * u) := by group
            _ = d * k := by rw [hu.sq, mul_one]
        exact hkd.symm
    have hcent : k ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hcommutes d hd
    have hk2 : k ∈ K ⊓ Subgroup.centralizer (zGroup Ω : Set G) :=
      Subgroup.mem_inf.mpr ⟨hkK, hcent⟩
    rw [h.inf_centralizer_zGroup hK hu] at hk2
    exact hk2
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr
      ⟨hu.mem, det_geo_normalizer_of_centralizes h.zGroup_normal hH.1 hcomm_u⟩

theorem exists_conj_hyp_of_not_mem {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) {H H' : Subgroup G} (hH : IsHyp Ω H) (hH' : IsHyp Ω H')
    (huH : u ∉ H) (huH' : u ∉ H') : ∃ k ∈ K, conjSub k H = H' := by
  classical
  obtain ⟨e, he⟩ := h.exists_basis
  have hN := h.zGroup_normal
  have hu' : u ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K, hK, hu⟩)
  obtain ⟨p, hp⟩ := TL4.exists_e8Coord_eq he hu'
  have hp0 : p ≠ 0 := (det_geo_coord_ne_one he).mp (by rw [hp]; exact hu.ne_one)
  have hInf := h.inf_normalizer_hyp_of_not_mem hK hu hH huH
  have hconjU : ∀ k ∈ K, k⁻¹ * u * k = u := fun k hk => by
    have := hu.conj_eq (conjSub_eq_self_of_mem (K.inv_mem hk))
    rwa [inv_inv] at this
  have hval : ∀ L : {L : Subgroup G // IsHyp Ω L ∧ u ∉ L},
      dotProduct (Classical.choose (det_geo_hyp_fun he L.2.1)) p = 1 := by
    intro L
    have hs := Classical.choose_spec (det_geo_hyp_fun he L.2.1)
    have h0 : dotProduct (Classical.choose (det_geo_hyp_fun he L.2.1)) p ≠ 0 := fun h0 => by
      have hmem := (hs.2 p).mpr h0
      rw [hp] at hmem
      exact L.2.2 hmem
    exact det_geo_zmod_ne_zero _ h0
  have hιinj : Function.Injective (fun L : {L : Subgroup G // IsHyp Ω L ∧ u ∉ L} =>
      (⟨Classical.choose (det_geo_hyp_fun he L.2.1), hval L⟩ :
        {f : Fin 3 → ZMod 2 // dotProduct f p = 1})) := by
    intro L L' hLL
    have hc : Classical.choose (det_geo_hyp_fun he L.2.1) =
        Classical.choose (det_geo_hyp_fun he L'.2.1) := congrArg Subtype.val hLL
    apply Subtype.ext
    apply det_geo_ext he L.2.1.1 L'.2.1.1
    intro w
    rw [(Classical.choose_spec (det_geo_hyp_fun he L.2.1)).2 w,
      (Classical.choose_spec (det_geo_hyp_fun he L'.2.1)).2 w, hc]
  have hfib : Nat.card {f : Fin 3 → ZMod 2 // dotProduct f p = 1} = 4 := by
    rw [Nat.card_eq_fintype_card, det_geo_card_fiber p hp0]
  have hXcard : Nat.card {L : Subgroup G // IsHyp Ω L ∧ u ∉ L} ≤ 4 := by
    rw [← hfib]
    exact Nat.card_le_card_of_injective _ hιinj
  have hXfin : Finite {L : Subgroup G // IsHyp Ω L ∧ u ∉ L} := Finite.of_injective _ hιinj
  have hu_le : Subgroup.zpowers u ≤ K := Subgroup.zpowers_le.mpr hu.mem
  have hS'card : Nat.card ((Subgroup.zpowers u).subgroupOf K) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hu_le).toEquiv,
      card_zpowers_of_involution hu.sq hu.ne_one]
  have hidx : ((Subgroup.zpowers u).subgroupOf K).index = 4 := by
    have h1 := Subgroup.index_mul_card (H := (Subgroup.zpowers u).subgroupOf K)
    rw [hS'card, h.card K hK] at h1
    omega
  have hQcard : Nat.card (↥K ⧸ (Subgroup.zpowers u).subgroupOf K) = 4 := hidx
  have hF : ∀ k : K, IsHyp Ω (conjSub (k : G) H) ∧ u ∉ conjSub (k : G) H := by
    intro k
    refine ⟨isHyp_conjSub h hH (k : G), fun hmem => huH ?_⟩
    rw [mem_conjSub_iff, hconjU (k : G) k.2] at hmem
    exact hmem
  obtain ⟨F, hFdef⟩ : ∃ F : K → {L : Subgroup G // IsHyp Ω L ∧ u ∉ L},
      ∀ k : K, (F k).1 = conjSub (k : G) H :=
    ⟨fun k => ⟨conjSub (k : G) H, hF k⟩, fun k => rfl⟩
  have hFwd : ∀ a b : K, a⁻¹ * b ∈ (Subgroup.zpowers u).subgroupOf K → F a = F b := by
    intro a b hab
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab
    have hmemInf : (a : G)⁻¹ * (b : G) ∈ K ⊓ Subgroup.normalizer (H : Set G) := by
      rw [hInf]
      exact hab
    have hc : conjSub ((a : G)⁻¹ * (b : G)) H = H :=
      det_geo_conjSub_eq_of_mem (Subgroup.mem_inf.mp hmemInf).2
    apply Subtype.ext
    rw [hFdef, hFdef]
    calc conjSub (a : G) H = conjSub (a : G) (conjSub ((a : G)⁻¹ * (b : G)) H) := by rw [hc]
      _ = conjSub ((a : G) * ((a : G)⁻¹ * (b : G))) H := (conjSub_mul _ _ _).symm
      _ = conjSub (b : G) H := by rw [mul_inv_cancel_left]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (↥K ⧸ (Subgroup.zpowers u).subgroupOf K) →
      {L : Subgroup G // IsHyp Ω L ∧ u ∉ L}, ∀ k : K, ψ (QuotientGroup.mk k) = F k :=
    ⟨Quotient.lift F (fun a b hab => hFwd a b (QuotientGroup.leftRel_apply.mp hab)),
      fun k => rfl⟩
  have hψinj : Function.Injective ψ := by
    intro q q' hqq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
    rw [hψ, hψ] at hqq
    have hab : conjSub (a : G) H = conjSub (b : G) H := by
      have := congrArg Subtype.val hqq
      rwa [hFdef, hFdef] at this
    have hN' : (a : G)⁻¹ * (b : G) ∈ Subgroup.normalizer (H : Set G) := by
      apply det_geo_mem_normalizer_of_conjSub_eq
      calc conjSub ((a : G)⁻¹ * (b : G)) H = conjSub (a : G)⁻¹ (conjSub (b : G) H) :=
            conjSub_mul _ _ _
        _ = conjSub (a : G)⁻¹ (conjSub (a : G) H) := by rw [hab]
        _ = H := conjSub_inv_conjSub _ _
    have hmem : (a : G)⁻¹ * (b : G) ∈ K ⊓ Subgroup.normalizer (H : Set G) :=
      Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem a.2) b.2, hN'⟩
    rw [hInf] at hmem
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hmem
  have hbij : Function.Bijective ψ := by
    haveI := hXfin
    refine hψinj.bijective_of_nat_card_le ?_
    rw [hQcard]
    exact hXcard
  obtain ⟨q, hq⟩ := hbij.2 ⟨H', hH', huH'⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨(a : G), a.2, ?_⟩
  have := congrArg Subtype.val hq
  rw [hψ, hFdef] at this
  exact this

theorem le_normalizer_hyp_of_mem {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) {H : Subgroup G} (hH : IsHyp Ω H) (huH : u ∈ H) :
    K ≤ Subgroup.normalizer (H : Set G) := by
  have hfwd : ∀ k ∈ K, ∀ y ∈ H, k * y * k⁻¹ ∈ H := by
    intro k hk y hy
    have hρ : dComm y k ∈ Subgroup.zpowers u := h.dComm_mem_zpowers hK hu (hH.1 hy) hk
    have hρH : dComm y k ∈ H := (Subgroup.zpowers_le.mpr huH) hρ
    have e1 : k * y * k⁻¹ = (dComm y k)⁻¹ * y := by
      unfold dComm
      group
    rw [e1]
    exact H.mul_mem (H.inv_mem hρH) hy
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hfwd k hk y hy
  · intro hy
    have h2 := hfwd k⁻¹ (K.inv_mem hk) _ hy
    have e2 : k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y := by group
    rwa [e2] at h2

end DEHyp

end CFSG.ClassicalInvolution.Q3.Sec13

module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

structure Y6ARel {G : Type} [Group G] (a₁ b₁ a₂ b₂ z : G) : Prop where
  z_sq : z ^ 2 = 1
  a1_sq : a₁ ^ 2 = z
  b1_sq : b₁ ^ 2 = z
  a2_sq : a₂ ^ 2 = z
  b2_sq : b₂ ^ 2 = z
  comm1 : ⁅a₁, b₁⁆ = z
  comm2 : ⁅a₂, b₂⁆ = z
  a1a2 : ⁅a₁, a₂⁆ = 1
  a1b2 : ⁅a₁, b₂⁆ = 1
  b1a2 : ⁅b₁, a₂⁆ = 1
  b1b2 : ⁅b₁, b₂⁆ = 1

variable {G : Type} [Group G] {a₁ b₁ a₂ b₂ z : G}

private lemma sq_a1 (h : Y6ARel a₁ b₁ a₂ b₂ z) : a₁ * a₁ = z := by
  simpa [pow_two] using h.a1_sq

private lemma sq_b1 (h : Y6ARel a₁ b₁ a₂ b₂ z) : b₁ * b₁ = z := by
  simpa [pow_two] using h.b1_sq

private lemma sq_a2 (h : Y6ARel a₁ b₁ a₂ b₂ z) : a₂ * a₂ = z := by
  simpa [pow_two] using h.a2_sq

private lemma sq_b2 (h : Y6ARel a₁ b₁ a₂ b₂ z) : b₂ * b₂ = z := by
  simpa [pow_two] using h.b2_sq

private lemma sq_z (h : Y6ARel a₁ b₁ a₂ b₂ z) : z * z = 1 := by
  simpa [pow_two] using h.z_sq

private lemma commute_self_sq {g z : G} (hg : g ^ 2 = z) : g * z = z * g := by
  rw [← hg]; group

private lemma z_comm_a1 (h : Y6ARel a₁ b₁ a₂ b₂ z) : z * a₁ = a₁ * z :=
  (commute_self_sq h.a1_sq).symm

private lemma z_comm_b1 (h : Y6ARel a₁ b₁ a₂ b₂ z) : z * b₁ = b₁ * z :=
  (commute_self_sq h.b1_sq).symm

private lemma z_comm_a2 (h : Y6ARel a₁ b₁ a₂ b₂ z) : z * a₂ = a₂ * z :=
  (commute_self_sq h.a2_sq).symm

private lemma z_comm_b2 (h : Y6ARel a₁ b₁ a₂ b₂ z) : z * b₂ = b₂ * z :=
  (commute_self_sq h.b2_sq).symm

private lemma swap_commutator {x y z : G} (hxy : ⁅x, y⁆ = z) (hzz : z * z = 1) :
    y * x = z * (x * y) := by
  have h1 : x * y = z * (y * x) := by
    have hc := hxy
    simp only [commutatorElement_def] at hc
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = z * (y * x) := by rw [hc]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  calc y * x = z⁻¹ * (z * (y * x)) := by group
    _ = z⁻¹ * (x * y) := by rw [← h1]
    _ = z * (x * y) := by rw [hzi]

private lemma b1a1_eq (h : Y6ARel a₁ b₁ a₂ b₂ z) : b₁ * a₁ = z * (a₁ * b₁) :=
  swap_commutator h.comm1 (sq_z h)

private lemma b2a2_eq (h : Y6ARel a₁ b₁ a₂ b₂ z) : b₂ * a₂ = z * (a₂ * b₂) :=
  swap_commutator h.comm2 (sq_z h)

private def Q8List (p q z : G) (u : G) : Prop :=
  u = 1 ∨ u = z ∨ u = p ∨ u = p * z ∨ u = q ∨ u = q * z ∨ u = p * q ∨ u = p * q * z

private lemma q8_z_mul_mul {p q z : G} (hzp : z * p = p * z) (hzq : z * q = q * z) :
    z * (p * q) = (p * q) * z := by
  rw [← mul_assoc, hzp, mul_assoc, hzq, mul_assoc]

private lemma q8_pq_p {p q z : G} (hpp : p * p = z) (hzp : z * p = p * z)
    (hzz : z * z = 1) (hqp : q * p = z * (p * q)) : (p * q) * p = q := by
  rw [mul_assoc, hqp, ← mul_assoc, ← hzp,
    show (z * p) * (p * q) = z * ((p * p) * q) by group, hpp, ← mul_assoc, hzz, one_mul]

private lemma Q8List_of_closure {p q z : G} (hpp : p * p = z) (hqq : q * q = z)
    (hzz : z * z = 1) (hzp : z * p = p * z) (hzq : z * q = q * z)
    (hqp : q * p = z * (p * q)) :
    ∀ u ∈ (closure {p, q} : Subgroup G), Q8List p q z u := by
  have h_pz_p : (p * z) * p = 1 := by
    rw [mul_assoc, hzp, ← mul_assoc, hpp, hzz]
  have h_q_p : q * p = p * q * z := by
    rw [hqp, q8_z_mul_mul hzp hzq]
  have h_qz_p : (q * z) * p = p * q := by
    rw [mul_assoc, hzp, ← mul_assoc, h_q_p, mul_assoc, hzz, mul_one]
  have h_pq_p : (p * q) * p = q := q8_pq_p hpp hzp hzz hqp
  have h_pqz_p : (p * q * z) * p = q * z := by
    rw [mul_assoc, hzp, ← mul_assoc, h_pq_p]
  have h_pz_q : (p * z) * q = p * q * z := by
    rw [mul_assoc, hzq, ← mul_assoc]
  have h_qz_q : (q * z) * q = 1 := by
    rw [mul_assoc, hzq, ← mul_assoc, hqq, hzz]
  have h_pq_q : (p * q) * q = p * z := by
    rw [mul_assoc, hqq]
  have h_pqz_q : (p * q * z) * q = p := by
    rw [mul_assoc, hzq, ← mul_assoc, h_pq_q, mul_assoc, hzz, mul_one]
  have h_inv_p : p⁻¹ = p * z := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hpp, hzz]
  have h_inv_q : q⁻¹ = q * z := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hqq, hzz]
  have mul_p : ∀ x, Q8List p q z x → Q8List p q z (x * p) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [Q8List]
    · rw [hzp]; simp [Q8List]
    · rw [hpp]; simp [Q8List]
    · rw [h_pz_p]; simp [Q8List]
    · rw [h_q_p]; simp [Q8List]
    · rw [h_qz_p]; simp [Q8List]
    · rw [h_pq_p]; simp [Q8List]
    · rw [h_pqz_p]; simp [Q8List]
  have mul_q : ∀ x, Q8List p q z x → Q8List p q z (x * q) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [Q8List]
    · rw [hzq]; simp [Q8List]
    · simp [Q8List]
    · rw [h_pz_q]; simp [Q8List]
    · rw [hqq]; simp [Q8List]
    · rw [h_qz_q]; simp [Q8List]
    · rw [h_pq_q]; simp [Q8List]
    · rw [h_pqz_q]; simp [Q8List]
  have mul_z : ∀ x, Q8List p q z x → Q8List p q z (x * z) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [Q8List]
    · rw [hzz]; simp [Q8List]
    · simp [Q8List]
    · rw [mul_assoc, hzz, mul_one]; simp [Q8List]
    · simp [Q8List]
    · rw [mul_assoc, hzz, mul_one]; simp [Q8List]
    · simp [Q8List]
    · rw [mul_assoc, hzz, mul_one]; simp [Q8List]
  intro u hu
  refine Subgroup.closure_induction_right ?_ ?_ ?_ hu
  · exact Or.inl rfl
  · intro x _ y hy ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]; exact mul_p x ih
    · rw [hy]; exact mul_q x ih
  · intro x _ y hy ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy, h_inv_p, ← mul_assoc]; exact mul_z (x * p) (mul_p x ih)
    · rw [hy, h_inv_q, ← mul_assoc]; exact mul_z (x * q) (mul_q x ih)

private lemma sq_eq_one_of_z {z : G} (hzz : z * z = 1) {u : G} (hu : u = 1 ∨ u = z) :
    u ^ 2 = 1 := by
  rcases hu with rfl | rfl
  · simp
  · simpa [pow_two] using hzz

private lemma Q8List_sq {p q z : G} (hpp : p * p = z) (hqq : q * q = z) (hzz : z * z = 1)
    (hzp : z * p = p * z) (hzq : z * q = q * z) (h_pq_p : (p * q) * p = q) :
    ∀ u, Q8List p q z u → (u = 1 ∨ u = z → u ^ 2 = 1) ∧ (u ≠ 1 → u ≠ z → u ^ 2 = z) := by
  have hsq : (p * q) * (p * q) = z := by rw [← mul_assoc, h_pq_p, hqq]
  have hzpq : z * (p * q) = (p * q) * z := q8_z_mul_mul hzp hzq
  intro u hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨sq_eq_one_of_z hzz, fun h1 _ => absurd rfl h1⟩
  · exact ⟨sq_eq_one_of_z hzz, fun _ h2 => absurd rfl h2⟩
  · exact ⟨sq_eq_one_of_z hzz, fun _ _ => by rw [pow_two, hpp]⟩
  · refine ⟨sq_eq_one_of_z hzz, fun _ _ => ?_⟩
    rw [pow_two, show (p * z) * (p * z) = p * (z * p) * z by group, hzp,
      show p * (p * z) * z = (p * p) * (z * z) by group, hpp, hzz, mul_one]
  · exact ⟨sq_eq_one_of_z hzz, fun _ _ => by rw [pow_two, hqq]⟩
  · refine ⟨sq_eq_one_of_z hzz, fun _ _ => ?_⟩
    rw [pow_two, show (q * z) * (q * z) = q * (z * q) * z by group, hzq,
      show q * (q * z) * z = (q * q) * (z * z) by group, hqq, hzz, mul_one]
  · exact ⟨sq_eq_one_of_z hzz, fun _ _ => by rw [pow_two, hsq]⟩
  · refine ⟨sq_eq_one_of_z hzz, fun _ _ => ?_⟩
    rw [pow_two, show ((p * q) * z) * ((p * q) * z) = (p * q) * (z * (p * q)) * z by group,
      hzpq, show (p * q) * ((p * q) * z) * z = ((p * q) * (p * q)) * (z * z) by group,
      hsq, hzz, mul_one]

theorem y6q8_z_central (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a * z = z * a := by
  intro a ha
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ ha
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact commute_self_sq h.a1_sq
    · exact commute_self_sq h.b1_sq
    · exact commute_self_sq h.a2_sq
    · exact commute_self_sq h.b2_sq
  · simp
  · intro x y _ _ ihx ihy
    rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
  · intro x _ ih
    calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * z) * x⁻¹ := by rw [← ih]
      _ = z * x⁻¹ := by group

theorem y6q8_U_elems (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ u ∈ (closure {a₁, b₁} : Subgroup G),
      u = 1 ∨ u = z ∨ u = a₁ ∨ u = a₁ * z ∨ u = b₁ ∨ u = b₁ * z ∨ u = a₁ * b₁ ∨
        u = a₁ * b₁ * z := by
  intro u hu
  have hlist : Q8List a₁ b₁ z u :=
    Q8List_of_closure (sq_a1 h) (sq_b1 h) (sq_z h) (z_comm_a1 h) (z_comm_b1 h)
      (b1a1_eq h) u hu
  simpa only [Q8List] using hlist

theorem y6q8_W_elems (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ w ∈ (closure {a₂, b₂} : Subgroup G),
      w = 1 ∨ w = z ∨ w = a₂ ∨ w = a₂ * z ∨ w = b₂ ∨ w = b₂ * z ∨ w = a₂ * b₂ ∨
        w = a₂ * b₂ * z := by
  intro w hw
  have hlist : Q8List a₂ b₂ z w :=
    Q8List_of_closure (sq_a2 h) (sq_b2 h) (sq_z h) (z_comm_a2 h) (z_comm_b2 h)
      (b2a2_eq h) w hw
  simpa only [Q8List] using hlist

theorem y6q8_sq_U (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ u ∈ (closure {a₁, b₁} : Subgroup G), (u = 1 ∨ u = z → u ^ 2 = 1) ∧
      (u ≠ 1 → u ≠ z → u ^ 2 = z) := by
  intro u hu
  exact Q8List_sq (sq_a1 h) (sq_b1 h) (sq_z h) (z_comm_a1 h) (z_comm_b1 h)
    (q8_pq_p (sq_a1 h) (z_comm_a1 h) (sq_z h) (b1a1_eq h)) u
    (Q8List_of_closure (sq_a1 h) (sq_b1 h) (sq_z h) (z_comm_a1 h) (z_comm_b1 h)
      (b1a1_eq h) u hu)

theorem y6q8_sq_W (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ w ∈ (closure {a₂, b₂} : Subgroup G), (w = 1 ∨ w = z → w ^ 2 = 1) ∧
      (w ≠ 1 → w ≠ z → w ^ 2 = z) := by
  intro w hw
  exact Q8List_sq (sq_a2 h) (sq_b2 h) (sq_z h) (z_comm_a2 h) (z_comm_b2 h)
    (q8_pq_p (sq_a2 h) (z_comm_a2 h) (sq_z h) (b2a2_eq h)) w
    (Q8List_of_closure (sq_a2 h) (sq_b2 h) (sq_z h) (z_comm_a2 h) (z_comm_b2 h)
      (b2a2_eq h) w hw)

end CFSG.OddStandard.HigherRank.YamadaG23

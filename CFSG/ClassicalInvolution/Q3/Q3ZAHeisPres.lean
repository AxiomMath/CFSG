module

public import CFSG.ClassicalInvolution.Q3.Q3ZACalc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped commutatorElement

theorem three_eq_zero_f3 : (3 : F3) = 0 := by
  have : CharP F3 3 := inferInstance
  exact_mod_cast CharP.cast_eq_zero F3 3

theorem one_ne_neg_one_f3 : (1 : F3) ≠ -1 := by
  intro h
  have h2 : (2 : F3) = 0 := by linear_combination h
  have h3 := three_eq_zero_f3
  have : (1 : F3) = 0 := by linear_combination h3 - h2
  exact one_ne_zero this

section Pow

variable {G : Type} [Group G]

open scoped Classical in
@[expose] noncomputable def pw (g : G) (x : F3) : G :=
  if x = 0 then 1 else if x = 1 then g else g⁻¹

theorem pw_zero (g : G) : pw g 0 = 1 := by simp [pw]

theorem pw_one (g : G) : pw g 1 = g := by simp [pw]

theorem pw_neg_one (g : G) : pw g (-1) = g⁻¹ := by
  have h := one_ne_neg_one_f3
  simp [pw, h.symm]

theorem pw_mem (g : G) (x : F3) : pw g x = 1 ∨ pw g x = g ∨ pw g x = g⁻¹ := by
  rcases eq_zero_or_one_or_neg_one_f3 x with rfl | rfl | rfl
  · exact Or.inl (pw_zero g)
  · exact Or.inr (Or.inl (pw_one g))
  · exact Or.inr (Or.inr (pw_neg_one g))

theorem pw_add {g : G} (hg : g ^ 3 = 1) (x y : F3) : pw g (x + y) = pw g x * pw g y := by
  have h3 := three_eq_zero_f3
  have e1 : (1 : F3) + 1 = -1 := by linear_combination h3
  have e2 : (-1 : F3) + -1 = 1 := by linear_combination (-1 : F3) * h3
  have hg' : g * g * g = 1 := by rw [← pow_three']; exact hg
  have hg2 : g * g = g⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hg')).symm
  rcases eq_zero_or_one_or_neg_one_f3 x with rfl | rfl | rfl <;>
    rcases eq_zero_or_one_or_neg_one_f3 y with rfl | rfl | rfl
  · simp [pw_zero]
  · simp [pw_zero]
  · simp [pw_zero]
  · simp [pw_zero]
  · rw [e1, pw_neg_one, pw_one, hg2]
  · rw [add_neg_cancel, pw_zero, pw_one, pw_neg_one, mul_inv_cancel]
  · simp [pw_zero]
  · rw [neg_add_cancel, pw_zero, pw_one, pw_neg_one, inv_mul_cancel]
  · rw [e2, pw_one, pw_neg_one, ← mul_inv_rev, hg2, inv_inv]

theorem commute_pw {g h : G} (hgh : Commute g h) (x y : F3) : Commute (pw g x) (pw h y) := by
  rcases pw_mem g x with h1 | h1 | h1 <;> rcases pw_mem h y with h2 | h2 | h2 <;> rw [h1, h2] <;>
    first
    | exact Commute.one_left _
    | exact Commute.one_right _
    | exact hgh
    | exact hgh.inv_left
    | exact hgh.inv_right
    | exact hgh.inv_inv

theorem pw_inv' (g : G) (x : F3) : pw g⁻¹ x = pw g (-x) := by
  rcases eq_zero_or_one_or_neg_one_f3 x with rfl | rfl | rfl
  · rw [neg_zero, pw_zero, pw_zero]
  · rw [pw_one, pw_neg_one]
  · rw [neg_neg, pw_neg_one, pw_one, inv_inv]

theorem pw_map {H : Type} [Group H] (c : G →* H) (g : G) (x : F3) : c (pw g x) = pw (c g) x := by
  rcases eq_zero_or_one_or_neg_one_f3 x with rfl | rfl | rfl
  · rw [pw_zero, pw_zero, map_one]
  · rw [pw_one, pw_one]
  · rw [pw_neg_one, pw_neg_one, map_inv]

theorem pw_mul_of_commute {g h : G} (hgh : Commute g h) (x : F3) :
    pw (g * h) x = pw g x * pw h x := by
  rcases eq_zero_or_one_or_neg_one_f3 x with rfl | rfl | rfl
  · rw [pw_zero, pw_zero, pw_zero, mul_one]
  · rw [pw_one, pw_one, pw_one]
  · rw [pw_neg_one, pw_neg_one, pw_neg_one, mul_inv_rev, hgh.inv_inv.eq]

theorem pw_comm_pair {e f z : G} (hze : Commute z e) (hzf : Commute z f) (hef : ⁅e, f⁆ = z)
    (u x : F3) : pw f u * pw e x = pw z (-(u * x)) * (pw e x * pw f u) := by
  have h0 : e * f = z * (f * e) := by
    have : e * f * e⁻¹ * f⁻¹ = z := hef
    calc e * f = (e * f * e⁻¹ * f⁻¹) * (f * e) := by group
      _ = z * (f * e) := by rw [this]
  have hconj : f * e * f⁻¹ = z⁻¹ * e := by
    calc f * e * f⁻¹ = z⁻¹ * (z * (f * e)) * f⁻¹ := by group
      _ = z⁻¹ * (e * f) * f⁻¹ := by rw [← h0]
      _ = z⁻¹ * e := by group
  have hzf' : f⁻¹ * z * f = z := by
    rw [mul_assoc, hzf.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hconj' : f⁻¹ * e * f = z * e := by
    calc f⁻¹ * e * f = f⁻¹ * (z * (z⁻¹ * e)) * f := by group
      _ = f⁻¹ * (z * (f * e * f⁻¹)) * f := by rw [hconj]
      _ = (f⁻¹ * z * f) * e := by group
      _ = z * e := by rw [hzf']
  rcases eq_zero_or_one_or_neg_one_f3 u with rfl | rfl | rfl
  · rw [pw_zero, zero_mul, neg_zero, pw_zero, one_mul, mul_one, one_mul]
  · have key : f * pw e x = (f * pw e x * f⁻¹) * f := by group
    have hc : f * pw e x * f⁻¹ = pw (f * e * f⁻¹) x := by
      have := pw_map (MulAut.conj f).toMonoidHom e x
      simpa [MulAut.conj_apply] using this
    rw [pw_one, key, hc, hconj, pw_mul_of_commute hze.inv_left x, pw_inv', one_mul, mul_assoc]
  · have key : f⁻¹ * pw e x = (f⁻¹ * pw e x * f) * f⁻¹ := by group
    have hc : f⁻¹ * pw e x * f = pw (f⁻¹ * e * f) x := by
      have := pw_map (MulAut.conj f⁻¹).toMonoidHom e x
      simpa [MulAut.conj_apply] using this
    rw [pw_neg_one, key, hc, hconj', pw_mul_of_commute hze x, neg_mul, one_mul, neg_neg, mul_assoc]

theorem pw_pair_mul {e f z : G} (he : e ^ 3 = 1) (hf : f ^ 3 = 1) (hze : Commute z e)
    (hzf : Commute z f) (hef : ⁅e, f⁆ = z) (a b c d : F3) :
    pw e a * pw f b * (pw e c * pw f d) = pw z (-(b * c)) * (pw e (a + c) * pw f (b + d)) := by
  have h := pw_comm_pair hze hzf hef b c
  have hz1 : Commute (pw e a) (pw z (-(b * c))) := (commute_pw hze.symm a _)
  calc pw e a * pw f b * (pw e c * pw f d) = pw e a * (pw f b * pw e c) * pw f d := by
        simp only [mul_assoc]
    _ = pw e a * (pw z (-(b * c)) * (pw e c * pw f b)) * pw f d := by rw [h]
    _ = pw z (-(b * c)) * (pw e a * pw e c * (pw f b * pw f d)) := by
        rw [hz1.left_comm]
        simp only [mul_assoc]
    _ = pw z (-(b * c)) * (pw e (a + c) * pw f (b + d)) := by rw [← pw_add he, ← pw_add hf]

end Pow

section Pres

variable {G : Type} [Group G]

structure HeisRels (z e0 e1 f0 f1 : G) : Prop where
  z_e0 : Commute z e0
  z_e1 : Commute z e1
  z_f0 : Commute z f0
  z_f1 : Commute z f1
  pow_z : z ^ 3 = 1
  pow_e0 : e0 ^ 3 = 1
  pow_e1 : e1 ^ 3 = 1
  pow_f0 : f0 ^ 3 = 1
  pow_f1 : f1 ^ 3 = 1
  comm_0 : ⁅e0, f0⁆ = z
  comm_1 : ⁅e1, f1⁆ = z
  e0_e1 : Commute e0 e1
  f0_f1 : Commute f0 f1
  e0_f1 : Commute e0 f1
  e1_f0 : Commute e1 f0

theorem form_V4 (v w : V4) : form v w = v (Sum.inl 0) * w (Sum.inr 0) +
    v (Sum.inl 1) * w (Sum.inr 1) - v (Sum.inr 0) * w (Sum.inl 0) -
    v (Sum.inr 1) * w (Sum.inl 1) := by
  simp only [form_apply, Fintype.sum_sum_type, Fin.sum_univ_two, par_inl, par_inr, sgn_inl,
    sgn_inr]
  ring

@[expose] noncomputable def hp (e f : G) (x u : F3) : G := pw e x * pw f u

theorem move4 {A D B C E F : G} (hDB : Commute D B) (hDC : Commute D C) (hCE : Commute C E) :
    A * (B * C) * (D * (E * F)) = A * D * (B * E * (C * F)) := by
  calc A * (B * C) * (D * (E * F)) = A * (B * (C * (D * (E * F)))) := by simp only [mul_assoc]
    _ = A * (B * (D * (C * (E * F)))) := by rw [hDC.symm.left_comm]
    _ = A * (D * (B * (C * (E * F)))) := by rw [hDB.symm.left_comm]
    _ = A * (D * (B * (E * (C * F)))) := by rw [hCE.left_comm]
    _ = A * D * (B * E * (C * F)) := by simp only [mul_assoc]

@[expose] noncomputable def heisNF (z e0 e1 f0 f1 : G) (m : Heis) : G :=
  pw z (m.c - 2 * (m.v (Sum.inl 0) * m.v (Sum.inr 0) + m.v (Sum.inl 1) * m.v (Sum.inr 1))) *
    (hp e0 f0 (m.v (Sum.inl 0)) (m.v (Sum.inr 0)) * hp e1 f1 (m.v (Sum.inl 1)) (m.v (Sum.inr 1)))

theorem heisNF_mul {z e0 e1 f0 f1 : G} (h : HeisRels z e0 e1 f0 f1) (m m' : Heis) :
    heisNF z e0 e1 f0 f1 (m * m') = heisNF z e0 e1 f0 f1 m * heisNF z e0 e1 f0 f1 m' := by
  have hZ0 : ∀ s x u, Commute (pw z s) (hp e0 f0 x u) := fun s x u =>
    (commute_pw h.z_e0 s x).mul_right (commute_pw h.z_f0 s u)
  have hZ1 : ∀ s y w, Commute (pw z s) (hp e1 f1 y w) := fun s y w =>
    (commute_pw h.z_e1 s y).mul_right (commute_pw h.z_f1 s w)
  have hX : ∀ y w x u, Commute (hp e1 f1 y w) (hp e0 f0 x u) := fun y w x u =>
    ((commute_pw h.e0_e1.symm y x).mul_right (commute_pw h.e1_f0 y u)).mul_left
      ((commute_pw h.e0_f1.symm w x).mul_right (commute_pw h.f0_f1.symm w u))
  have hp0 : ∀ a b c d, hp e0 f0 a b * hp e0 f0 c d =
      pw z (-(b * c)) * hp e0 f0 (a + c) (b + d) := fun a b c d =>
    pw_pair_mul h.pow_e0 h.pow_f0 h.z_e0 h.z_f0 h.comm_0 a b c d
  have hp1 : ∀ a b c d, hp e1 f1 a b * hp e1 f1 c d =
      pw z (-(b * c)) * hp e1 f1 (a + c) (b + d) := fun a b c d =>
    pw_pair_mul h.pow_e1 h.pow_f1 h.z_e1 h.z_f1 h.comm_1 a b c d
  have hZ4 : ∀ (s1 s2 a b : F3) (Q : G),
      pw z s1 * pw z s2 * (pw z a * (pw z b * Q)) = pw z (s1 + s2 + a + b) * Q := by
    intro s1 s2 a b Q
    rw [pw_add h.pow_z (s1 + s2 + a) b, pw_add h.pow_z (s1 + s2) a, pw_add h.pow_z s1 s2]
    simp only [mul_assoc]
  rcases m with ⟨c, v⟩
  rcases m' with ⟨c', v'⟩
  simp only [heisNF, Heis.mul_def, Pi.add_apply]
  rw [form_V4]
  generalize v (Sum.inl 0) = x
  generalize v (Sum.inl 1) = y
  generalize v (Sum.inr 0) = u
  generalize v (Sum.inr 1) = w
  generalize v' (Sum.inl 0) = x'
  generalize v' (Sum.inl 1) = y'
  generalize v' (Sum.inr 0) = u'
  generalize v' (Sum.inr 1) = w'
  rw [move4 (hZ0 _ _ _) (hZ1 _ _ _) (hX _ _ _ _), hp0, hp1]
  have e2 : pw z (-(u * x')) * hp e0 f0 (x + x') (u + u') *
      (pw z (-(w * y')) * hp e1 f1 (y + y') (w + w')) =
      pw z (-(u * x')) * (pw z (-(w * y')) * (hp e0 f0 (x + x') (u + u') *
        hp e1 f1 (y + y') (w + w'))) := by
    rw [mul_assoc, (hZ0 _ _ _).symm.left_comm]
  rw [e2, hZ4]
  have hE : c + c' + 2 * (x * u' + y * w' - u * x' - w * y') -
      2 * ((x + x') * (u + u') + (y + y') * (w + w')) =
      c - 2 * (x * u + y * w) + (c' - 2 * (x' * u' + y' * w')) + -(u * x') + -(w * y') := by
    linear_combination (-(u * x') - w * y') * three_eq_zero_f3
  rw [hE]

theorem exists_hom_of_rels {z e0 e1 f0 f1 : G} (h : HeisRels z e0 e1 f0 f1) :
    ∃ φ : Heis →* G, φ Heis.center = z ∧ φ (Heis.vec bE0) = e0 ∧ φ (Heis.vec bE1) = e1 ∧
      φ (Heis.vec bF0) = f0 ∧ φ (Heis.vec bF1) = f1 := by
  refine ⟨{ toFun := heisNF z e0 e1 f0 f1, map_one' := ?_, map_mul' := heisNF_mul h },
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [heisNF, Heis.one_def, hp, pw_zero]
  · simp [heisNF, Heis.center, hp, pw_zero, pw_one]
  · simp [heisNF, Heis.vec, hp, pw_zero, pw_one]
  · simp [heisNF, Heis.vec, hp, pw_zero, pw_one]
  · simp [heisNF, Heis.vec, hp, pw_zero, pw_one]
  · simp [heisNF, Heis.vec, hp, pw_zero, pw_one]

end Pres

end CFSG.ClassicalInvolution.Q3.Q3ZA

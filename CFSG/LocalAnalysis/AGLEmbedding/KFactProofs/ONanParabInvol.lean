module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

theorem braid_of_rels {R : Type*} [Ring R] {a b : R} (ha2 : a + a = 0) (hb2 : b + b = 0)
    (ha : a * a = 0) (hb : b * b = 0) (haba : a * b * a = a) (hbab : b * a * b = b) :
    (1 + a) * (1 + a) = 1 ∧ (1 + b) * (1 + b) = 1 ∧
      (1 + a) * (1 + b) * (1 + a) = (1 + b) * (1 + a) * (1 + b) ∧
      (1 + a) * (1 + b) * (1 + a) = 1 + b + b * a + a * b + a := by
  have e1 : (1 + a) * (1 + a) = 1 + (a + a) + a * a := by noncomm_ring
  have e2 : (1 + b) * (1 + b) = 1 + (b + b) + b * b := by noncomm_ring
  have e3 : (1 + a) * (1 + b) * (1 + a) =
      1 + (a + a) + a * a + b + b * a + a * b + a * b * a := by noncomm_ring
  have e4 : (1 + b) * (1 + a) * (1 + b) =
      1 + (b + b) + b * b + a + a * b + b * a + b * a * b := by noncomm_ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, ha2, ha]
    simp
  · rw [e2, hb2, hb]
    simp
  · rw [e3, e4, ha2, hb2, ha, hb, haba, hbab]
    abel
  · rw [e3, ha2, ha, haba]
    abel

theorem cube_eq_one_of_braid {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxyx : x * y * x = y * x * y) : (x * y) ^ 3 = 1 := by
  calc (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (x * y * x) * (x * y * x) := by rw [hxyx]
    _ = x * y * (x * x) * y * x := by simp only [mul_assoc]
    _ = 1 := by rw [hx, mul_one, mul_assoc x y y, hy, mul_one, hx]

theorem braid_of_rankOneRels {G : Type*} [Group G] {k : Type*} [Field k] (h2 : (1 : k) + 1 = 0)
    (R : RankOneRels G k) :
    R.x 1 * R.x 1 = 1 ∧ R.y 1 * R.y 1 = 1 ∧ R.x 1 * R.y 1 * R.x 1 = R.y 1 * R.x 1 * R.y 1 := by
  have hneg : (-1 : k) = 1 := neg_eq_of_add_eq_zero_right h2
  have hx2 : R.x 1 * R.x 1 = 1 := by rw [← R.x_add, h2, R.x_zero]
  have hy2 : R.y 1 * R.y 1 = 1 := by rw [← R.y_add, h2, R.y_zero]
  refine ⟨hx2, hy2, ?_⟩
  have hc := R.conj_x 1 one_ne_zero 1
  simp only [inv_one, one_pow, mul_one, hneg] at hc
  rw [mul_inv_eq_iff_eq_mul] at hc
  have e1 : R.x 1 * R.y 1 * R.x 1 * R.x 1 = R.x 1 * R.y 1 := by
    rw [mul_assoc (R.x 1 * R.y 1) (R.x 1) (R.x 1), hx2, mul_one]
  rw [e1] at hc
  calc R.x 1 * R.y 1 * R.x 1 = R.y 1 * (R.x 1 * R.y 1 * R.x 1) * R.x 1 := by rw [← hc]
    _ = R.y 1 * (R.x 1 * R.y 1) * (R.x 1 * R.x 1) := by simp only [mul_assoc]
    _ = R.y 1 * R.x 1 * R.y 1 := by rw [hx2, mul_one, mul_assoc]

section Node

variable {K : Type*} [Group K]

theorem HasOrderThree.of_involutions {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H) {i : Fin D.rank} {x y : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) (hy : y ∈ D.rootGroup (-Pi.single i 1)) (hx1 : x ≠ 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hbraid : x * y * x = y * x * y) :
    HasOrderThree D i := by
  refine ⟨x, hx, y, hy, cube_eq_one_of_braid hx2 hy2 hbraid, x, fun h => ?_⟩
  have h1 : x * y * x = y := by rw [h, ← mul_assoc, hx2, one_mul]
  have h2 : y * x * y = y := hbraid ▸ h1
  have h3 : y * x = 1 := mul_eq_right.1 h2
  have h4 : x = y := by
    rw [eq_inv_of_mul_eq_one_right h3, inv_eq_of_mul_eq_one_right hy2]
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  have hxU : x ∈ posUnipotent D := rootGroup_le_posUnipotent hα (ht_single_pos i) hx
  have hyU : y ∈ negUnipotent D := rootGroup_le_negUnipotent hα' (by
    rw [ht_neg]
    have := ht_single_pos (D := D) i
    omega) hy
  have hmem : x ∈ posUnipotent D ⊓ negUnipotent D := ⟨hxU, h4 ▸ hyU⟩
  rw [posUnipotent_inf_negUnipotent hext, Subgroup.mem_bot] at hmem
  exact hx1 hmem

end Node

end CFSG.AGLEmbedding.ParabHub

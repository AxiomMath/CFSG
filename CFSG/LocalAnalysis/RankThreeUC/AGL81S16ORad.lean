module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OPlane

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  quadMinus_apply polar_quadMinus)

section Rad

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

@[expose] def inZ (x : OW F) : Prop := ∀ i : Fin (3 - 1), x (Sum.inr (Sum.inl i)) = 0

theorem vec_decomp (x : OW F) :
    x = x (Sum.inl idx0) • eV F idx0 + x (Sum.inl idx1) • eV F idx1 +
      x (Sum.inr (Sum.inl idx0)) • fV F idx0 + x (Sum.inr (Sum.inl idx1)) • fV F idx1 +
      x (Sum.inr (Sum.inr 0)) • nVec F 0 + x (Sum.inr (Sum.inr 1)) • nVec F 1 := by
  have hne01 : idx0 ≠ idx1 := by decide
  ext k
  rcases k with i | i | j
  · fin_cases i <;> simp [Pi.single_apply, hne01, idx0, idx1]
  · fin_cases i <;> simp [Pi.single_apply, hne01, idx0, idx1]
  · fin_cases j <;> simp [Pi.single_apply]

theorem Q_coords (x : OW F) :
    quadMinus 3 F b c x = x (Sum.inl idx0) * x (Sum.inr (Sum.inl idx0)) +
      x (Sum.inl idx1) * x (Sum.inr (Sum.inl idx1)) + x (Sum.inr (Sum.inr 0)) ^ 2 +
      b * x (Sum.inr (Sum.inr 0)) * x (Sum.inr (Sum.inr 1)) + c * x (Sum.inr (Sum.inr 1)) ^ 2 := by
  rw [quadMinus_apply, Fin.sum_univ_two]
  rfl

theorem polar_coords (x y : OW F) :
    polar (quadMinus 3 F b c) x y = x (Sum.inl idx0) * y (Sum.inr (Sum.inl idx0)) +
      y (Sum.inl idx0) * x (Sum.inr (Sum.inl idx0)) +
      (x (Sum.inl idx1) * y (Sum.inr (Sum.inl idx1)) + y (Sum.inl idx1) * x (Sum.inr (Sum.inl idx1))) +
      b * (x (Sum.inr (Sum.inr 0)) * y (Sum.inr (Sum.inr 1)) +
        y (Sum.inr (Sum.inr 0)) * x (Sum.inr (Sum.inr 1))) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [polar_quadMinus, Fin.sum_univ_two]
  simp only [h2, zero_mul, add_zero]
  simp only [idx0, idx1, Fin.zero_eta, Fin.mk_one]

theorem gl_ext {g g' : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (h : ∀ x : OW F, gv g x = gv g' x) :
    g = g' := by
  apply Units.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simp only [gv, Matrix.mulVec_single_one] at this
  simpa using this

theorem gv_apply_decomp (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (x : OW F)
    (k : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) :
    gv g x k = x (Sum.inl idx0) * gv g (eV F idx0) k + x (Sum.inl idx1) * gv g (eV F idx1) k +
      x (Sum.inr (Sum.inl idx0)) * gv g (fV F idx0) k +
      x (Sum.inr (Sum.inl idx1)) * gv g (fV F idx1) k +
      x (Sum.inr (Sum.inr 0)) * gv g (nVec F 0) k + x (Sum.inr (Sum.inr 1)) * gv g (nVec F 1) k := by
  conv_lhs => rw [vec_decomp x]
  simp only [gv_add, gv_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

structure RadHyp (b c : F) (h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) : Prop where
  iso : ∀ v : OW F, quadMinus 3 F b c (gv h v) = quadMinus 3 F b c v
  fixE : ∀ i : Fin (3 - 1), gv h (eV F i) = eV F i
  trivV : ∀ (x : OW F) (i : Fin (3 - 1)), (gv h x - x) (Sum.inr (Sum.inl i)) = 0
  trivZ : ∀ z : OW F, inZ z → ∀ j : Fin 2, (gv h z - z) (Sum.inr (Sum.inr j)) = 0

@[expose] def nvec (F : Type) [Field F] (p q : F) : OW F := p • nVec F 0 + q • nVec F 1

theorem nvec_inl (p q : F) (i : Fin (3 - 1)) : nvec F p q (Sum.inl i) = 0 := by
  simp [nvec, Pi.single_apply]

theorem nvec_inr_inl (p q : F) (i : Fin (3 - 1)) : nvec F p q (Sum.inr (Sum.inl i)) = 0 := by
  simp [nvec, Pi.single_apply]

theorem nvec_n0 (p q : F) : nvec F p q (Sum.inr (Sum.inr 0)) = p := by
  simp [nvec, Pi.single_apply]

theorem nvec_n1 (p q : F) : nvec F p q (Sum.inr (Sum.inr 1)) = q := by
  simp [nvec, Pi.single_apply]

theorem quad_nvec (p q : F) : quadMinus 3 F b c (nvec F p q) = p ^ 2 + b * p * q + c * q ^ 2 := by
  rw [Q_coords]
  simp only [nvec_inl, nvec_inr_inl, nvec_n0, nvec_n1]
  ring

theorem polar_nvec_right (x : OW F) (p q : F) :
    polar (quadMinus 3 F b c) x (nvec F p q) =
      b * (x (Sum.inr (Sum.inr 0)) * q + p * x (Sum.inr (Sum.inr 1))) := by
  rw [polar_coords]
  simp only [nvec_inl, nvec_inr_inl, nvec_n0, nvec_n1]
  ring

theorem eich_nvec (i : Fin (3 - 1)) (p q : F) (x : OW F) :
    eichler (quadMinus 3 F b c) (eV F i) (nvec F p q) x = x +
      x (Sum.inr (Sum.inl i)) • nvec F p q +
      (b * (x (Sum.inr (Sum.inr 0)) * q + p * x (Sum.inr (Sum.inr 1))) +
        (p ^ 2 + b * p * q + c * q ^ 2) * x (Sum.inr (Sum.inl i))) • eV F i := by
  have hw : polar (quadMinus 3 F b c) (eV F i) (nvec F p q) = 0 := by
    rw [polar_comm, polar_e_right, nvec_inr_inl]
  rw [eichler_apply (quad_eV i) hw, polar_e_right, polar_nvec_right, quad_nvec, sub_eq_add_neg,
    ← neg_smul, CharTwo.neg_eq]

theorem eich_e1 (s : F) (x : OW F) :
    eichler (quadMinus 3 F b c) (eV F idx0) (s • eV F idx1) x =
      x + x (Sum.inr (Sum.inl idx0)) • (s • eV F idx1) + (s * x (Sum.inr (Sum.inl idx1))) • eV F idx0 := by
  have hne01 : idx0 ≠ idx1 := by decide
  have hw : polar (quadMinus 3 F b c) (eV F idx0) (s • eV F idx1) = 0 := by
    rw [polar_comm, polar_e_right]
    simp [Pi.single_apply, hne01]
  rw [eichler_apply (quad_eV idx0) hw, polar_e_right, polar_smul_right_eq, polar_e_right,
    map_smul_eq_sq, quad_eV idx1, mul_zero, zero_mul, add_zero, sub_eq_add_neg, ← neg_smul,
    CharTwo.neg_eq]

namespace RadHyp

variable {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hh : RadHyp b c h)
include hh

theorem f_coord (x : OW F) (i : Fin (3 - 1)) :
    gv h x (Sum.inr (Sum.inl i)) = x (Sum.inr (Sum.inl i)) := by
  have := hh.trivV x i
  simp only [Pi.sub_apply] at this
  exact sub_eq_zero.mp this

theorem n_coord (z : OW F) (hz : inZ z) (j : Fin 2) :
    gv h z (Sum.inr (Sum.inr j)) = z (Sum.inr (Sum.inr j)) := by
  have := hh.trivZ z hz j
  simp only [Pi.sub_apply] at this
  exact sub_eq_zero.mp this

theorem inZ_nVec (j : Fin 2) : inZ (nVec F j) := by
  intro i
  simp [Pi.single_apply]

theorem n_coord_nVec (j j' : Fin 2) :
    gv h (nVec F j) (Sum.inr (Sum.inr j')) = nVec F j (Sum.inr (Sum.inr j')) :=
  hh.n_coord _ (hh.inZ_nVec j) j'

theorem exists_params :
    ∃ v0 v1 u0 u1 : OW F,
      (∀ (x : OW F) (k : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2), gv h x k =
        x (Sum.inl idx0) * eV F idx0 k + x (Sum.inl idx1) * eV F idx1 k +
          x (Sum.inr (Sum.inl idx0)) * v0 k + x (Sum.inr (Sum.inl idx1)) * v1 k +
          x (Sum.inr (Sum.inr 0)) * u0 k + x (Sum.inr (Sum.inr 1)) * u1 k) ∧
      v0 (Sum.inr (Sum.inl idx0)) = 1 ∧ v0 (Sum.inr (Sum.inl idx1)) = 0 ∧
      v1 (Sum.inr (Sum.inl idx0)) = 0 ∧ v1 (Sum.inr (Sum.inl idx1)) = 1 ∧
      u0 (Sum.inr (Sum.inl idx0)) = 0 ∧ u0 (Sum.inr (Sum.inl idx1)) = 0 ∧
      u1 (Sum.inr (Sum.inl idx0)) = 0 ∧ u1 (Sum.inr (Sum.inl idx1)) = 0 ∧
      u0 (Sum.inr (Sum.inr 0)) = 1 ∧ u0 (Sum.inr (Sum.inr 1)) = 0 ∧
      u1 (Sum.inr (Sum.inr 0)) = 0 ∧ u1 (Sum.inr (Sum.inr 1)) = 1 ∧
      quadMinus 3 F b c v0 = 0 ∧ quadMinus 3 F b c v1 = 0 ∧
      polar (quadMinus 3 F b c) v0 v1 = 0 ∧
      polar (quadMinus 3 F b c) u0 v0 = 0 ∧ polar (quadMinus 3 F b c) u0 v1 = 0 ∧
      polar (quadMinus 3 F b c) u1 v0 = 0 ∧ polar (quadMinus 3 F b c) u1 v1 = 0 := by
  have hne01 : idx0 ≠ idx1 := by decide
  refine ⟨gv h (fV F idx0), gv h (fV F idx1), gv h (nVec F 0), gv h (nVec F 1), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x k
    rw [gv_apply_decomp, hh.fixE, hh.fixE]
  · rw [hh.f_coord]; simp [Pi.single_apply]
  · rw [hh.f_coord]; simp [Pi.single_apply, hne01]
  · rw [hh.f_coord]; simp [Pi.single_apply, hne01]
  · rw [hh.f_coord]; simp [Pi.single_apply]
  · rw [hh.f_coord]; simp [Pi.single_apply]
  · rw [hh.f_coord]; simp [Pi.single_apply]
  · rw [hh.f_coord]; simp [Pi.single_apply]
  · rw [hh.f_coord]; simp [Pi.single_apply]
  · rw [hh.n_coord_nVec]; simp [Pi.single_apply]
  · rw [hh.n_coord_nVec]; simp [Pi.single_apply]
  · rw [hh.n_coord_nVec]; simp [Pi.single_apply]
  · rw [hh.n_coord_nVec]; simp [Pi.single_apply]
  · rw [hh.iso]; exact quadMinus_single_inr idx0
  · rw [hh.iso]; exact quadMinus_single_inr idx1
  · rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]
  · rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]
  · rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]
  · rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]
  · rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]

end RadHyp

theorem eV_self (i : Fin (3 - 1)) : eV F i (Sum.inl i) = 1 := by simp

theorem eV_ne {i k : Fin (3 - 1)} (hk : k ≠ i) : eV F i (Sum.inl k) = 0 := by
  simp [Pi.single_apply, hk]

theorem eV_inr (i : Fin (3 - 1)) (m : Fin (3 - 1) ⊕ Fin 2) : eV F i (Sum.inr m) = 0 := by
  simp

theorem nVec_inl (j : Fin 2) (i : Fin (3 - 1)) : nVec F j (Sum.inl i) = 0 := by
  simp [Pi.single_apply]

theorem nVec_inr_inl (j : Fin 2) (i : Fin (3 - 1)) : nVec F j (Sum.inr (Sum.inl i)) = 0 := by
  simp [Pi.single_apply]

theorem nVec_00 : nVec F 0 (Sum.inr (Sum.inr 0)) = 1 := by simp

theorem nVec_01 : nVec F 0 (Sum.inr (Sum.inr 1)) = 0 := by simp [Pi.single_apply]

theorem nVec_10 : nVec F 1 (Sum.inr (Sum.inr 0)) = 0 := by simp [Pi.single_apply]

theorem nVec_11 : nVec F 1 (Sum.inr (Sum.inr 1)) = 1 := by simp

theorem rad_eq_eichler_prod (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hh : RadHyp b c h) :
    ∃ A₁ ∈ StatedOmega (StatedQuadMinus 3 F b c), ∃ A₂ ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ A₃ ∈ StatedOmega (StatedQuadMinus 3 F b c), h = A₁ * A₂ * A₃ := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hne01 : idx0 ≠ idx1 := by decide
  have hne10 : idx1 ≠ idx0 := by decide
  obtain ⟨v0, v1, u0, u1, hcoord, v0f0, v0f1, v1f0, v1f1, u0f0, u0f1, u1f0, u1f1, u0n0, u0n1, u1n0,
    u1n1, hQ0, hQ1, hP01, hP00, hP01', hP10, hP11⟩ := hh.exists_params
  have R1 : v0 (Sum.inl idx0) = v0 (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v0 (Sum.inr (Sum.inr 0)) * v0 (Sum.inr (Sum.inr 1)) + c * v0 (Sum.inr (Sum.inr 1)) ^ 2 := by
    rw [Q_coords, v0f0, v0f1] at hQ0
    linear_combination hQ0 - (v0 (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v0 (Sum.inr (Sum.inr 0)) * v0 (Sum.inr (Sum.inr 1)) + c * v0 (Sum.inr (Sum.inr 1)) ^ 2) * h2
  have R2 : v1 (Sum.inl idx1) = v1 (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v1 (Sum.inr (Sum.inr 0)) * v1 (Sum.inr (Sum.inr 1)) + c * v1 (Sum.inr (Sum.inr 1)) ^ 2 := by
    rw [Q_coords, v1f0, v1f1] at hQ1
    linear_combination hQ1 - (v1 (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v1 (Sum.inr (Sum.inr 0)) * v1 (Sum.inr (Sum.inr 1)) + c * v1 (Sum.inr (Sum.inr 1)) ^ 2) * h2
  have R3 : v1 (Sum.inl idx0) = v0 (Sum.inl idx1) + b * (v0 (Sum.inr (Sum.inr 0)) *
      v1 (Sum.inr (Sum.inr 1)) + v1 (Sum.inr (Sum.inr 0)) * v0 (Sum.inr (Sum.inr 1))) := by
    rw [polar_coords, v0f0, v0f1, v1f0, v1f1] at hP01
    linear_combination hP01 - (v0 (Sum.inl idx1) + b * (v0 (Sum.inr (Sum.inr 0)) *
      v1 (Sum.inr (Sum.inr 1)) + v1 (Sum.inr (Sum.inr 0)) * v0 (Sum.inr (Sum.inr 1)))) * h2
  have R4a : u0 (Sum.inl idx0) = b * v0 (Sum.inr (Sum.inr 1)) := by
    rw [polar_coords, u0f0, u0f1, v0f0, v0f1, u0n0, u0n1] at hP00
    linear_combination hP00 - b * v0 (Sum.inr (Sum.inr 1)) * h2
  have R4b : u1 (Sum.inl idx0) = b * v0 (Sum.inr (Sum.inr 0)) := by
    rw [polar_coords, u1f0, u1f1, v0f0, v0f1, u1n0, u1n1] at hP10
    linear_combination hP10 - b * v0 (Sum.inr (Sum.inr 0)) * h2
  have R4c : u0 (Sum.inl idx1) = b * v1 (Sum.inr (Sum.inr 1)) := by
    rw [polar_coords, u0f0, u0f1, v1f0, v1f1, u0n0, u0n1] at hP01'
    linear_combination hP01' - b * v1 (Sum.inr (Sum.inr 1)) * h2
  have R4d : u1 (Sum.inl idx1) = b * v1 (Sum.inr (Sum.inr 0)) := by
    rw [polar_coords, u1f0, u1f1, v1f0, v1f1, u1n0, u1n1] at hP11
    linear_combination hP11 - b * v1 (Sum.inr (Sum.inr 0)) * h2
  obtain ⟨A₁, hA₁, hA₁x⟩ := eichler_mem_statedOmega hirr (eV F idx0)
    (nvec F (v0 (Sum.inr (Sum.inr 0))) (v0 (Sum.inr (Sum.inr 1))))
  obtain ⟨A₂, hA₂, hA₂x⟩ := eichler_mem_statedOmega hirr (eV F idx1)
    (nvec F (v1 (Sum.inr (Sum.inr 0))) (v1 (Sum.inr (Sum.inr 1))))
  obtain ⟨A₃, hA₃, hA₃x⟩ := eichler_mem_statedOmega hirr (eV F idx0)
    (v0 (Sum.inl idx1) • eV F idx1)
  refine ⟨A₁, hA₁, A₂, hA₂, A₃, hA₃, gl_ext fun x => ?_⟩
  have e1 : ∀ y, gv A₁ y = eichler (quadMinus 3 F b c) (eV F idx0)
      (nvec F (v0 (Sum.inr (Sum.inr 0))) (v0 (Sum.inr (Sum.inr 1)))) y := hA₁x
  have e2 : ∀ y, gv A₂ y = eichler (quadMinus 3 F b c) (eV F idx1)
      (nvec F (v1 (Sum.inr (Sum.inr 0))) (v1 (Sum.inr (Sum.inr 1)))) y := hA₂x
  have e3 : ∀ y, gv A₃ y = eichler (quadMinus 3 F b c) (eV F idx0)
      (v0 (Sum.inl idx1) • eV F idx1) y := hA₃x
  rw [gv_mul, gv_mul, e3, eich_e1, e2, eich_nvec, e1, eich_nvec]
  have hi : ∀ i : Fin (3 - 1), i = idx0 ∨ i = idx1 := by decide
  have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  funext k
  rw [hcoord]
  rcases k with i | i | j
  · rcases hi i with rfl | rfl
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_inl, nvec_inr_inl, nvec_n0, nvec_n1,
        eV_self, eV_ne hne10, eV_ne hne01, eV_inr, nVec_inl, nVec_inr_inl, nVec_00, nVec_01, nVec_10,
        nVec_11]
      linear_combination x (Sum.inr (Sum.inr 0)) * R4a + x (Sum.inr (Sum.inr 1)) * R4b +
        x (Sum.inr (Sum.inl idx0)) * R1 + x (Sum.inr (Sum.inl idx1)) * R3
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_inl, nvec_inr_inl, nvec_n0, nvec_n1,
        eV_self, eV_ne hne10, eV_ne hne01, eV_inr, nVec_inl, nVec_inr_inl, nVec_00, nVec_01, nVec_10,
        nVec_11]
      linear_combination x (Sum.inr (Sum.inr 0)) * R4c + x (Sum.inr (Sum.inr 1)) * R4d +
        x (Sum.inr (Sum.inl idx1)) * R2
  · rcases hi i with rfl | rfl
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_inl, nvec_inr_inl, nvec_n0, nvec_n1,
        eV_self, eV_ne hne10, eV_ne hne01, eV_inr, nVec_inl, nVec_inr_inl, nVec_00, nVec_01, nVec_10,
        nVec_11]
      linear_combination x (Sum.inr (Sum.inl idx0)) * v0f0 + x (Sum.inr (Sum.inl idx1)) * v1f0 +
        x (Sum.inr (Sum.inr 0)) * u0f0 + x (Sum.inr (Sum.inr 1)) * u1f0
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_inl, nvec_inr_inl, nvec_n0, nvec_n1,
        eV_self, eV_ne hne10, eV_ne hne01, eV_inr, nVec_inl, nVec_inr_inl, nVec_00, nVec_01, nVec_10,
        nVec_11]
      linear_combination x (Sum.inr (Sum.inl idx0)) * v0f1 + x (Sum.inr (Sum.inl idx1)) * v1f1 +
        x (Sum.inr (Sum.inr 0)) * u0f1 + x (Sum.inr (Sum.inr 1)) * u1f1
  · rcases hj j with rfl | rfl
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_inl, nvec_inr_inl, nvec_n0, nvec_n1,
        eV_self, eV_ne hne10, eV_ne hne01, eV_inr, nVec_inl, nVec_inr_inl, nVec_00, nVec_01, nVec_10,
        nVec_11]
      linear_combination x (Sum.inr (Sum.inr 0)) * u0n0 + x (Sum.inr (Sum.inr 1)) * u1n0
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_inl, nvec_inr_inl, nvec_n0, nvec_n1,
        eV_self, eV_ne hne10, eV_ne hne01, eV_inr, nVec_inl, nVec_inr_inl, nVec_00, nVec_01, nVec_10,
        nVec_11]
      linear_combination x (Sum.inr (Sum.inr 0)) * u0n1 + x (Sum.inr (Sum.inr 1)) * u1n1

theorem rad_mem_omega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hh : RadHyp b c h) :
    h ∈ StatedOmega (StatedQuadMinus 3 F b c) := by
  obtain ⟨A₁, hA₁, A₂, hA₂, A₃, hA₃, rfl⟩ := rad_eq_eichler_prod hirr hh
  exact mul_mem (mul_mem hA₁ hA₂) hA₃

end Rad

end CFSG.LocalAnalysis.RankThreeUC

module

public import CFSG.ClassicalInvolution.Q3.Q3ZAModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups commutatorElement
open Matrix

theorem eq_zero_or_one_or_neg_one_f3 (a : F3) : a = 0 ∨ a = 1 ∨ a = -1 := by
  classical
  have : Fintype F3 := Fintype.ofFinite _
  have hcard : Fintype.card F3 = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact CFSG.ClassicalInvolution.Q3.Q3W.card_gf3
  have h := FiniteField.pow_card a
  rw [hcard] at h
  have h3 : a * (a - 1) * (a + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact Or.inl h5
    · exact Or.inr (Or.inl (sub_eq_zero.mp h5))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h4))

section Additive

variable {G : Type} [Group G]

theorem add_map_zero {f : F3 → G} (hf : ∀ s t, f (s + t) = f s * f t) : f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem add_map_neg {f : F3 → G} (hf : ∀ s t, f (s + t) = f s * f t) (s : F3) :
    f (-s) = (f s)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hf, neg_add_cancel, add_map_zero hf]

theorem eq_of_add_of_one {f g : F3 → G} (hf : ∀ s t, f (s + t) = f s * f t)
    (hg : ∀ s t, g (s + t) = g s * g t) (h1 : f 1 = g 1) : f = g := by
  funext u
  rcases eq_zero_or_one_or_neg_one_f3 u with rfl | rfl | rfl
  · rw [add_map_zero hf, add_map_zero hg]
  · exact h1
  · rw [add_map_neg hf, add_map_neg hg, h1]

end Additive

section Roots

variable {G : Type} [Group G]

@[expose] noncomputable def rU (θ : StatedSp 2 F3 →* G) (u : F3) : G := θ (sb (usl u))

@[expose] noncomputable def rL (θ : StatedSp 2 F3 →* G) (u : F3) : G := θ (sb (lsl u))

theorem rU_add (θ : StatedSp 2 F3 →* G) (s t : F3) : rU θ (s + t) = rU θ s * rU θ t := by
  simp only [rU, usl_add, map_mul]

theorem rL_add (θ : StatedSp 2 F3 →* G) (s t : F3) : rL θ (s + t) = rL θ s * rL θ t := by
  simp only [rL, lsl_add, map_mul]

end Roots

theorem form_E0_E1 : form bE0 bE1 = 0 := by
  simp [form_apply, Fintype.sum_sum_type, Pi.single_apply]

theorem form_E1_E0 : form bE1 bE0 = 0 := by
  simp [form_apply, Fintype.sum_sum_type, Pi.single_apply]

theorem form_F0_F1 : form bF0 bF1 = 0 := by
  simp [form_apply, Fintype.sum_sum_type, Pi.single_apply]

theorem form_F1_F0 : form bF1 bF0 = 0 := by
  simp [form_apply, Fintype.sum_sum_type, Pi.single_apply]

theorem form_EE (a b c d : F3) : form (a • bE0 + b • bE1) (c • bE0 + d • bE1) = 0 := by
  simp [form_add_left, form_add_right, form_smul_left, form_smul_right, form_self, form_E0_E1,
    form_E1_E0]

theorem form_FF (a b c d : F3) : form (a • bF0 + b • bF1) (c • bF0 + d • bF1) = 0 := by
  simp [form_add_left, form_add_right, form_smul_left, form_smul_right, form_self, form_F0_F1,
    form_F1_F0]

section PhCalc

variable {G : Type} [Group G]

@[expose] noncomputable def ph (φ : Heis →* G) (v : V4) : G := φ (Heis.vec v)

theorem vec_inv (v : V4) : (Heis.vec v)⁻¹ = Heis.vec (-v) := by
  refine Heis.ext ?_ rfl
  simp [Heis.inv_def, Heis.vec]

theorem ph_neg (φ : Heis →* G) (v : V4) : ph φ (-v) = (ph φ v)⁻¹ := by
  rw [ph, ph, ← map_inv, vec_inv]

theorem ph_zero (φ : Heis →* G) : ph φ 0 = 1 := by
  have h : Heis.vec 0 = 1 := rfl
  rw [ph, h, map_one]

theorem ph_mul (φ : Heis →* G) {v w : V4} (h : form v w = 0) :
    ph φ v * ph φ w = ph φ (v + w) := by
  rw [ph, ph, ph, ← map_mul, Heis.vec_mul_vec, h, mul_zero]
  rfl

theorem ph_comm (φ : Heis →* G) {v w : V4} (h : form v w = 0) : Commute (ph φ v) (ph φ w) := by
  have h' : form w v = 0 := by rw [form_antisymm, h, neg_zero]
  show ph φ v * ph φ w = ph φ w * ph φ v
  rw [ph_mul φ h, ph_mul φ h', add_comm]

theorem ph_smul_add (φ : Heis →* G) (v : V4) (s t : F3) :
    ph φ ((s + t) • v) = ph φ (s • v) * ph φ (t • v) := by
  have h : form (s • v) (t • v) = 0 := by
    rw [form_smul_left, form_smul_right, form_self, mul_zero, mul_zero]
  rw [add_smul, ph_mul φ h]

variable {θ : StatedSp 2 F3 →* G} {φ : Heis →* G}

theorem conj_ph (hact : ∀ (s : StatedSp 2 F3) (x : Heis), θ s * φ x * (θ s)⁻¹ = φ (heisAct s x))
    (r : StatedSp 2 F3) (v : V4) : θ r * ph φ v * (θ r)⁻¹ = ph φ (mat 2 F3 r *ᵥ v) :=
  hact r (Heis.vec v)

theorem comm_ph_theta
    (hact : ∀ (s : StatedSp 2 F3) (x : Heis), θ s * φ x * (θ s)⁻¹ = φ (heisAct s x))
    (r : StatedSp 2 F3) (v : V4) (hv : form v (mat 2 F3 r *ᵥ v) = 0) :
    ⁅ph φ v, θ r⁆ = ph φ (v - mat 2 F3 r *ᵥ v) := by
  have h1 : θ r * (ph φ v)⁻¹ * (θ r)⁻¹ = ph φ (-(mat 2 F3 r *ᵥ v)) := by
    rw [← ph_neg, conj_ph hact, Matrix.mulVec_neg]
  have h2 : form v (-(mat 2 F3 r *ᵥ v)) = 0 := by rw [Heis.form_neg_right', hv, neg_zero]
  calc ⁅ph φ v, θ r⁆ = ph φ v * (θ r * (ph φ v)⁻¹ * (θ r)⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ph φ v * ph φ (-(mat 2 F3 r *ᵥ v)) := by rw [h1]
    _ = ph φ (v - mat 2 F3 r *ᵥ v) := by rw [ph_mul φ h2, sub_eq_add_neg]

theorem commute_ph_theta
    (hact : ∀ (s : StatedSp 2 F3) (x : Heis), θ s * φ x * (θ s)⁻¹ = φ (heisAct s x))
    (r : StatedSp 2 F3) (v : V4) (hv : mat 2 F3 r *ᵥ v = v) : Commute (ph φ v) (θ r) := by
  have h := comm_ph_theta hact r v (by rw [hv]; exact form_self v)
  rw [hv, sub_self, ph_zero] at h
  exact commutatorElement_eq_one_iff_commute.mp h

end PhCalc

end CFSG.ClassicalInvolution.Q3.Q3ZA

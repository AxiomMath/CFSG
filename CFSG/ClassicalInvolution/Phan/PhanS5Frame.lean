module

public import CFSG.ClassicalInvolution.Phan.PhanS5Act
public import CFSG.ClassicalInvolution.Phan.PhanH5Frames
public import CFSG.ClassicalInvolution.Phan.PhanS4Std
public import CFSG.ClassicalInvolution.Phan.PhanS5Fld

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ClassicalInvolution.PhanB3.H (mk7 polar_mk7)

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem exists_sq_add_sq_neg_one' [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  classical
  have := Fintype.ofFinite F
  have hcard : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 : Polynomial F))
    (g := (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial F)) (by simp)
    (by rw [Polynomial.degree_X_pow_add_C (by norm_num)]; simp) hcard
  refine ⟨a, b, ?_⟩
  simp at h
  linear_combination h

section Vectors

@[expose] def conjV (x : W7 K) : W7 K := mapV D.τ x

theorem exists_c2 [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ c : K, c * D.τ c = -1 / 4 := by
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_neg_one' hodd
  refine ⟨(algebraMap F K a + algebraMap F K b * D.θ) / 2, ?_⟩
  have h1 : D.τ ((algebraMap F K a + algebraMap F K b * D.θ) / 2) =
      (algebraMap F K a - algebraMap F K b * D.θ) / 2 := by
    rw [map_div₀, map_add, map_mul, D.tau_alg, D.tau_alg, D.tau_theta]
    have : D.τ (2 : K) = 2 := map_ofNat D.τ 2
    rw [this]
    ring
  rw [h1]
  have hab' : (algebraMap F K a) ^ 2 + (algebraMap F K b) ^ 2 = -1 := by
    rw [← map_pow, ← map_pow, ← map_add, hab, map_neg, map_one]
  have e : (algebraMap F K a + algebraMap F K b * D.θ) *
      (algebraMap F K a - algebraMap F K b * D.θ) = -1 := by
    linear_combination hab' - (algebraMap F K b) ^ 2 * D.theta_sq
  rw [div_mul_div_comm, e]
  norm_num

@[expose] noncomputable def stdModel (h2 : (2 : K) ≠ 0) : Std.Model K where
  q := Nat.card F
  τ := D.τ
  κ := -2
  card_K := D.card_K
  tau_pow := D.tau_pow
  tau_tau := D.tau_tau
  κ_ne := neg_ne_zero.2 h2
  tau_κ := by rw [map_neg, map_ofNat]
  two_ne := h2

variable (c₂ : K)

@[expose] noncomputable def vB : Fin 3 ⊕ Fin 3 ⊕ Unit → W7 K :=
  Sum.elim
    ![mk7 (1 / 2) 0 0 (1 / 2) 0 0 (D.θ / 2), c₂ • mk7 0 1 D.θ 0 (-1) (-D.θ) 0,
      mk7 0 (1 / 2) (D.θ / 2) 0 (1 / 2) (D.θ / 2) 0]
    (Sum.elim
      ![mk7 (1 / 2) 0 0 (1 / 2) 0 0 (-(D.θ / 2)), D.τ c₂ • mk7 0 1 (-D.θ) 0 (-1) D.θ 0,
        mk7 0 (1 / 2) (-(D.θ / 2)) 0 (1 / 2) (-(D.θ / 2)) 0]
      fun _ => mk7 1 0 0 (-1) 0 0 0)

theorem polar_vB (h2 : (2 : K) ≠ 0) (hc : c₂ * D.τ c₂ = -1 / 4) (s t : Fin 3 ⊕ Fin 3 ⊕ Unit) :
    polar (quadOdd 3 K) (vB D c₂ s) (vB D c₂ t) =
      Std.bf (stdModel D h2) (Pi.single s 1) (Pi.single t 1) := by
  have hθ := D.theta_sq
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hc' : c₂ * D.τ c₂ * 4 = -1 := by rw [hc]; field_simp
  rcases s with i | i | u <;> rcases t with j | j | v <;>
    (try fin_cases i) <;> (try fin_cases j) <;>
    simp [vB, polar_mk7, Std.bf, Pi.single_apply, stdModel,
      CFSG.ClassicalInvolution.PhanB3.H.quad_mk7, QuadraticMap.map_smul] <;> field_simp <;>
    ring_nf <;> (try simp [hθ, hc]) <;> (try ring_nf)
  all_goals first
    | exact inv_mul_cancel₀ h4
    | linear_combination (-1) * hc'

end Vectors

section Theta

variable (c₂ : K)

@[expose] def swapIdx : Fin 3 ⊕ Fin 3 ⊕ Unit → Fin 3 ⊕ Fin 3 ⊕ Unit :=
  Sum.elim (fun i => .inr (.inl i)) (Sum.elim (fun i => .inl i) (fun u => .inr (.inr u)))

theorem swapIdx_swapIdx (s : Fin 3 ⊕ Fin 3 ⊕ Unit) : swapIdx (swapIdx s) = s := by
  rcases s with i | i | u <;> rfl

theorem tauV_apply (M : Std.Model K) (x : Std.Vec K) (s : Fin 3 ⊕ Fin 3 ⊕ Unit) :
    Std.tauV M x s = M.τ (x (swapIdx s)) := by
  rcases s with i | i | u <;> rfl

theorem conjV_vB (s : Fin 3 ⊕ Fin 3 ⊕ Unit) :
    conjV D (vB D c₂ s) = vB D c₂ (swapIdx s) := by
  have h2 : D.τ (2 : K) = 2 := map_ofNat D.τ 2
  funext r
  rcases s with i | i | u <;> rcases r with k | k | w <;> (try fin_cases i) <;>
    (try fin_cases k) <;>
    simp [conjV, mapV, vB, mk7, swapIdx, D.tau_theta, D.tau_tau, h2, map_div₀] <;>
    (try ring)

@[expose] noncomputable def ΘM : Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) (Fin 3 ⊕ Fin 3 ⊕ Unit) K :=
  Matrix.of fun r s => vB D c₂ s r

@[expose] noncomputable def Θ : Std.Vec K →ₗ[K] W7 K := (ΘM D c₂).mulVecLin

theorem Θ_apply (x : Std.Vec K) (r : Fin 3 ⊕ Fin 3 ⊕ Unit) :
    Θ D c₂ x r = ∑ s, vB D c₂ s r * x s := by
  simp [Θ, ΘM, Matrix.mulVec, dotProduct]

theorem Θ_single (s : Fin 3 ⊕ Fin 3 ⊕ Unit) : Θ D c₂ (Pi.single s 1) = vB D c₂ s := by
  funext r
  simp [Θ_apply, Pi.single_apply]

noncomputable def bfBil (M : Std.Model K) : LinearMap.BilinForm K (Std.Vec K) :=
  LinearMap.mk₂ K (Std.bf M) (Std.bf_add_left M) (fun c x y => by
    rw [Std.bf_smul_left, smul_eq_mul])
    (fun x y z => by
      rw [Std.bf_comm M x (y + z), Std.bf_add_left, Std.bf_comm M y x, Std.bf_comm M z x])
    (fun c x y => by
      rw [Std.bf_comm M x (c • y), Std.bf_smul_left, Std.bf_comm M y x, smul_eq_mul])

theorem polar_Θ (h2 : (2 : K) ≠ 0) (hc : c₂ * D.τ c₂ = -1 / 4) (x y : Std.Vec K) :
    polar (quadOdd 3 K) (Θ D c₂ x) (Θ D c₂ y) = Std.bf (stdModel D h2) x y := by
  have := LinearMap.BilinForm.ext_basis (Pi.basisFun K (Fin 3 ⊕ Fin 3 ⊕ Unit))
    (B := (polarBilin (quadOdd 3 K)).compl₁₂ (Θ D c₂) (Θ D c₂))
    (F₂ := bfBil (stdModel D h2)) (fun s t => by
      simp [Θ_single, polar_vB D c₂ h2 hc, bfBil, Pi.basisFun_apply])
  have h := congrArg (fun B => B x y) this
  simpa [bfBil, LinearMap.mk₂_apply] using h

theorem Θ_tauV (h2 : (2 : K) ≠ 0) (x : Std.Vec K) :
    Θ D c₂ (Std.tauV (stdModel D h2) x) = conjV D (Θ D c₂ x) := by
  funext r
  simp only [Θ_apply, conjV, mapV, map_sum, map_mul]
  refine Fintype.sum_equiv ⟨swapIdx, swapIdx, swapIdx_swapIdx, swapIdx_swapIdx⟩ _ _ fun s => ?_
  have h1 : D.τ (vB D c₂ (swapIdx s) r) = vB D c₂ s r := by
    have := congrFun (conjV_vB D c₂ (swapIdx s)) r
    rw [swapIdx_swapIdx] at this
    exact this
  simp only [Equiv.coe_fn_mk, h1, tauV_apply]
  rfl

theorem bf_single_inl (M : Std.Model K) (x : Std.Vec K) (j : Fin 3) :
    Std.bf M x (Pi.single (.inl j) 1) = x (.inr (.inl j)) := by
  simp [Std.bf, Pi.single_apply]

theorem bf_single_inr_inl (M : Std.Model K) (x : Std.Vec K) (j : Fin 3) :
    Std.bf M x (Pi.single (.inr (.inl j)) 1) = x (.inl j) := by
  simp [Std.bf, Pi.single_apply]

theorem bf_single_inr_inr (M : Std.Model K) (x : Std.Vec K) :
    Std.bf M x (Pi.single (.inr (.inr ())) 1) = M.κ * x (.inr (.inr ())) := by
  simp [Std.bf]

theorem Θ_injective (h2 : (2 : K) ≠ 0) (hc : c₂ * D.τ c₂ = -1 / 4) :
    Function.Injective (Θ D c₂) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have key : ∀ s, Std.bf (stdModel D h2) x (Pi.single s 1) = 0 := fun s => by
    rw [← polar_Θ D c₂ h2 hc, hx]
    simp
  funext s
  rcases s with j | j | u
  · have := key (.inr (.inl j))
    rwa [bf_single_inr_inl] at this
  · have := key (.inl j)
    rwa [bf_single_inl] at this
  · have := key (.inr (.inr ()))
    rw [bf_single_inr_inr] at this
    exact (mul_eq_zero.mp this).resolve_left (stdModel D h2).κ_ne

@[expose] noncomputable def ΘEquiv (h2 : (2 : K) ≠ 0) (hc : c₂ * D.τ c₂ = -1 / 4) :
    Std.Vec K ≃ₗ[K] W7 K :=
  LinearEquiv.ofInjectiveEndo (Θ D c₂) (Θ_injective D c₂ h2 hc)

theorem ΘEquiv_apply (h2 : (2 : K) ≠ 0) (hc : c₂ * D.τ c₂ = -1 / 4) (x : Std.Vec K) :
    ΘEquiv D c₂ h2 hc x = Θ D c₂ x := rfl

end Theta

end CFSG.ClassicalInvolution.PhanB3.S

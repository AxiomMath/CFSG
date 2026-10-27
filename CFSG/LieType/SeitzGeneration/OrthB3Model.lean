module

public import CFSG.LieType.SeitzGeneration.OrthB3Plane

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin OrthBlk

structure B3Data (K : Type) [Field K] where
  x : Matrix.SpecialLinearGroup (Fin 2) K
  p : ℕ
  hp : p.Prime
  hp2 : p ≠ 2
  hxp : x ^ p = 1
  hx1 : x ≠ 1
  two : (2 : K) ≠ 0
  ell : ∀ t : K, t ^ 2 - (x : Matrix (Fin 2) (Fin 2) K).trace * t + 1 ≠ 0

namespace B3Data

variable {K : Type} [Field K] (X : B3Data K)

section Matrices

@[expose] def τ : K := (X.x : Matrix (Fin 2) (Fin 2) K).trace

@[expose] def c₂ : K := 1 - (X.τ / 2) ^ 2

@[expose] def x₀ : Matrix (Fin 2) (Fin 2) K := (X.x : Matrix (Fin 2) (Fin 2) K) - (X.τ / 2) • 1

theorem det_x : (X.x : Matrix (Fin 2) (Fin 2) K).det = 1 := X.x.2

theorem τ_eq : X.τ = (X.x : Matrix (Fin 2) (Fin 2) K) 0 0 + (X.x : Matrix (Fin 2) (Fin 2) K) 1 1 :=
  Matrix.trace_fin_two _

theorem two_mul_half : 2 * (X.τ / 2) = X.τ := mul_div_cancel₀ _ X.two

theorem two_mul_half' :
    2 * (X.τ / 2) =
      (X.x : Matrix (Fin 2) (Fin 2) K) 0 0 + (X.x : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  rw [two_mul_half, τ_eq]

theorem c₂_ne_zero : X.c₂ ≠ 0 := by
  intro h0
  apply X.ell (X.τ / 2)
  change (X.τ / 2) ^ 2 - X.τ * (X.τ / 2) + 1 = 0
  unfold c₂ at h0
  linear_combination h0 + (X.τ / 2) * X.two_mul_half

include X in
theorem four_ne_zero : (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by norm_num]
  exact mul_ne_zero X.two X.two

theorem four_sub_ne_zero : 4 - X.τ ^ 2 ≠ 0 := by
  intro h
  have h4 : 4 * X.c₂ = 0 := by
    unfold c₂
    linear_combination h - (2 * (X.τ / 2) + X.τ) * X.two_mul_half
  exact X.c₂_ne_zero ((mul_eq_zero.mp h4).resolve_left (four_ne_zero X))

theorem x10_ne_zero : (X.x : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
  intro h0
  apply X.ell ((X.x : Matrix (Fin 2) (Fin 2) K) 0 0)
  have hd := X.det_x
  rw [Matrix.det_fin_two, h0] at hd
  rw [Matrix.trace_fin_two]
  linear_combination -hd

theorem x₀_mul_x₀ : X.x₀ * X.x₀ = (-X.c₂) • 1 := by
  have hd := X.det_x
  rw [Matrix.det_fin_two] at hd
  have hh := X.two_mul_half'
  ext i j
  fin_cases i <;> fin_cases j
  · simp [x₀, c₂, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -hd - (X.x : Matrix (Fin 2) (Fin 2) K) 0 0 * hh
  · simp [x₀, c₂, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -(X.x : Matrix (Fin 2) (Fin 2) K) 0 1 * hh
  · simp [x₀, c₂, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -(X.x : Matrix (Fin 2) (Fin 2) K) 1 0 * hh
  · simp [x₀, c₂, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -hd - (X.x : Matrix (Fin 2) (Fin 2) K) 1 1 * hh

theorem det_x₀ : X.x₀.det = X.c₂ := by
  have hd := X.det_x
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.det_fin_two]
  simp [x₀, c₂]
  linear_combination hd + X.τ / 2 * X.two_mul_half'

theorem trace_x₀ : X.x₀.trace = 0 := by
  rw [Matrix.trace_fin_two]
  simp [x₀]
  linear_combination -X.two_mul_half'

theorem x₀_11 : X.x₀ 1 1 = -X.x₀ 0 0 := by
  have h := X.trace_x₀
  rw [Matrix.trace_fin_two] at h
  linear_combination h

theorem x₀_10 : X.x₀ 1 0 = (X.x : Matrix (Fin 2) (Fin 2) K) 1 0 := by
  simp [x₀]

theorem commute_x_pow_x₀ (n : ℕ) :
    Commute ((X.x : Matrix (Fin 2) (Fin 2) K) ^ n) X.x₀ :=
  ((Commute.refl _).pow_left n).sub_right ((Commute.one_right _).smul_right _)

@[expose] def kx (y : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  y 0 • 1 + y 1 • (X.x : Matrix (Fin 2) (Fin 2) K)

theorem commute_x_pow_kx (n : ℕ) (y : Fin 2 → K) :
    Commute ((X.x : Matrix (Fin 2) (Fin 2) K) ^ n) (X.kx y) :=
  ((Commute.one_right _).smul_right _).add_right (((Commute.refl _).pow_left n).smul_right _)

@[expose] def T₁ : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := Matrix.toLin' !![0, -1; 1, X.τ]

@[expose] def T₁' : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := Matrix.toLin' !![X.τ, 1; -1, 0]

theorem T₁_apply (y : Fin 2 → K) : X.T₁ y = ![-y 1, y 0 + X.τ * y 1] := by
  ext i; fin_cases i <;> simp [T₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem T₁'_apply (y : Fin 2 → K) : X.T₁' y = ![X.τ * y 0 + y 1, -y 0] := by
  ext i; fin_cases i <;> simp [T₁', Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem T₁_comp : X.T₁ ∘ₗ X.T₁' = LinearMap.id := LinearMap.ext fun y => by
  rw [LinearMap.comp_apply, T₁'_apply, T₁_apply]
  ext i; fin_cases i <;> simp

theorem T₁_comp' : X.T₁' ∘ₗ X.T₁ = LinearMap.id := LinearMap.ext fun y => by
  rw [LinearMap.comp_apply, T₁_apply, T₁'_apply]
  ext i; fin_cases i <;> simp

theorem kx_T₁ (y : Fin 2 → K) : X.kx (X.T₁ y) = (X.x : Matrix (Fin 2) (Fin 2) K) * X.kx y := by
  have hCH : (X.x : Matrix (Fin 2) (Fin 2) K) * X.x = X.τ • (X.x : Matrix (Fin 2) (Fin 2) K) - 1 :=
    sq_eq_trace_smul X.det_x
  rw [kx, kx, T₁_apply, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, hCH]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  module

theorem kx_pow (n : ℕ) (y : Fin 2 → K) :
    X.kx ((X.T₁ ^ n) y) = (X.x : Matrix (Fin 2) (Fin 2) K) ^ n * X.kx y := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, kx_T₁, ih, ← Matrix.mul_assoc, ← pow_succ']

@[expose] def m : ℕ := (X.p + 1) / 2

theorem two_mul_m : 2 * X.m = X.p + 1 := by
  obtain ⟨k, hk⟩ := X.hp.odd_of_ne_two X.hp2
  unfold m
  omega

@[expose] def y : Matrix.SpecialLinearGroup (Fin 2) K := X.x ^ X.m

theorem y_mul_y : X.y * X.y = X.x := by
  rw [y, ← pow_add, ← two_mul, two_mul_m, pow_succ, X.hxp, one_mul]

theorem coe_y : (X.y : Matrix (Fin 2) (Fin 2) K) = (X.x : Matrix (Fin 2) (Fin 2) K) ^ X.m := by
  rw [y, Matrix.SpecialLinearGroup.coe_pow]

theorem not_dvd_m : ¬ X.p ∣ X.m := by
  intro h
  have h2 : X.p ∣ X.p + 1 := X.two_mul_m ▸ h.mul_left 2
  have h1 : X.p ∣ 1 := (Nat.dvd_add_right (dvd_refl X.p)).mp h2
  exact X.hp.one_lt.ne' (Nat.dvd_one.mp h1)

end Matrices

section Vectors

variable (K) in
@[expose] def zv : Fin 3 ⊕ Fin 3 ⊕ Unit → K := Pi.single (Sum.inr (Sum.inr ())) 1

variable (K) in
@[expose] def e₂ : Fin 3 ⊕ Fin 3 ⊕ Unit → K := Pi.single (Sum.inl 2) 1

variable (K) in
@[expose] def f₂ : Fin 3 ⊕ Fin 3 ⊕ Unit → K := Pi.single (Sum.inr (Sum.inl 2)) 1

@[expose] def v₂ : Fin 3 ⊕ Fin 3 ⊕ Unit → K := e₂ K + X.c₂ • f₂ K + (X.τ / 2) • zv K

@[expose] def bv : Fin 3 ⊕ Fin 3 ⊕ Unit → K := e₂ K - X.c₂ • f₂ K

omit X in
theorem q3_apply (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    quadOdd 3 K v = v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) +
      v (Sum.inl 1) * v (Sum.inr (Sum.inl 1)) + v (Sum.inl 2) * v (Sum.inr (Sum.inl 2)) +
      v (Sum.inr (Sum.inr ())) ^ 2 := by
  rw [quadOdd_apply, Fin.sum_univ_three]

omit X in
theorem polar_q3 (v w : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    polar (quadOdd 3 K) v w =
      v (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) + w (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) +
        (v (Sum.inl 1) * w (Sum.inr (Sum.inl 1)) + w (Sum.inl 1) * v (Sum.inr (Sum.inl 1))) +
        (v (Sum.inl 2) * w (Sum.inr (Sum.inl 2)) + w (Sum.inl 2) * v (Sum.inr (Sum.inl 2))) +
        2 * (v (Sum.inr (Sum.inr ())) * w (Sum.inr (Sum.inr ()))) := by
  rw [polar_quadOdd, Fin.sum_univ_three]

omit X in
theorem Q_zv : quadOdd 3 K (zv K) = 1 := by
  rw [q3_apply]; simp [zv]

theorem Q_v₂ : quadOdd 3 K X.v₂ = 1 := by
  rw [q3_apply]
  simp [v₂, e₂, f₂, zv, c₂]

theorem Q_bv : quadOdd 3 K X.bv = -X.c₂ := by
  rw [q3_apply]
  simp [bv, e₂, f₂]

theorem polar_zv_v₂ : polar (quadOdd 3 K) (zv K) X.v₂ = X.τ := by
  rw [polar_q3]
  simp [v₂, e₂, f₂, zv]
  exact X.two_mul_half

theorem polar_zv_bv : polar (quadOdd 3 K) (zv K) X.bv = 0 := by
  rw [polar_q3]
  simp [bv, e₂, f₂, zv]

theorem polar_v₂_bv : polar (quadOdd 3 K) X.v₂ X.bv = 0 := by
  rw [polar_q3]
  simp [bv, v₂, e₂, f₂, zv]

theorem v₂_ne_zv : X.v₂ ≠ zv K := by
  intro h
  have := congrFun h (Sum.inl 2)
  simp [v₂, e₂, f₂, zv] at this

end Vectors

section Block

omit X in
theorem orth01 : (oddPair K (0 : Fin 3)).Orth (oddPair K 1) := oddPair_orth (by decide)

variable (K) in
@[expose] def mB : QBlock (quadOdd 3 K) (Matrix (Fin 2) (Fin 2) K) := m2Block orth01

omit X in
theorem mB_ι (M : Matrix (Fin 2) (Fin 2) K) : (mB K).ι M = m2Emb (oddPair K 0) (oddPair K 1) M :=
  rfl

omit X in
theorem mB_qM (M : Matrix (Fin 2) (Fin 2) K) : (mB K).qM M = M.det := rfl

omit X in
theorem mB_m (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    (mB K).m v =
      !![v (Sum.inl 0), -v (Sum.inl 1); v (Sum.inr (Sum.inl 1)), v (Sum.inr (Sum.inl 0))] := by
  change m2Proj (oddPair K 0) (oddPair K 1) v = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m2Proj, oddPair_e, oddPair_f, polar_comm _ v, polar_single_inl_quadOdd,
      polar_single_inr_quadOdd]

omit X in
theorem mB_m_eq_zero {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (h0 : v (Sum.inl 0) = 0)
    (h1 : v (Sum.inl 1) = 0) (h2 : v (Sum.inr (Sum.inl 0)) = 0) (h3 : v (Sum.inr (Sum.inl 1)) = 0) :
    (mB K).m v = 0 := by
  rw [mB_m, h0, h1, h2, h3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit X in
theorem polar_mB (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (M : Matrix (Fin 2) (Fin 2) K) :
    polar (quadOdd 3 K) v ((mB K).ι M) = polDet ((mB K).m v) M :=
  polar_m2Emb v M

omit X in
theorem Q_mB (M : Matrix (Fin 2) (Fin 2) K) : quadOdd 3 K ((mB K).ι M) = M.det :=
  Q_m2Emb orth01 M

omit X in
theorem mB_ι_injective : Function.Injective (mB K).ι := fun M N h => by
  rw [← (mB K).m_ι M, ← (mB K).m_ι N, h]

omit X in
theorem mB_m_zv : (mB K).m (zv K) = 0 := mB_m_eq_zero (by simp [zv]) (by simp [zv]) (by simp [zv])
  (by simp [zv])

theorem mB_m_v₂ : (mB K).m X.v₂ = 0 := mB_m_eq_zero (by simp [v₂, e₂, f₂, zv])
  (by simp [v₂, e₂, f₂, zv]) (by simp [v₂, e₂, f₂, zv]) (by simp [v₂, e₂, f₂, zv])

theorem mB_m_bv : (mB K).m X.bv = 0 := mB_m_eq_zero (by simp [bv, e₂, f₂])
  (by simp [bv, e₂, f₂]) (by simp [bv, e₂, f₂]) (by simp [bv, e₂, f₂])

omit X in
theorem polar_mB_of_m_eq_zero {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hv : (mB K).m v = 0)
    (M : Matrix (Fin 2) (Fin 2) K) : polar (quadOdd 3 K) v ((mB K).ι M) = 0 := by
  rw [polar_mB, hv, polDet_zero_left]

omit X in
theorem polar_mB_of_m_eq_zero' {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hv : (mB K).m v = 0)
    (M : Matrix (Fin 2) (Fin 2) K) : polar (quadOdd 3 K) ((mB K).ι M) v = 0 := by
  rw [polar_comm, polar_mB_of_m_eq_zero hv]

omit X in
theorem Q_ι_one : quadOdd 3 K ((mB K).ι 1) = 1 := by rw [Q_mB, Matrix.det_one]

theorem Q_ι_x : quadOdd 3 K ((mB K).ι X.x) = 1 := by rw [Q_mB]; exact X.det_x

theorem polar_ι_one_x : polar (quadOdd 3 K) ((mB K).ι 1) ((mB K).ι X.x) = X.τ := by
  rw [polar_mB, (mB K).m_ι, polDet_eq, Matrix.trace_one, Matrix.one_mul, Fintype.card_fin]
  change ((2 : ℕ) : K) * X.τ - X.τ = X.τ
  push_cast
  ring

@[expose] def C₀ : QBlock (quadOdd 3 K) (Fin 2 → K) :=
  planeBlock ((mB K).ι 1) ((mB K).ι X.x) X.τ Q_ι_one X.Q_ι_x X.polar_ι_one_x X.four_sub_ne_zero

@[expose] def C₂ : QBlock (quadOdd 3 K) (Fin 2 → K) :=
  planeBlock (zv K) X.v₂ X.τ Q_zv X.Q_v₂ X.polar_zv_v₂ X.four_sub_ne_zero

theorem C₀_ι (y : Fin 2 → K) : X.C₀.ι y = (mB K).ι (X.kx y) := by
  change y 0 • (mB K).ι 1 + y 1 • (mB K).ι X.x = _
  rw [kx, map_add, map_smul, map_smul]

theorem C₂_ι (y : Fin 2 → K) : X.C₂.ι y = y 0 • zv K + y 1 • X.v₂ := rfl

theorem kx_injective : Function.Injective X.kx := fun y y' h => by
  rw [← X.C₀.m_ι y, ← X.C₀.m_ι y', X.C₀_ι, X.C₀_ι, h]

theorem mB_m_C₂_ι (y : Fin 2 → K) : (mB K).m (X.C₂.ι y) = 0 := by
  rw [C₂_ι, map_add, map_smul, map_smul, mB_m_zv, X.mB_m_v₂, smul_zero, smul_zero, add_zero]

theorem C₂_m_mB_ι (M : Matrix (Fin 2) (Fin 2) K) : X.C₂.m ((mB K).ι M) = 0 :=
  planeCoord_of_orth (polar_mB_of_m_eq_zero' mB_m_zv M)
    (polar_mB_of_m_eq_zero' X.mB_m_v₂ M)

theorem C₀_m_C₂_ι (y : Fin 2 → K) : X.C₀.m (X.C₂.ι y) = 0 :=
  planeCoord_of_orth (polar_mB_of_m_eq_zero (X.mB_m_C₂_ι y) 1)
    (polar_mB_of_m_eq_zero (X.mB_m_C₂_ι y) _)

theorem C₂_m_C₀_ι (y : Fin 2 → K) : X.C₂.m (X.C₀.ι y) = 0 := by
  rw [C₀_ι]
  exact X.C₂_m_mB_ι _

theorem C₂_m_bv : X.C₂.m X.bv = 0 := by
  refine planeCoord_of_orth ?_ ?_
  · rw [polar_comm]; exact X.polar_zv_bv
  · rw [polar_comm]; exact X.polar_v₂_bv

@[expose] def D : QBlock (quadOdd 3 K) ((Fin 2 → K) × (Fin 2 → K)) :=
  X.C₀.sum X.C₂ X.C₀_m_C₂_ι X.C₂_m_C₀_ι

theorem D_ι (w : (Fin 2 → K) × (Fin 2 → K)) : X.D.ι w = X.C₀.ι w.1 + X.C₂.ι w.2 := rfl

theorem D_m_eq_zero_iff (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    X.D.m v = 0 ↔ X.C₀.m v = 0 ∧ X.C₂.m v = 0 := by
  change (X.C₀.m v, X.C₂.m v) = 0 ↔ _
  rw [Prod.ext_iff]
  rfl

theorem exists_decomp (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    ∃ w r, X.D.m r = 0 ∧ v = X.D.ι w + r :=
  ⟨X.D.m v, v - X.D.ι (X.D.m v), by rw [map_sub, X.D.m_ι, sub_self], by abel⟩

theorem D_m_map_eq_zero {g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)) (h1 : g ((mB K).ι 1) = (mB K).ι 1)
    (h2 : g ((mB K).ι X.x) = (mB K).ι X.x) (h3 : g (zv K) = zv K) (h4 : g X.v₂ = X.v₂)
    {r : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hr : X.D.m r = 0) : X.D.m (g r) = 0 := by
  rw [D_m_eq_zero_iff] at hr ⊢
  exact ⟨planeCoord_map_eq_zero X.four_sub_ne_zero hg h1 h2 hr.1,
    planeCoord_map_eq_zero X.four_sub_ne_zero hg h3 h4 hr.2⟩

end Block

section Elements

omit X in
theorem sand_mem (a : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    (mB K).sand a ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
  (mB K).sand_mem_orthogonalGroup (fun _ => rfl) a

omit X in
theorem sand_fix_ι (a : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    {M : Matrix (Fin 2) (Fin 2) K}
    (h : (a.1 : Matrix (Fin 2) (Fin 2) K) * M * (↑a.2⁻¹ : Matrix (Fin 2) (Fin 2) K) = M) :
    (mB K).sand a ((mB K).ι M) = (mB K).ι M := by
  rw [(mB K).sand_ι, h]

@[expose] def g₂ : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  X.C₂.blkEquivOf X.T₁ X.T₁' X.T₁_comp X.T₁_comp'

theorem T₁_qM (y : Fin 2 → K) : X.C₂.qM (X.T₁ y) = X.C₂.qM y := by
  change (X.T₁ y) 0 ^ 2 + X.τ * (X.T₁ y) 0 * (X.T₁ y) 1 + (X.T₁ y) 1 ^ 2 =
    y 0 ^ 2 + X.τ * y 0 * y 1 + y 1 ^ 2
  rw [T₁_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem T₁_pow_p : X.T₁ ^ X.p = 1 := by
  refine LinearMap.ext fun z => X.kx_injective ?_
  rw [kx_pow, ← Matrix.SpecialLinearGroup.coe_pow, X.hxp, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mul, Module.End.one_apply]

theorem g₂_mem : X.g₂ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
  X.C₂.blkEquivOf_mem_orthogonalGroup _ _ _ _ X.T₁_qM

theorem g₂_pow : X.g₂ ^ X.p = 1 := X.C₂.blkEquivOf_pow_eq_one _ _ _ _ X.T₁_pow_p

theorem g₂_C₂_ι (y : Fin 2 → K) : X.g₂ (X.C₂.ι y) = X.C₂.ι (X.T₁ y) := X.C₂.blk_ι _ _

theorem g₂_fix {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hv : X.C₂.m v = 0) : X.g₂ v = v :=
  X.C₂.blk_of_m_eq_zero _ hv

theorem g₂_zv : X.g₂ (zv K) = X.v₂ := by
  have h := X.g₂_C₂_ι ![1, 0]
  rw [C₂_ι, C₂_ι, T₁_apply] at h
  simpa using h

theorem g₂_zv_ne : X.g₂ (zv K) ≠ zv K := by
  rw [g₂_zv]
  exact X.v₂_ne_zv

theorem sand_commute_g₂
    (a : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute ((mB K).sand a) X.g₂ :=
  (mB K).sand_commute X.C₂ X.mB_m_C₂_ι X.C₂_m_mB_ι X.T₁_comp X.T₁_comp' a

@[expose] def swp : (Fin 2 → K) × (Fin 2 → K) →ₗ[K] (Fin 2 → K) × (Fin 2 → K) :=
  (LinearMap.snd K _ _).prod (LinearMap.fst K _ _)

omit X in
theorem swp_comp : (swp : (Fin 2 → K) × (Fin 2 → K) →ₗ[K] _) ∘ₗ swp = LinearMap.id :=
  LinearMap.ext fun _ => rfl

@[expose] def σ : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  X.D.blkEquivOf swp swp swp_comp swp_comp

theorem σ_mem : X.σ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
  X.D.blkEquivOf_mem_orthogonalGroup _ _ _ _ fun w => by
    change (w.2 0 ^ 2 + X.τ * w.2 0 * w.2 1 + w.2 1 ^ 2) +
        (w.1 0 ^ 2 + X.τ * w.1 0 * w.1 1 + w.1 1 ^ 2) =
      (w.1 0 ^ 2 + X.τ * w.1 0 * w.1 1 + w.1 1 ^ 2) + (w.2 0 ^ 2 + X.τ * w.2 0 * w.2 1 + w.2 1 ^ 2)
    ring

theorem σ_D_ι (w : (Fin 2 → K) × (Fin 2 → K)) : X.σ (X.D.ι w) = X.D.ι (swp w) := X.D.blk_ι _ _

theorem σ_fix {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hv : X.D.m v = 0) : X.σ v = v :=
  X.D.blk_of_m_eq_zero _ hv

theorem σ_mul_σ : X.σ * X.σ = 1 := by
  refine LinearEquiv.ext fun v => ?_
  change X.D.blk swp (X.D.blk swp v) = v
  rw [← QBlock.blk_comp, swp_comp, QBlock.blk_id]

theorem σ_inv : X.σ⁻¹ = X.σ := inv_eq_of_mul_eq_one_right X.σ_mul_σ

theorem σ_ι_one : X.σ ((mB K).ι 1) = zv K := by
  have h := X.σ_D_ι (![1, 0], 0)
  rw [D_ι, D_ι, C₀_ι, C₂_ι, C₂_ι] at h
  simpa [swp, kx, C₀_ι] using h

theorem σ_ι_x : X.σ ((mB K).ι X.x) = X.v₂ := by
  have h := X.σ_D_ι (![0, 1], 0)
  rw [D_ι, D_ι, C₀_ι, C₂_ι, C₂_ι] at h
  simpa [swp, kx, C₀_ι] using h

@[expose] def g₀ : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  (mB K).sand (X.y, X.y⁻¹)

@[expose] def g₁ : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  (mB K).sand (X.y, X.y)

theorem g₀_mul_g₁ : X.g₀ * X.g₁ = (mB K).sand (X.x, 1) := by
  rw [g₀, g₁, ← map_mul]
  congr 1
  exact Prod.ext X.y_mul_y (inv_mul_cancel _)

theorem g₀_inv_mul_g₁ : X.g₀⁻¹ * X.g₁ = (mB K).sand (1, X.x) := by
  rw [g₀, g₁, ← map_inv, ← map_mul]
  congr 1
  exact Prod.ext (inv_mul_cancel _) (by rw [Prod.snd_mul, Prod.snd_inv, inv_inv, X.y_mul_y])

theorem g₁_C₀_ι (z : Fin 2 → K) : X.g₁ (X.C₀.ι z) = X.C₀.ι z := by
  rw [C₀_ι, g₁]
  refine sand_fix_ι _ ?_
  dsimp only
  rw [coe_y, (X.commute_x_pow_kx X.m z).eq, Matrix.mul_assoc, ← coe_y,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_one]

theorem g₁_fix {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hv : (mB K).m v = 0) : X.g₁ v = v :=
  (mB K).sand_of_m_eq_zero _ hv

theorem g₁_ι_one : X.g₁ ((mB K).ι 1) = (mB K).ι 1 := by
  have h := X.g₁_C₀_ι ![1, 0]
  simpa [C₀_ι, kx] using h

theorem g₁_ι_x : X.g₁ ((mB K).ι X.x) = (mB K).ι X.x := by
  have h := X.g₁_C₀_ι ![0, 1]
  simpa [C₀_ι, kx] using h

theorem g₁_ι_x₀ (c : K) : X.g₁ ((mB K).ι (c • X.x₀)) = (mB K).ι (c • X.x₀) := by
  rw [g₁]
  refine sand_fix_ι _ ?_
  dsimp only
  rw [coe_y, (((X.commute_x_pow_x₀ X.m).smul_right c)).eq, Matrix.mul_assoc, ← coe_y,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_one]

theorem g₀_C₀_ι (z : Fin 2 → K) : X.g₀ (X.C₀.ι z) = X.C₀.ι (X.T₁ z) := by
  rw [C₀_ι, C₀_ι, g₀, (mB K).sand_ι, kx_T₁]
  congr 1
  dsimp only
  rw [inv_inv, Matrix.mul_assoc, coe_y, ← (X.commute_x_pow_kx X.m z).eq, ← Matrix.mul_assoc,
    ← coe_y, ← Matrix.SpecialLinearGroup.coe_mul, X.y_mul_y]

theorem g₀_fix {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hv : (mB K).m v = 0) : X.g₀ v = v :=
  (mB K).sand_of_m_eq_zero _ hv

theorem g₀_fix_D {r : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hr : X.D.m r = 0) : X.g₀ r = r := by
  obtain ⟨h0, -⟩ := (X.D_m_eq_zero_iff r).mp hr
  obtain ⟨e1, e2⟩ := planeCoord_eq_zero X.four_sub_ne_zero h0
  rw [polar_mB] at e1 e2
  have hxM := mul_mul_eq_of_polDet X.det_x e1 e2
  have hyM := pow_mul_pow_eq_of_mul_mul_eq hxM X.m
  rw [g₀, (mB K).sand_apply, QBlock.blk_apply, sw_apply]
  dsimp only
  rw [inv_inv, coe_y, hyM, sub_self, map_zero, add_zero]

theorem g₂_D_ι (w : (Fin 2 → K) × (Fin 2 → K)) : X.g₂ (X.D.ι w) = X.D.ι (w.1, X.T₁ w.2) := by
  rw [D_ι, D_ι, map_add, X.g₂_fix (X.C₂_m_C₀_ι _), g₂_C₂_ι]

theorem g₀_D_ι (w : (Fin 2 → K) × (Fin 2 → K)) : X.g₀ (X.D.ι w) = X.D.ι (X.T₁ w.1, w.2) := by
  rw [D_ι, D_ι, map_add, g₀_C₀_ι, X.g₀_fix (X.mB_m_C₂_ι _)]

theorem g₁_D_ι (w : (Fin 2 → K) × (Fin 2 → K)) : X.g₁ (X.D.ι w) = X.D.ι w := by
  rw [D_ι, map_add, g₁_C₀_ι, X.g₁_fix (X.mB_m_C₂_ι _)]

theorem g₁_mem : X.g₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) := sand_mem _

theorem g₁_zv : X.g₁ (zv K) = zv K := X.g₁_fix mB_m_zv

theorem g₁_v₂ : X.g₁ X.v₂ = X.v₂ := X.g₁_fix X.mB_m_v₂

theorem sigma_mul_g₁ : X.σ * X.g₁ = X.g₁ * X.σ := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, r, hr, rfl⟩ := X.exists_decomp v
  have hg₁r : X.D.m (X.g₁ r) = 0 :=
    X.D_m_map_eq_zero X.g₁_mem X.g₁_ι_one X.g₁_ι_x X.g₁_zv X.g₁_v₂ hr
  simp only [LinearEquiv.mul_apply, map_add, g₁_D_ι, σ_D_ι, X.σ_fix hg₁r, X.σ_fix hr]

theorem sigma_mul_g₀ : X.σ * X.g₀ = X.g₂ * X.σ := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, r, hr, rfl⟩ := X.exists_decomp v
  have hr2 : X.C₂.m r = 0 := ((X.D_m_eq_zero_iff r).mp hr).2
  simp only [LinearEquiv.mul_apply, map_add, g₀_D_ι, X.g₀_fix_D hr, σ_D_ι, X.σ_fix hr, g₂_D_ι,
    X.g₂_fix hr2]
  rfl

theorem indep_master {i j k : ℤ} (h : (mB K).sand (X.x ^ i, X.x ^ j) * X.g₂ ^ k = 1) :
    (X.p : ℤ) ∣ i ∧ (X.p : ℤ) ∣ j ∧ (X.p : ℤ) ∣ k := by
  have hc : Commute ((mB K).sand (X.x ^ i, X.x ^ j)) (X.g₂ ^ k) :=
    (X.sand_commute_g₂ _).zpow_right k
  have h' : X.g₂ ^ k * (mB K).sand (X.x ^ i, X.x ^ j) = 1 := by rw [← hc.eq]; exact h
  have hk : (X.p : ℤ) ∣ k := by
    refine dvd_of_zpow_apply X.hp X.g₂_pow X.g₂_zv_ne ?_
    have := DFunLike.congr_fun h' (zv K)
    rw [LinearEquiv.mul_apply, (mB K).sand_of_m_eq_zero _ mB_m_zv] at this
    exact this
  have hg₂k : X.g₂ ^ k = 1 := by
    obtain ⟨t, rfl⟩ := hk
    rw [zpow_mul, zpow_natCast, X.g₂_pow, one_zpow]
  rw [hg₂k, mul_one] at h
  have hM : ∀ M : Matrix (Fin 2) (Fin 2) K,
      (↑(X.x ^ i) : Matrix (Fin 2) (Fin 2) K) * M * (↑(X.x ^ j)⁻¹ : Matrix (Fin 2) (Fin 2) K) =
        M := fun M => by
    have := DFunLike.congr_fun h ((mB K).ι M)
    rw [(mB K).sand_ι, LinearEquiv.coe_one, id_eq] at this
    exact mB_ι_injective this
  have hij : X.x ^ i = X.x ^ j := by
    have h1 := hM 1
    rw [Matrix.mul_one, ← Matrix.SpecialLinearGroup.coe_mul] at h1
    have h2 : X.x ^ i * (X.x ^ j)⁻¹ = 1 :=
      Subtype.ext (by rw [h1, Matrix.SpecialLinearGroup.coe_one])
    exact mul_inv_eq_one.mp h2
  have hpow : (X.x ^ i) ^ X.p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, X.hxp, one_zpow]
  have hcen : X.x ^ i = 1 := eq_one_of_central X.hp X.hp2 _ hpow fun M => by
    have h3 := hM M
    rw [← hij] at h3
    calc (↑(X.x ^ i) : Matrix (Fin 2) (Fin 2) K) * M =
          ↑(X.x ^ i) * M * (↑(X.x ^ i)⁻¹ : Matrix (Fin 2) (Fin 2) K) * ↑(X.x ^ i) := by
          rw [Matrix.mul_assoc _ (↑(X.x ^ i)⁻¹ : Matrix (Fin 2) (Fin 2) K),
            ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
            Matrix.mul_one]
      _ = M * ↑(X.x ^ i) := by rw [h3]
  have : Fact X.p.Prime := ⟨X.hp⟩
  have hord : orderOf X.x = X.p := orderOf_eq_prime X.hxp X.hx1
  refine ⟨?_, ?_, hk⟩
  · rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hcen
  · rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr (hij ▸ hcen)

theorem sand_zpow (a b : Matrix.SpecialLinearGroup (Fin 2) K) (i : ℤ) :
    (mB K).sand (a, b) ^ i = (mB K).sand (a ^ i, b ^ i) := by
  rw [← map_zpow]
  rfl

theorem indep_L_R_g₂ {i j k : ℤ}
    (h : (mB K).sand (X.x, 1) ^ i * (mB K).sand (1, X.x) ^ j * X.g₂ ^ k = 1) :
    (X.p : ℤ) ∣ i ∧ (X.p : ℤ) ∣ j ∧ (X.p : ℤ) ∣ k := by
  refine X.indep_master ?_
  rw [sand_zpow, sand_zpow, ← map_mul, one_zpow, one_zpow] at h
  convert h using 3
  exact Prod.ext (mul_one _).symm (one_mul _).symm

theorem indep_L_g₂ {i j : ℤ} (h : (mB K).sand (X.x, 1) ^ i * X.g₂ ^ j = 1) :
    (X.p : ℤ) ∣ i ∧ (X.p : ℤ) ∣ j := by
  have := X.indep_L_R_g₂ (i := i) (j := 0) (k := j) (by rw [zpow_zero, mul_one]; exact h)
  exact ⟨this.1, this.2.2⟩

theorem indep_R_g₂ {i j : ℤ} (h : (mB K).sand (1, X.x) ^ i * X.g₂ ^ j = 1) :
    (X.p : ℤ) ∣ i ∧ (X.p : ℤ) ∣ j := by
  have := X.indep_L_R_g₂ (i := 0) (j := i) (k := j) (by rw [zpow_zero, one_mul]; exact h)
  exact ⟨this.2.1, this.2.2⟩

theorem indep_g₁_g₂ {i j : ℤ} (h : X.g₁ ^ i * X.g₂ ^ j = 1) :
    (X.p : ℤ) ∣ i ∧ (X.p : ℤ) ∣ j := by
  rw [g₁, sand_zpow, y, ← zpow_natCast, ← zpow_mul] at h
  obtain ⟨h1, -, h3⟩ := X.indep_master h
  refine ⟨?_, h3⟩
  rcases (Nat.prime_iff_prime_int.mp X.hp).dvd_or_dvd h1 with h | h
  · exact absurd (Int.natCast_dvd_natCast.mp h) X.not_dvd_m
  · exact h

end Elements

end B3Data

end CFSG.LieType.SeitzGeneration

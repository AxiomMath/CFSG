module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutMatrix
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbstract
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutHeis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix Matrix.GeneralLinearGroup
open scoped Fin.NatCast

variable {K : Type*} [Field K]

theorem det_hX {ω : K} (hω3 : ω ^ 3 = 1) : (hX ω).det = 1 := by
  simp [hX, Matrix.det_diagonal, Fin.prod_univ_three]
  calc ω * ω ^ 2 = ω ^ 3 := by ring
    _ = 1 := hω3

theorem det_hP : (hP : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [hP, Matrix.det_fin_three]

@[expose] def hXsl {ω : K} (hω3 : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨hX ω, det_hX hω3⟩

@[expose] def hPsl : SpecialLinearGroup (Fin 3) K := ⟨hP, det_hP⟩

theorem coe_hXsl {ω : K} (hω3 : ω ^ 3 = 1) :
    ((SpecialLinearGroup.toGL (hXsl hω3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hX ω := rfl

theorem coe_hPsl :
    ((SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = hP := rfl

theorem mat_eq_smul_of_gl {A X : GL (Fin 3) K} {c : Kˣ} (h : A * X = X * scalar (Fin 3) c * A) :
    (A : Matrix (Fin 3) (Fin 3) K) * X = (c : K) • ((X : Matrix (Fin 3) (Fin 3) K) * A) := by
  have := congrArg Units.val h
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scalar] at this
  have hs : (Matrix.scalar (Fin 3) (c : K) : Matrix (Fin 3) (Fin 3) K) = (c : K) • 1 := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [this, hs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem scalar_mul_mul_inv (z : Kˣ) (g : GL (Fin 3) K) :
    scalar (Fin 3) z * g * (scalar (Fin 3) z)⁻¹ = g := by
  rw [mul_inv_eq_iff_eq_mul, Matrix.GeneralLinearGroup.scalar_commute]

theorem exists_conj_of_acts_like_conj {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (H : Subgroup (GL (Fin 3) K)) (hXH : SpecialLinearGroup.toGL (hXsl hω3) ∈ H)
    (hPH : SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K) ∈ H)
    (hinj : ∀ e : MulAut ↥H, (∀ m : ↥H, ∃ c : Kˣ,
      ((e m : ↥H) : GL (Fin 3) K) = (m : GL (Fin 3) K) * scalar (Fin 3) c) → e = 1)
    (d : MulAut ↥H) (A : GL (Fin 3) K)
    (hd : ∀ m : ↥H, ∃ c : Kˣ, ((d m : ↥H) : GL (Fin 3) K) =
      A * (m : GL (Fin 3) K) * A⁻¹ * scalar (Fin 3) c)
    (hdX : ∃ z : Kˣ, ((d ⟨_, hXH⟩ : ↥H) : GL (Fin 3) K) =
      SpecialLinearGroup.toGL (hXsl hω3) * scalar (Fin 3) z)
    (hdP : ∃ z : Kˣ, ((d ⟨_, hPH⟩ : ↥H) : GL (Fin 3) K) =
      SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K) * scalar (Fin 3) z) :
    ∃ s : ↥H, d = MulAut.conj s := by
  set Xg : GL (Fin 3) K := SpecialLinearGroup.toGL (hXsl hω3) with hXg
  set Pg : GL (Fin 3) K := SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K) with hPg
  have key : ∀ (Y : GL (Fin 3) K) (hY : Y ∈ H) (z : Kˣ),
      ((d ⟨Y, hY⟩ : ↥H) : GL (Fin 3) K) = Y * scalar (Fin 3) z →
        ∃ ζ : Kˣ, A * Y = Y * scalar (Fin 3) ζ * A := by
    intro Y hY z hz
    obtain ⟨c, hc⟩ := hd ⟨Y, hY⟩
    rw [hz] at hc
    refine ⟨z * c⁻¹, ?_⟩
    calc A * Y = (A * Y * A⁻¹) * A := by group
      _ = ((A * Y * A⁻¹ * scalar (Fin 3) c) * (scalar (Fin 3) c)⁻¹) * A := by group
      _ = ((Y * scalar (Fin 3) z) * (scalar (Fin 3) c)⁻¹) * A := by rw [← hc]
      _ = Y * scalar (Fin 3) (z * c⁻¹) * A := by rw [map_mul, map_inv]; group
  obtain ⟨zX, hzX⟩ := hdX
  obtain ⟨zP, hzP⟩ := hdP
  obtain ⟨ζ, hζ⟩ := key Xg hXH zX hzX
  obtain ⟨η, hη⟩ := key Pg hPH zP hzP
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
  obtain ⟨c, a, b, hc0, hA⟩ := matrix_eq_smul_pow_mul_pow hω3 hω1 (A : Matrix (Fin 3) (Fin 3) K)
    hdet (ζ : K) (η : K) (mat_eq_smul_of_gl (X := Xg) hζ) (mat_eq_smul_of_gl (X := Pg) hη)
  set s₀ : GL (Fin 3) K := Pg ^ a * Xg ^ b with hs₀
  have hs₀H : s₀ ∈ H := H.mul_mem (H.pow_mem hPH a) (H.pow_mem hXH b)
  have hAeq : A = scalar (Fin 3) (Units.mk0 c hc0) * s₀ := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_scalar, hA, hs₀, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
    rfl
  refine ⟨⟨s₀, hs₀H⟩, ?_⟩
  have hE : (MulAut.conj (⟨s₀, hs₀H⟩ : ↥H))⁻¹ * d = 1 := by
    apply hinj
    intro m
    obtain ⟨cm, hcm⟩ := hd m
    refine ⟨cm, ?_⟩
    rw [MulAut.mul_apply, MulAut.conj_inv_apply]
    show s₀⁻¹ * ((d m : ↥H) : GL (Fin 3) K) * s₀ = (m : GL (Fin 3) K) * scalar (Fin 3) cm
    rw [hcm, hAeq]
    have h1 : scalar (Fin 3) (Units.mk0 c hc0) * s₀ * (m : GL (Fin 3) K) *
        (scalar (Fin 3) (Units.mk0 c hc0) * s₀)⁻¹ = s₀ * (m : GL (Fin 3) K) * s₀⁻¹ := by
      calc scalar (Fin 3) (Units.mk0 c hc0) * s₀ * (m : GL (Fin 3) K) *
            (scalar (Fin 3) (Units.mk0 c hc0) * s₀)⁻¹
          = scalar (Fin 3) (Units.mk0 c hc0) * (s₀ * (m : GL (Fin 3) K) * s₀⁻¹) *
            (scalar (Fin 3) (Units.mk0 c hc0))⁻¹ := by group
        _ = s₀ * (m : GL (Fin 3) K) * s₀⁻¹ := scalar_mul_mul_inv _ _
    have hw : s₀⁻¹ * scalar (Fin 3) cm * s₀ = scalar (Fin 3) cm := by
      calc s₀⁻¹ * scalar (Fin 3) cm * s₀ = s₀⁻¹ * (scalar (Fin 3) cm * s₀) := mul_assoc _ _ _
        _ = s₀⁻¹ * (s₀ * scalar (Fin 3) cm) := by rw [Matrix.GeneralLinearGroup.scalar_commute]
        _ = scalar (Fin 3) cm := inv_mul_cancel_left _ _
    rw [h1]
    calc s₀⁻¹ * (s₀ * (m : GL (Fin 3) K) * s₀⁻¹ * scalar (Fin 3) cm) * s₀
        = (m : GL (Fin 3) K) * (s₀⁻¹ * scalar (Fin 3) cm * s₀) := by group
      _ = (m : GL (Fin 3) K) * scalar (Fin 3) cm := by rw [hw]
  exact (inv_mul_eq_one.1 hE).symm

section Heis

variable {ω : K}

theorem ne_zero_of_pow_three (hω3 : ω ^ 3 = 1) : ω ≠ 0 := by
  rintro rfl
  simp at hω3

theorem hX_mul_hP (hω3 : ω ^ 3 = 1) :
    hX ω * (hP : Matrix (Fin 3) (Fin 3) K) = ω • ((hP : Matrix (Fin 3) (Fin 3) K) * hX ω) := by
  ext i j
  simp only [hX, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases h : i = j + 1
  · subst h
    fin_cases j <;> simp [hP] <;> first | ring1 | linear_combination (-1) * hω3
  · simp [hP, h]

theorem hX_pow_three (hω3 : ω ^ 3 = 1) : hX ω ^ 3 = 1 := by
  rw [hX, Matrix.diagonal_pow]
  have : ∀ i : Fin 3, (ω ^ (i : ℕ)) ^ 3 = 1 := fun i => by
    rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have h3 : (fun i : Fin 3 => ω ^ (i : ℕ)) ^ 3 = 1 := by
    funext i
    simpa using this i
  rw [h3]
  exact Matrix.diagonal_one

theorem hP_pow_three : (hP : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  rw [hP_pow]
  ext i j
  simp [Matrix.one_apply]

@[expose] noncomputable def wGL (hω3 : ω ^ 3 = 1) : GL (Fin 3) K :=
  scalar (Fin 3) (Units.mk0 ω (ne_zero_of_pow_three hω3))

theorem wGL_pow_three (hω3 : ω ^ 3 = 1) : wGL hω3 ^ 3 = 1 := by
  rw [wGL, ← map_pow]
  have : (Units.mk0 ω (ne_zero_of_pow_three hω3)) ^ 3 = 1 := Units.ext (by simpa using hω3)
  rw [this, map_one]

theorem XGL_pow_three (hω3 : ω ^ 3 = 1) : SpecialLinearGroup.toGL (hXsl hω3) ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_hXsl, hX_pow_three hω3]
  rfl

theorem PGL_pow_three : SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_hPsl, hP_pow_three]
  rfl

theorem XGL_mul_PGL (hω3 : ω ^ 3 = 1) :
    SpecialLinearGroup.toGL (hXsl hω3) * SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K)
      = wGL hω3 * (SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K) *
        SpecialLinearGroup.toGL (hXsl hω3)) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, wGL, coe_scalar, coe_hXsl, coe_hPsl,
    hX_mul_hP hω3, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  rfl

theorem isPGroup_closure_X_P (hω3 : ω ^ 3 = 1) :
    IsPGroup 3 (Subgroup.closure {SpecialLinearGroup.toGL (hXsl hω3),
      SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K)} : Subgroup (GL (Fin 3) K)) :=
  isPGroup_closure_heis (fun g => Matrix.GeneralLinearGroup.scalar_commute _ g)
    (wGL_pow_three hω3) (XGL_pow_three hω3) PGL_pow_three (XGL_mul_PGL hω3)

end Heis

theorem sylowCentreInn_of_family {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (H : Subgroup (GL (Fin 3) K)) [Finite ↥H]
    (hXH : SpecialLinearGroup.toGL (hXsl hω3) ∈ H)
    (hPH : SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K) ∈ H)
    (D : Subgroup (MulAut ↥H)) (hND : LocalBalance.innerAut ↥H ≤ D)
    (h1 : ∀ (σ : MulAut ↥H) (k : ℕ), σ ^ (3 ^ k) = 1 → σ ∈ D)
    (hDform : ∀ d ∈ D, ∃ A : GL (Fin 3) K, ∀ m : ↥H, ∃ c : Kˣ,
      ((d m : ↥H) : GL (Fin 3) K) = A * (m : GL (Fin 3) K) * A⁻¹ * scalar (Fin 3) c)
    (hcenter : ∀ c ∈ Subgroup.center ↥H, ∃ z : Kˣ, (c : GL (Fin 3) K) = scalar (Fin 3) z)
    (hinj : ∀ e : MulAut ↥H, (∀ m : ↥H, ∃ c : Kˣ,
      ((e m : ↥H) : GL (Fin 3) K) = (m : GL (Fin 3) K) * scalar (Fin 3) c) → e = 1) :
    SylowCentreInn ↥H := by
  refine sylowCentreInn_of_data D hND
    ((Subgroup.closure {SpecialLinearGroup.toGL (hXsl hω3),
      SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K)}).subgroupOf H)
    (isPGroup_closure_X_P hω3).comap_subtype h1 ?_
  intro d hd hcen
  obtain ⟨A, hA⟩ := hDform d hd
  have hscal : ∀ (Y : GL (Fin 3) K) (hY : Y ∈ H),
      Y ∈ Subgroup.closure {SpecialLinearGroup.toGL (hXsl hω3),
        SpecialLinearGroup.toGL (hPsl : SpecialLinearGroup (Fin 3) K)} →
      ∃ z : Kˣ, ((d ⟨Y, hY⟩ : ↥H) : GL (Fin 3) K) = Y * scalar (Fin 3) z := by
    intro Y hY hYc
    obtain ⟨z, hz⟩ := hcenter _ (hcen ⟨Y, hY⟩ ((Subgroup.mem_subgroupOf).2 hYc))
    refine ⟨z, ?_⟩
    have h2 : ((d ⟨Y, hY⟩ : ↥H) : GL (Fin 3) K) = scalar (Fin 3) z * Y := by
      have : ((d ⟨Y, hY⟩ * (⟨Y, hY⟩ : ↥H)⁻¹ : ↥H) : GL (Fin 3) K) = scalar (Fin 3) z := hz
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at this
      simpa using congrArg (· * Y) this
    rw [h2, Matrix.GeneralLinearGroup.scalar_commute]
  obtain ⟨s, hs⟩ := exists_conj_of_acts_like_conj hω3 hω1 H hXH hPH hinj d A hA
    (hscal _ hXH (Subgroup.subset_closure (by simp)))
    (hscal _ hPH (Subgroup.subset_closure (by simp)))
  exact ⟨s, hs.symm⟩

theorem mulAut_eq_one_of_central_perfect {X : Type*} [Group X] (hperf : Group.IsPerfect X)
    (a : MulAut X) (h : ∀ x, x⁻¹ * a x ∈ Subgroup.center X) : a = 1 := by
  let f : X →* Subgroup.center X :=
    { toFun := fun x => ⟨x⁻¹ * a x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (x * y)⁻¹ * a (x * y) = (x⁻¹ * a x) * (y⁻¹ * a y)
        have hc := Subgroup.mem_center_iff.1 (h x) y⁻¹
        calc (x * y)⁻¹ * a (x * y) = y⁻¹ * (x⁻¹ * a x) * a y := by rw [map_mul]; group
          _ = (x⁻¹ * a x) * y⁻¹ * a y := by rw [hc]
          _ = (x⁻¹ * a x) * (y⁻¹ * a y) := by rw [mul_assoc] }
  have hker : commutator X ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hperf.commutator_eq_top, top_le_iff] at hker
  apply MulEquiv.ext
  intro x
  have hx : x ∈ f.ker := hker ▸ Subgroup.mem_top x
  have h1 : x⁻¹ * a x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have h2 : a x = x := by
    calc a x = x * (x⁻¹ * a x) := by group
      _ = x := by rw [h1, mul_one]
  exact h2

theorem eq_one_of_scalar_perfect {H : Subgroup (GL (Fin 3) K)} (hperf : Group.IsPerfect ↥H)
    (e : MulAut ↥H) (h : ∀ m : ↥H, ∃ c : Kˣ,
      ((e m : ↥H) : GL (Fin 3) K) = (m : GL (Fin 3) K) * scalar (Fin 3) c) : e = 1 := by
  refine mulAut_eq_one_of_central_perfect hperf e fun x => ?_
  obtain ⟨c, hc⟩ := h x
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have h1 : (((x⁻¹ * e x : ↥H)) : GL (Fin 3) K) = scalar (Fin 3) c := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hc]
    group
  have h2 : ((g * (x⁻¹ * e x) : ↥H) : GL (Fin 3) K) = (g : GL (Fin 3) K) * scalar (Fin 3) c := by
    rw [Subgroup.coe_mul, h1]
  have h3 : ((x⁻¹ * e x * g : ↥H) : GL (Fin 3) K) = scalar (Fin 3) c * (g : GL (Fin 3) K) := by
    rw [Subgroup.coe_mul, h1]
  rw [h2, h3]
  exact (Matrix.GeneralLinearGroup.scalar_commute c _).symm

end CFSG.HardMathSupport.Solomon.Coordinator

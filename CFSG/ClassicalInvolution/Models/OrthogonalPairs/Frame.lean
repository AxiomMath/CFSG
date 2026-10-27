module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

structure Frame (Q : QuadraticForm K V) where
  P : HypPair Q
  P' : HypPair Q
  orth : P.Orth P'

namespace Frame

variable (F : Frame Q)

abbrev e₁ : V := F.P.e
abbrev f₁ : V := F.P.f
abbrev e₂ : V := F.P'.e
abbrev f₂ : V := F.P'.f

@[expose] def swap : Frame Q where
  P := F.P
  P' := ⟨F.P'.f, F.P'.e, F.P'.Q_f, F.P'.Q_e, F.P'.polar_fe⟩
  orth :=
    { ee := F.orth.ef
      ef := F.orth.ee
      fe := F.orth.ff
      ff := F.orth.fe }

theorem Q_e₁ : Q F.e₁ = 0 := F.P.Q_e
theorem Q_f₁ : Q F.f₁ = 0 := F.P.Q_f
theorem Q_e₂ : Q F.e₂ = 0 := F.P'.Q_e
theorem Q_f₂ : Q F.f₂ = 0 := F.P'.Q_f
theorem polar_e₁_f₁ : polar Q F.e₁ F.f₁ = 1 := F.P.polar_ef
theorem polar_f₁_e₁ : polar Q F.f₁ F.e₁ = 1 := F.P.polar_fe
theorem polar_e₂_f₂ : polar Q F.e₂ F.f₂ = 1 := F.P'.polar_ef
theorem polar_f₂_e₂ : polar Q F.f₂ F.e₂ = 1 := F.P'.polar_fe
theorem polar_e₁_e₁ : polar Q F.e₁ F.e₁ = 0 := F.P.polar_ee
theorem polar_f₁_f₁ : polar Q F.f₁ F.f₁ = 0 := F.P.polar_ff
theorem polar_e₂_e₂ : polar Q F.e₂ F.e₂ = 0 := F.P'.polar_ee
theorem polar_f₂_f₂ : polar Q F.f₂ F.f₂ = 0 := F.P'.polar_ff
theorem polar_e₁_e₂ : polar Q F.e₁ F.e₂ = 0 := F.orth.ee
theorem polar_e₁_f₂ : polar Q F.e₁ F.f₂ = 0 := F.orth.ef
theorem polar_f₁_e₂ : polar Q F.f₁ F.e₂ = 0 := F.orth.fe
theorem polar_f₁_f₂ : polar Q F.f₁ F.f₂ = 0 := F.orth.ff
theorem polar_e₂_e₁ : polar Q F.e₂ F.e₁ = 0 := by rw [polar_comm, F.orth.ee]
theorem polar_f₂_e₁ : polar Q F.f₂ F.e₁ = 0 := by rw [polar_comm, F.orth.ef]
theorem polar_e₂_f₁ : polar Q F.e₂ F.f₁ = 0 := by rw [polar_comm, F.orth.fe]
theorem polar_f₂_f₁ : polar Q F.f₂ F.f₁ = 0 := by rw [polar_comm, F.orth.ff]

attribute [local simp] Q_e₁ Q_f₁ Q_e₂ Q_f₂ polar_e₁_f₁ polar_f₁_e₁ polar_e₂_f₂ polar_f₂_e₂
  polar_e₁_e₁ polar_f₁_f₁ polar_e₂_e₂ polar_f₂_f₂ polar_e₁_e₂ polar_e₁_f₂ polar_f₁_e₂
  polar_f₁_f₂ polar_e₂_e₁ polar_f₂_e₁ polar_e₂_f₁ polar_f₂_f₁

@[expose] def coords : V →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun x := !![polar Q x F.f₁, -polar Q x F.f₂; polar Q x F.e₂, polar Q x F.e₁]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [polar_add_left, add_comm]
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [polar_smul_left]

@[expose] def incl : Matrix (Fin 2) (Fin 2) K →ₗ[K] V where
  toFun X := X 0 0 • F.e₁ + X 1 1 • F.f₁ + (-X 0 1) • F.e₂ + X 1 0 • F.f₂
  map_add' X Y := by
    simp only [Matrix.add_apply, add_smul, neg_add]
    abel
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add,
      neg_smul, smul_neg]

theorem incl_apply (X : Matrix (Fin 2) (Fin 2) K) :
    F.incl X = X 0 0 • F.e₁ + X 1 1 • F.f₁ + (-X 0 1) • F.e₂ + X 1 0 • F.f₂ :=
  rfl

theorem coords_apply (x : V) :
    F.coords x = !![polar Q x F.f₁, -polar Q x F.f₂; polar Q x F.e₂, polar Q x F.e₁] :=
  rfl

theorem coords_incl (X : Matrix (Fin 2) (Fin 2) K) : F.coords (F.incl X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coords_apply, incl_apply, polar_add_left, polar_smul_left]

theorem polar_incl_right (x : V) (Y : Matrix (Fin 2) (Fin 2) K) :
    polar Q x (F.incl Y) =
      (F.coords x) 1 1 * Y 0 0 + (F.coords x) 0 0 * Y 1 1 - (F.coords x) 1 0 * Y 0 1 -
        (F.coords x) 0 1 * Y 1 0 := by
  simp only [incl_apply, coords_apply, polar_add_right, polar_smul_right]
  simp
  ring

theorem Q_incl (X : Matrix (Fin 2) (Fin 2) K) : Q (F.incl X) = X.det := by
  rw [incl_apply, Matrix.det_fin_two, QuadraticMap.map_add Q, QuadraticMap.map_add Q,
    QuadraticMap.map_add Q]
  simp only [polar_add_left, polar_smul_left, polar_smul_right, map_smul_eq_sq, smul_eq_mul]
  simp
  ring

theorem Q_incl_add (X : Matrix (Fin 2) (Fin 2) K) {r : V} (hr : F.coords r = 0) :
    Q (F.incl X + r) = X.det + Q r := by
  rw [QuadraticMap.map_add Q, Q_incl, polar_comm, polar_incl_right, hr]
  simp

theorem Q_eq (x : V) : Q x = (F.coords x).det + Q (x - F.incl (F.coords x)) := by
  have hr : F.coords (x - F.incl (F.coords x)) = 0 := by rw [map_sub, coords_incl, sub_self]
  have := F.Q_incl_add (F.coords x) hr
  rwa [add_sub_cancel] at this

@[expose] def embLin (T : Module.End K (Matrix (Fin 2) (Fin 2) K)) : V →ₗ[K] V :=
  LinearMap.id + F.incl ∘ₗ (T - 1) ∘ₗ F.coords

theorem embLin_apply (T : Module.End K (Matrix (Fin 2) (Fin 2) K)) (x : V) :
    F.embLin T x = x + F.incl (T (F.coords x) - F.coords x) := by
  simp [embLin]

theorem embLin_one : F.embLin 1 = 1 := by
  ext x
  simp [embLin_apply]

theorem embLin_mul (S T : Module.End K (Matrix (Fin 2) (Fin 2) K)) :
    F.embLin (S * T) = F.embLin S * F.embLin T := by
  ext x
  simp only [embLin_apply, Module.End.mul_apply, map_add, coords_incl, map_sub]
  abel

theorem embLin_apply_eq (T : Module.End K (Matrix (Fin 2) (Fin 2) K)) (x : V) :
    F.embLin T x = F.incl (T (F.coords x)) + (x - F.incl (F.coords x)) := by
  rw [embLin_apply, map_sub]
  abel

theorem Q_embLin {T : Module.End K (Matrix (Fin 2) (Fin 2) K)} (hT : ∀ X, (T X).det = X.det)
    (x : V) : Q (F.embLin T x) = Q x := by
  have hr : F.coords (x - F.incl (F.coords x)) = 0 := by rw [map_sub, coords_incl, sub_self]
  rw [embLin_apply_eq, F.Q_incl_add _ hr, hT, ← Q_eq]

@[expose] def rhoL : SL(2, K) →* Module.End K (Matrix (Fin 2) (Fin 2) K) where
  toFun A := LinearMap.mulLeft K (A : Matrix (Fin 2) (Fin 2) K)
  map_one' := by
    ext X : 1
    simp
  map_mul' A B := by
    ext X : 1
    simp

@[expose] noncomputable def embHom {G : Type*} [Group G]
    (ρ : G →* Module.End K (Matrix (Fin 2) (Fin 2) K)) : G →* (V ≃ₗ[K] V) where
  toFun g := LinearEquiv.ofLinearMap (F.embLin (ρ g)) (F.embLin (ρ g⁻¹))
    (by
      rw [← Module.End.mul_eq_comp, ← embLin_mul, ← map_mul, mul_inv_cancel, map_one, embLin_one]
      rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← embLin_mul, ← map_mul, inv_mul_cancel, map_one, embLin_one]
      rfl)
  map_one' := by
    refine LinearEquiv.ext fun x => ?_
    simp [embLin_one]
  map_mul' g h := by
    refine LinearEquiv.ext fun x => ?_
    simp [embLin_mul]

theorem embHom_apply {G : Type*} [Group G] (ρ : G →* Module.End K (Matrix (Fin 2) (Fin 2) K))
    (g : G) (x : V) : F.embHom ρ g x = F.embLin (ρ g) x :=
  rfl

@[expose] noncomputable def La : SL(2, K) →* (V ≃ₗ[K] V) := F.embHom rhoL

theorem La_apply (A : SL(2, K)) (x : V) :
    F.La A x = x + F.incl ((A : Matrix (Fin 2) (Fin 2) K) * F.coords x - F.coords x) := by
  rw [La, embHom_apply, embLin_apply]
  rfl

theorem La_apply_incl (A : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    F.La A (F.incl X) = F.incl ((A : Matrix (Fin 2) (Fin 2) K) * X) := by
  rw [La_apply, coords_incl, map_sub]
  abel

theorem La_apply_of_coords_eq_zero (A : SL(2, K)) {r : V} (hr : F.coords r = 0) : F.La A r = r := by
  rw [La_apply, hr]
  simp

theorem La_mem_orthogonalGroup (A : SL(2, K)) :
    F.La A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  exact F.Q_embLin (T := rhoL A) (fun X => by
    simp [rhoL, Matrix.det_mul]) x

theorem La_injective : Function.Injective (F.La : SL(2, K) → V ≃ₗ[K] V) := by
  intro A B h
  apply Subtype.ext
  have := congrArg (fun g : V ≃ₗ[K] V => F.coords (g (F.incl 1))) h
  simpa [La_apply_incl, coords_incl] using this

theorem coords_La (A : SL(2, K)) (x : V) :
    F.coords (F.La A x) = (A : Matrix (Fin 2) (Fin 2) K) * F.coords x := by
  rw [La_apply, map_add, coords_incl]
  abel

theorem coe_transvection_zero_one (c : K) :
    ((Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem coe_transvection_one_zero (c : K) :
    ((Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem La_transvection_zero_one (c : K) :
    F.La (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      eichler Q F.e₂ (c • F.e₁) := by
  refine LinearEquiv.ext fun x => ?_
  have hu : Q F.e₂ = 0 := F.Q_e₂
  have hw : polar Q F.e₂ (c • F.e₁) = 0 := by rw [polar_smul_right, F.polar_e₂_e₁]; simp
  rw [eichler_apply hu hw, La_apply, coe_transvection_zero_one]
  simp only [Matrix.mul_fin_two, coords_apply, incl_apply, polar_smul_right, map_smul_eq_sq,
    Q_e₁, smul_eq_mul]
  simp
  module

theorem La_transvection_one_zero (c : K) :
    F.La (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      eichler Q F.f₁ (c • F.f₂) := by
  refine LinearEquiv.ext fun x => ?_
  have hu : Q F.f₁ = 0 := F.Q_f₁
  have hw : polar Q F.f₁ (c • F.f₂) = 0 := by rw [polar_smul_right, F.polar_f₁_f₂]; simp
  rw [eichler_apply hu hw, La_apply, coe_transvection_one_zero]
  simp only [Matrix.mul_fin_two, coords_apply, incl_apply, polar_smul_right, map_smul_eq_sq,
    Q_f₂, smul_eq_mul]
  simp
  module

theorem sl2_apply_mem {G : Type*} [Group G] (φ : SL(2, K) →* G) (H : Subgroup G)
    (h01 : ∀ c, φ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) ∈ H)
    (h10 : ∀ c, φ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c) ∈ H)
    (A : SL(2, K)) : φ A ∈ H := by
  have htop := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 2) (K := K)
  have hle : (⊤ : Subgroup SL(2, K)) ≤ H.comap φ := by
    rw [← htop, Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01 c
    · exact h10 c
    · exact absurd rfl hij
  exact hle (Subgroup.mem_top A)

theorem La_mem_elementaryGroup (A : SL(2, K)) : F.La A ∈ elementaryGroup Q := by
  refine sl2_apply_mem F.La (elementaryGroup Q) (fun c => ?_) (fun c => ?_) A
  · rw [La_transvection_zero_one]
    exact eichler_mem_elementaryGroup Q _ _
  · rw [La_transvection_one_zero]
    exact eichler_mem_elementaryGroup Q _ _

theorem La_range_eq_closure :
    F.La.range = Subgroup.closure
      ({g | ∃ c : K, g = eichler Q F.e₂ (c • F.e₁)} ∪
        {g | ∃ c : K, g = eichler Q F.f₁ (c • F.f₂)}) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨A, rfl⟩
    refine sl2_apply_mem F.La (Subgroup.closure _) (fun c => ?_) (fun c => ?_) A
    · rw [La_transvection_zero_one]
      exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
    · rw [La_transvection_one_zero]
      exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  · rw [Subgroup.closure_le]
    rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, La_transvection_zero_one F c⟩
    · exact ⟨_, La_transvection_one_zero F c⟩

end Frame

@[expose] def sigmaLin : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun X := !![X 0 0, -X 1 0; -X 0 1, X 1 1]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem sigmaLin_apply (X : Matrix (Fin 2) (Fin 2) K) :
    sigmaLin X = !![X 0 0, -X 1 0; -X 0 1, X 1 1] :=
  rfl

theorem sigmaLin_sigmaLin (X : Matrix (Fin 2) (Fin 2) K) : sigmaLin (sigmaLin X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]

theorem det_sigmaLin (X : Matrix (Fin 2) (Fin 2) K) : (sigmaLin X).det = X.det := by
  simp only [sigmaLin_apply, Matrix.det_fin_two]
  simp
  ring

theorem sigmaLin_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    sigmaLin (A * B) = sigmaLin B * sigmaLin A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

namespace Frame

variable (F : Frame Q)

theorem coords_swap (x : V) : F.swap.coords x = sigmaLin (F.coords x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coords_apply, sigmaLin_apply, swap]

theorem incl_swap (X : Matrix (Fin 2) (Fin 2) K) : F.swap.incl X = F.incl (sigmaLin X) := by
  simp only [incl_apply, sigmaLin_apply, swap]
  simp
  abel

theorem embLin_swap (T : Module.End K (Matrix (Fin 2) (Fin 2) K)) :
    F.swap.embLin T = F.embLin (sigmaLin ∘ₗ T ∘ₗ sigmaLin) := by
  ext x
  rw [embLin_apply, embLin_apply, incl_swap, coords_swap]
  simp [sigmaLin_sigmaLin]

theorem sigmaLin_comp_mulLeft_comp_sigmaLin (A : Matrix (Fin 2) (Fin 2) K) :
    sigmaLin ∘ₗ LinearMap.mulLeft K A ∘ₗ sigmaLin = LinearMap.mulRight K (sigmaLin A) := by
  ext X : 1
  simp [sigmaLin_mul, sigmaLin_sigmaLin]

theorem La_swap_apply (A : SL(2, K)) (x : V) :
    F.swap.La A x =
      F.embLin (LinearMap.mulRight K (sigmaLin (A : Matrix (Fin 2) (Fin 2) K))) x := by
  rw [La, embHom_apply, embLin_swap]
  change F.embLin (sigmaLin ∘ₗ LinearMap.mulLeft K (A : Matrix (Fin 2) (Fin 2) K) ∘ₗ sigmaLin) x = _
  rw [sigmaLin_comp_mulLeft_comp_sigmaLin]

theorem La_comm_La_swap (A B : SL(2, K)) : F.La A * F.swap.La B = F.swap.La B * F.La A := by
  refine LinearEquiv.ext fun x => ?_
  have h2 : ∀ y, F.La A y = F.embLin (LinearMap.mulLeft K (A : Matrix (Fin 2) (Fin 2) K)) y :=
    fun y => rfl
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, La_swap_apply, h2, La_swap_apply, h2,
    ← Module.End.mul_apply, ← Module.End.mul_apply, ← embLin_mul, ← embLin_mul]
  congr 2
  ext X : 1
  simp [Matrix.mul_assoc]

theorem La_neg_one_apply (x : V) : F.La (-1) x = x - (2 : K) • F.incl (F.coords x) := by
  rw [La_apply]
  simp [two_smul]
  abel

theorem La_swap_neg_one : F.swap.La (-1) = F.La (-1) := by
  refine LinearEquiv.ext fun x => ?_
  rw [La_neg_one_apply, La_neg_one_apply, coords_swap, incl_swap, sigmaLin_sigmaLin]

theorem La_neg_one_mul_self : F.La (-1) * F.La (-1) = 1 := by
  rw [← map_mul, neg_mul_neg, one_mul, map_one]

theorem La_neg_one_comm (A : SL(2, K)) : F.La (-1) * F.La A = F.La A * F.La (-1) := by
  rw [← map_mul, ← map_mul, neg_mul, mul_neg, one_mul, mul_one]

theorem La_swap_neg_one_comm (A : SL(2, K)) :
    F.La (-1) * F.swap.La A = F.swap.La A * F.La (-1) := by
  rw [← F.La_swap_neg_one, ← map_mul, ← map_mul, neg_mul, mul_neg, one_mul, mul_one]

@[expose] def span : Submodule K V := LinearMap.range F.incl

@[expose] def perp : Submodule K V := LinearMap.ker F.coords

theorem mem_span_iff {x : V} : x ∈ F.span ↔ x = F.incl (F.coords x) := by
  constructor
  · rintro ⟨X, rfl⟩
    rw [coords_incl]
  · intro h
    exact ⟨_, h.symm⟩

theorem mem_perp_iff {x : V} : x ∈ F.perp ↔ F.coords x = 0 :=
  LinearMap.mem_ker

theorem isCompl_span_perp : IsCompl F.span F.perp := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ ⟨X, rfl⟩ hx
    rw [mem_perp_iff, coords_incl] at hx
    rw [hx, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨F.incl (F.coords x), ⟨_, rfl⟩, x - F.incl (F.coords x), ?_, by abel⟩
    rw [mem_perp_iff, map_sub, coords_incl, sub_self]

theorem span_eq_swap_span : F.swap.span = F.span := by
  ext x
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨sigmaLin X, (F.incl_swap X).symm⟩
  · rintro ⟨X, rfl⟩
    exact ⟨sigmaLin X, by rw [incl_swap, sigmaLin_sigmaLin]⟩

theorem perp_swap : F.swap.perp = F.perp := by
  ext x
  rw [mem_perp_iff, mem_perp_iff, coords_swap]
  constructor
  · intro h
    have := congrArg sigmaLin h
    simpa [sigmaLin_sigmaLin] using this
  · intro h
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]

@[expose] def map (F : Frame Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : Frame Q where
  P := ⟨g F.e₁, g F.f₁, by rw [map_of_mem hg, F.Q_e₁], by rw [map_of_mem hg, F.Q_f₁],
    by rw [polar_map_of_mem hg, F.polar_e₁_f₁]⟩
  P' := ⟨g F.e₂, g F.f₂, by rw [map_of_mem hg, F.Q_e₂], by rw [map_of_mem hg, F.Q_f₂],
    by rw [polar_map_of_mem hg, F.polar_e₂_f₂]⟩
  orth :=
    ⟨by rw [polar_map_of_mem hg]; exact F.orth.ee, by rw [polar_map_of_mem hg]; exact F.orth.ef,
      by rw [polar_map_of_mem hg]; exact F.orth.fe, by rw [polar_map_of_mem hg]; exact F.orth.ff⟩

theorem map_incl (F : Frame Q) {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (X : Matrix (Fin 2) (Fin 2) K) : (F.map hg).incl X = g (F.incl X) := by
  simp [incl_apply, map]

theorem map_coords (F : Frame Q) {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (x : V) : (F.map hg).coords x = F.coords (g⁻¹ x) := by
  have h : ∀ y : V, polar Q x (g y) = polar Q (g⁻¹ x) y := fun y => by
    rw [← polar_map_of_mem hg (g⁻¹ x) y]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coords_apply, map, h]

theorem map_La (F : Frame Q) {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (A : SL(2, K)) : (F.map hg).La A = g * F.La A * g⁻¹ := by
  refine LinearEquiv.ext fun x => ?_
  rw [La_apply, map_coords, map_incl, LinearEquiv.mul_apply, LinearEquiv.mul_apply, La_apply,
    map_add]
  simp

end Frame

end CFSG.ClassicalInvolution.Models.OrthogonalPairs

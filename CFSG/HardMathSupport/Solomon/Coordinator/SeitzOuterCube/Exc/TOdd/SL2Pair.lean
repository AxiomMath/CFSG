module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.SubfieldMaximalSL2
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Seitz.TrialityOdd.Proving (sl2Range u2_mem_sl2Range l2_mem_sl2Range)
open CFSG.HardMathSupport.Foote.ModuleExclusions (Ai hilbert90_matrix)

section Basic

variable {K : Type} [Field K]

theorem scalar_of_commute_u2_l2 (M : Matrix (Fin 2) (Fin 2) K)
    (hu : M * (u2 (1 : K) : Matrix (Fin 2) (Fin 2) K) =
      (u2 (1 : K) : Matrix (Fin 2) (Fin 2) K) * M)
    (hl : M * (l2 (1 : K) : Matrix (Fin 2) (Fin 2) K) =
      (l2 (1 : K) : Matrix (Fin 2) (Fin 2) K) * M) :
    ∃ s : K, M = s • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [u2_coe] at hu
  rw [l2_coe] at hl
  have h1 := congrFun (congrFun hu 0) 0
  have h2 := congrFun (congrFun hu 0) 1
  have h3 := congrFun (congrFun hl 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h1 h2 h3
  have h4 : M 1 1 = M 0 0 := by linear_combination (-1 : K) * h2
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h3, h4]

theorem cube_apply_of_orderOf_eq_three {τ : K ≃+* K} (hτ : orderOf τ = 3) (x : K) :
    τ (τ (τ x)) = x := by
  have h1 : τ ^ 3 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have := congrArg (fun f : K ≃+* K => f x) h1
  simpa [pow_succ, RingAut.mul_apply] using this

theorem mulAut_cube_apply {G : Type*} [Group G] (θ : MulAut G) (h : θ ^ 3 = 1) (A : G) :
    θ (θ (θ A)) = A := by
  have := congrArg (fun f : MulAut G => f A) h
  simpa [pow_succ, MulAut.mul_apply] using this

theorem lang_conj_shape {R : Type*} [Ring R] (φ : R →+* R) (N Ni B Bi : R) (hN' : Ni * N = 1)
    (hB : B * Bi = 1) (h : N * φ B = B) (A : R) :
    N * φ A * Ni = B * φ (Bi * A * B) * Bi := by
  have e1 : B * φ Bi = N := by
    calc B * φ Bi = (N * φ B) * φ Bi := by rw [h]
      _ = N * φ (B * Bi) := by rw [map_mul, mul_assoc]
      _ = N := by rw [hB, map_one, mul_one]
  have e2 : φ B * Bi = Ni := by
    calc φ B * Bi = (Ni * N) * φ B * Bi := by rw [hN', one_mul]
      _ = Ni * (N * φ B) * Bi := by rw [mul_assoc Ni N]
      _ = Ni * B * Bi := by rw [h]
      _ = Ni := by rw [mul_assoc, hB, mul_one]
  calc N * φ A * Ni = (B * φ Bi) * φ A * (φ B * Bi) := by rw [e1, e2]
    _ = B * φ (Bi * A * B) * Bi := by simp only [map_mul, mul_assoc]

theorem commute_of_conj_commute {g : GL (Fin 2) K} {M Y : Matrix (Fin 2) (Fin 2) K}
    (h : M * ((g : Matrix (Fin 2) (Fin 2) K) * Y *
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
      ((g : Matrix (Fin 2) (Fin 2) K) * Y *
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * M) :
    (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M * (g : Matrix (Fin 2) (Fin 2) K)) * Y =
      Y * (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M *
        (g : Matrix (Fin 2) (Fin 2) K)) := by
  calc (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M *
        (g : Matrix (Fin 2) (Fin 2) K)) * Y
      = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          (M * ((g : Matrix (Fin 2) (Fin 2) K) * Y *
            ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) *
          (g : Matrix (Fin 2) (Fin 2) K) := by
        simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    _ = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          (((g : Matrix (Fin 2) (Fin 2) K) * Y *
            ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * M) *
          (g : Matrix (Fin 2) (Fin 2) K) := by rw [h]
    _ = _ := by simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]

theorem mul_comm_of_conj_eq_self {U : GL (Fin 2) K} {A : Matrix (Fin 2) (Fin 2) K}
    (h : (U : Matrix (Fin 2) (Fin 2) K) * A *
      ((U⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = A) :
    (U : Matrix (Fin 2) (Fin 2) K) * A = A * (U : Matrix (Fin 2) (Fin 2) K) := by
  calc (U : Matrix (Fin 2) (Fin 2) K) * A
      = ((U : Matrix (Fin 2) (Fin 2) K) * A *
          ((U⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * (U : Matrix (Fin 2) (Fin 2) K) := by
        simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    _ = A * (U : Matrix (Fin 2) (Fin 2) K) := by rw [h]

theorem eq_scalar_of_conj_eq_scalar {g : GL (Fin 2) K} {M : Matrix (Fin 2) (Fin 2) K} {s : K}
    (h : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M * (g : Matrix (Fin 2) (Fin 2) K) =
      s • (1 : Matrix (Fin 2) (Fin 2) K)) :
    M = Matrix.scalar (Fin 2) s := by
  calc M = (g : Matrix (Fin 2) (Fin 2) K) *
        (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M * (g : Matrix (Fin 2) (Fin 2) K)) *
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]
    _ = Matrix.scalar (Fin 2) s := by
        rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv,
          Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem finrank_fixedField_eq_three [Finite K] {τ : K ≃+* K} (hτ : orderOf τ = 3) {F : Subfield K}
    (hFτ : ∀ x, x ∈ F ↔ τ x = x) : Module.finrank F K = 3 := by
  have hFeq : F = FixedPoints.subfield (Subgroup.zpowers τ) K := by
    ext x
    rw [hFτ]
    constructor
    · exact CFSG.HardMathSupport.Foote.ModuleExclusions.mem_fixedPoints_subfield_of_apply_eq τ x
    · intro hx
      exact hx ⟨τ, Subgroup.mem_zpowers τ⟩
  subst hFeq
  haveI : Fintype (Subgroup.zpowers τ) := Fintype.ofFinite _
  rw [FixedPoints.finrank_eq_card (Subgroup.zpowers τ) K, ← Nat.card_eq_fintype_card,
    Nat.card_zpowers, hτ]

theorem mem_sl2Range_iff_map_eq {τ : K ≃+* K} {F : Subfield K} (hFτ : ∀ x, x ∈ F ↔ τ x = x)
    (y : SpecialLinearGroup (Fin 2) K) :
    y ∈ sl2Range F K ↔ (y : Matrix (Fin 2) (Fin 2) K).map τ = y := by
  constructor
  · rintro ⟨z, rfl⟩
    ext i j
    rw [Matrix.map_apply]
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (hFτ _).1 (z.1 i j).2
  · intro h
    have hfix : ∀ i j, τ (y.1 i j) = y.1 i j := fun i j => congrFun (congrFun h i) j
    let M : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => ⟨y.1 i j, (hFτ _).2 (hfix i j)⟩
    have hdet : M.det = 1 := by
      apply (algebraMap F K).injective
      rw [RingHom.map_det, map_one]
      have : (algebraMap F K).mapMatrix M = y.1 := by
        ext i j
        rfl
      rw [this]
      exact y.2
    exact ⟨⟨M, hdet⟩, Subtype.ext (by ext i j; rfl)⟩

theorem det_gl2_conj_eq_one (h : GL (Fin 2) K) (A : SpecialLinearGroup (Fin 2) K) :
    ((h : Matrix (Fin 2) (Fin 2) K) * A *
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
  have h1 : (h : Matrix (Fin 2) (Fin 2) K).det *
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, A.det_coe, mul_one, h1]

@[expose] def sl2ConjFun (h : GL (Fin 2) K) (A : SpecialLinearGroup (Fin 2) K) :
    SpecialLinearGroup (Fin 2) K :=
  ⟨(h : Matrix (Fin 2) (Fin 2) K) * A * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
    det_gl2_conj_eq_one h A⟩

@[simp] theorem coe_sl2ConjFun (h : GL (Fin 2) K) (A : SpecialLinearGroup (Fin 2) K) :
    ((sl2ConjFun h A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (h : Matrix (Fin 2) (Fin 2) K) * A *
        ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl

theorem sl2ConjFun_sl2ConjFun (g h : GL (Fin 2) K) (A : SpecialLinearGroup (Fin 2) K) :
    sl2ConjFun g (sl2ConjFun h A) = sl2ConjFun (g * h) A := by
  apply Subtype.ext
  simp only [coe_sl2ConjFun, Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

theorem sl2ConjFun_one (A : SpecialLinearGroup (Fin 2) K) : sl2ConjFun 1 A = A := by
  apply Subtype.ext
  simp

@[expose] def sl2Conj (h : GL (Fin 2) K) : MulAut (SpecialLinearGroup (Fin 2) K) where
  toFun := sl2ConjFun h
  invFun := sl2ConjFun h⁻¹
  left_inv A := by rw [sl2ConjFun_sl2ConjFun, inv_mul_cancel, sl2ConjFun_one]
  right_inv A := by rw [sl2ConjFun_sl2ConjFun, mul_inv_cancel, sl2ConjFun_one]
  map_mul' A B := by
    apply Subtype.ext
    simp only [coe_sl2ConjFun, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
      Units.inv_mul_cancel_left]

@[simp] theorem coe_sl2Conj (h : GL (Fin 2) K) (A : SpecialLinearGroup (Fin 2) K) :
    ((sl2Conj h A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (h : Matrix (Fin 2) (Fin 2) K) * A *
        ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl

theorem sl2Conj_apply_sl2Conj (g h : GL (Fin 2) K) (A : SpecialLinearGroup (Fin 2) K) :
    sl2Conj g (sl2Conj h A) = sl2Conj (g * h) A :=
  sl2ConjFun_sl2ConjFun g h A

end Basic

section Lang

variable {K : Type} [Field K] [Finite K]

theorem exists_sl2_lang_conj (τ : K ≃+* K) (hτ : orderOf τ = 3)
    (θ : MulAut (SpecialLinearGroup (Fin 2) K)) (N Ni : Matrix (Fin 2) (Fin 2) K)
    (hN : N * Ni = 1)
    (hθN : ∀ A : SpecialLinearGroup (Fin 2) K,
      (θ A : Matrix (Fin 2) (Fin 2) K) = N * (A : Matrix (Fin 2) (Fin 2) K).map τ * Ni)
    (hθ : θ ^ 3 = 1) :
    ∃ h : GL (Fin 2) K, ∀ A : SpecialLinearGroup (Fin 2) K,
      (θ A : Matrix (Fin 2) (Fin 2) K) =
        (h : Matrix (Fin 2) (Fin 2) K) *
          (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A *
            (h : Matrix (Fin 2) (Fin 2) K)).map τ *
          ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  classical
  set φ : Matrix (Fin 2) (Fin 2) K →+* Matrix (Fin 2) (Fin 2) K := τ.toRingHom.mapMatrix with hφ
  have hN' : Ni * N = 1 := mul_eq_one_comm.1 hN
  have hφ3 : ∀ M, φ (φ (φ M)) = M := by
    intro M
    ext i j
    simp [hφ, RingHom.mapMatrix_apply, Matrix.map_apply, cube_apply_of_orderOf_eq_three hτ]
  have hθ' : ∀ A : SpecialLinearGroup (Fin 2) K,
      (θ A : Matrix (Fin 2) (Fin 2) K) = N * φ A * Ni := hθN
  set c : Matrix (Fin 2) (Fin 2) K := N * φ N * φ (φ N) with hc
  set ci : Matrix (Fin 2) (Fin 2) K := φ (φ Ni) * φ Ni * Ni with hci
  have hcci : c * ci = 1 := by
    have e1 : φ (φ N) * φ (φ Ni) = 1 := by rw [← map_mul, ← map_mul, hN, map_one, map_one]
    have e2 : φ N * φ Ni = 1 := by rw [← map_mul, hN, map_one]
    calc c * ci = N * (φ N * (φ (φ N) * φ (φ Ni)) * φ Ni) * Ni := by
          simp only [hc, hci, Matrix.mul_assoc]
      _ = 1 := by rw [e1, mul_one, e2, mul_one, hN]
  have hcic : ci * c = 1 := mul_eq_one_comm.1 hcci
  have hcomm : ∀ A : SpecialLinearGroup (Fin 2) K,
      c * (A : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K) * c := by
    intro A
    have h1 := congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K))
      (mulAut_cube_apply θ hθ A)
    simp only [hθ', map_mul, hφ3, Matrix.mul_assoc] at h1
    have key : c * (A : Matrix (Fin 2) (Fin 2) K) * ci = A := by
      calc c * (A : Matrix (Fin 2) (Fin 2) K) * ci
          = N * (φ N * (φ (φ N) * ((A : Matrix (Fin 2) (Fin 2) K) *
              (φ (φ Ni) * (φ Ni * Ni))))) := by
            simp only [hc, hci, Matrix.mul_assoc]
        _ = A := h1
    calc c * (A : Matrix (Fin 2) (Fin 2) K)
        = c * A * (ci * c) := by rw [hcic, Matrix.mul_one]
      _ = (c * A * ci) * c := by simp only [Matrix.mul_assoc]
      _ = A * c := by rw [key]
  obtain ⟨s, hs⟩ := scalar_of_commute_u2_l2 c (hcomm (u2 1)) (hcomm (l2 1))
  have hNdet : N.det ≠ 0 := by
    have := congrArg Matrix.det hN
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hAi3 : Ai τ N 3 = c := by
    have e : (1 : Matrix (Fin 2) (Fin 2) K).map τ = 1 := Matrix.map_one τ (map_zero τ) (map_one τ)
    show N * (N * (N * (1 : Matrix (Fin 2) (Fin 2) K).map τ).map τ).map τ = N * φ N * φ (φ N)
    rw [e]
    show N * φ (N * φ (N * 1)) = N * φ N * φ (φ N)
    rw [mul_one, map_mul, mul_assoc]
  obtain ⟨l, B, hl, hB, hlB⟩ := hilbert90_matrix τ N hNdet s (by rw [hτ, hAi3, hs])
  have hN1 : (l • N) * (l⁻¹ • Ni) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hl, one_smul, hN]
  have hN1' : (l⁻¹ • Ni) * (l • N) = 1 := mul_eq_one_comm.1 hN1
  have hBdet : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have hBBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBdet
  have hBiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBdet
  refine ⟨⟨B, B⁻¹, hBBi, hBiB⟩, fun A => ?_⟩
  have hshape := lang_conj_shape φ (l • N) (l⁻¹ • Ni) B B⁻¹ hN1' hBBi hlB A
  have hscal : (l • N) * φ A * (l⁻¹ • Ni) = N * φ A * Ni := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hl,
      one_smul]
  show (θ A : Matrix (Fin 2) (Fin 2) K) = B * (B⁻¹ * A * B).map τ * B⁻¹
  rw [hθ' A, ← hscal, hshape]
  rfl

end Lang

section Fixed

variable {K : Type} [Field K] {τ : K ≃+* K} {F : Subfield K}

theorem fixed_eq_map_sl2Range (hFτ : ∀ x, x ∈ F ↔ τ x = x)
    (θ : MulAut (SpecialLinearGroup (Fin 2) K)) (h : GL (Fin 2) K)
    (hθ : ∀ A : SpecialLinearGroup (Fin 2) K, (θ A : Matrix (Fin 2) (Fin 2) K) =
      (h : Matrix (Fin 2) (Fin 2) K) *
        (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A *
          (h : Matrix (Fin 2) (Fin 2) K)).map τ *
        ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :
    {A | θ A = A} =
      ((sl2Range F K).map (sl2Conj h).toMonoidHom : Set (SpecialLinearGroup (Fin 2) K)) := by
  ext A
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · intro hA
    refine ⟨sl2Conj h⁻¹ A, ?_, ?_⟩
    · rw [mem_sl2Range_iff_map_eq hFτ]
      have h1 : (A : Matrix (Fin 2) (Fin 2) K) =
          (h : Matrix (Fin 2) (Fin 2) K) *
            (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A *
              (h : Matrix (Fin 2) (Fin 2) K)).map τ *
            ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        have := hθ A
        rwa [hA] at this
      show (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A *
          (h : Matrix (Fin 2) (Fin 2) K)).map τ =
        ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * (h : Matrix (Fin 2) (Fin 2) K)
      calc (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A *
            (h : Matrix (Fin 2) (Fin 2) K)).map τ
          = ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((h : Matrix (Fin 2) (Fin 2) K) *
              (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A *
                (h : Matrix (Fin 2) (Fin 2) K)).map τ *
              ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
            (h : Matrix (Fin 2) (Fin 2) K) := by
            simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one]
        _ = _ := by rw [← h1]
    · show sl2Conj h (sl2Conj h⁻¹ A) = A
      rw [sl2Conj_apply_sl2Conj, mul_inv_cancel]
      exact sl2ConjFun_one A
  · rintro ⟨y, hy, rfl⟩
    show θ (sl2Conj h y) = sl2Conj h y
    apply Subtype.ext
    rw [hθ (sl2Conj h y)]
    have e : ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (sl2Conj h y : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K) = y := by
      simp only [coe_sl2Conj, Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul,
        Matrix.mul_one]
    rw [e, (mem_sl2Range_iff_map_eq hFτ y).1 hy]
    rfl

end Fixed

section Sup

variable {K : Type} [Field K] [Finite K] {τ : K ≃+* K}
  {F : Subfield K}

theorem sup_map_sl2Conj_eq_top (hK : ringChar K ≠ 2) (hτ : orderOf τ = 3)
    (hFτ : ∀ x, x ∈ F ↔ τ x = x) (hF : 5 ≤ Nat.card F) (g₁ g₂ : GL (Fin 2) K)
    (hne : (sl2Range F K).map (sl2Conj g₁).toMonoidHom ≠
      (sl2Range F K).map (sl2Conj g₂).toMonoidHom) :
    (sl2Range F K).map (sl2Conj g₁).toMonoidHom ⊔ (sl2Range F K).map (sl2Conj g₂).toMonoidHom =
      ⊤ := by
  have h3 : Module.finrank F K = 3 := finrank_fixedField_eq_three hτ hFτ
  set R : Subgroup (SpecialLinearGroup (Fin 2) K) := sl2Range F K with hR
  set S₃ : Subgroup (SpecialLinearGroup (Fin 2) K) :=
    R.map (sl2Conj (g₁⁻¹ * g₂)).toMonoidHom with hS₃
  have hS₂ : R.map (sl2Conj g₂).toMonoidHom = S₃.map (sl2Conj g₁).toMonoidHom := by
    rw [hS₃, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun A => ?_
    show sl2ConjFun g₂ A = sl2ConjFun g₁ (sl2ConjFun (g₁⁻¹ * g₂) A)
    rw [sl2ConjFun_sl2ConjFun, mul_inv_cancel_left]
  have hcard : Nat.card S₃ = Nat.card R :=
    Subgroup.card_map_of_injective (sl2Conj _).injective
  have hne' : S₃ ≠ R := by
    intro h
    apply hne
    rw [hS₂, h]
  have htop := CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.sl2_range_sup_eq_top h3 hK hF S₃
    hcard hne'
  rw [hS₂, ← Subgroup.map_sup, htop, Subgroup.map_top,
    MonoidHom.range_eq_top.2 (sl2Conj g₁).surjective]

theorem sl2_closure_fixed_of_ne (hK : ringChar K ≠ 2) (hτ : orderOf τ = 3)
    (hFτ : ∀ x, x ∈ F ↔ τ x = x) (hF : 5 ≤ Nat.card F)
    (θ₁ θ₂ : MulAut (SpecialLinearGroup (Fin 2) K)) (N₁ Ni₁ N₂ Ni₂ : Matrix (Fin 2) (Fin 2) K)
    (hN₁ : N₁ * Ni₁ = 1) (hN₂ : N₂ * Ni₂ = 1)
    (hθ₁ : ∀ A : SpecialLinearGroup (Fin 2) K,
      (θ₁ A : Matrix (Fin 2) (Fin 2) K) = N₁ * (A : Matrix (Fin 2) (Fin 2) K).map τ * Ni₁)
    (hθ₂ : ∀ A : SpecialLinearGroup (Fin 2) K,
      (θ₂ A : Matrix (Fin 2) (Fin 2) K) = N₂ * (A : Matrix (Fin 2) (Fin 2) K).map τ * Ni₂)
    (h₁ : θ₁ ^ 3 = 1) (h₂ : θ₂ ^ 3 = 1) (hne : {A | θ₁ A = A} ≠ {A | θ₂ A = A}) :
    Subgroup.closure ({A | θ₁ A = A} ∪ {A | θ₂ A = A}) = ⊤ := by
  obtain ⟨g₁, hg₁⟩ := exists_sl2_lang_conj τ hτ θ₁ N₁ Ni₁ hN₁ hθ₁ h₁
  obtain ⟨g₂, hg₂⟩ := exists_sl2_lang_conj τ hτ θ₂ N₂ Ni₂ hN₂ hθ₂ h₂
  have hC₁ := fixed_eq_map_sl2Range hFτ θ₁ g₁ hg₁
  have hC₂ := fixed_eq_map_sl2Range hFτ θ₂ g₂ hg₂
  rw [hC₁, hC₂, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  refine sup_map_sl2Conj_eq_top hK hτ hFτ hF g₁ g₂ ?_
  intro h
  apply hne
  rw [hC₁, hC₂, h]

end Sup

section Main

variable {K : Type} [Field K] [Finite K]

theorem sl2_closure_fixed_pair (hK : ringChar K ≠ 2) (τ : K ≃+* K) (hτ : orderOf τ = 3)
    {F : Subfield K} (hFτ : ∀ x, x ∈ F ↔ τ x = x) (hF : 5 ≤ Nat.card F)
    (θ₁ θ₂ β : MulAut (SpecialLinearGroup (Fin 2) K)) (N₁ Nb : GL (Fin 2) K)
    (hθ₁ : ∀ A : SpecialLinearGroup (Fin 2) K, (θ₁ A : Matrix (Fin 2) (Fin 2) K) =
      N₁ * (A : Matrix (Fin 2) (Fin 2) K).map τ *
        ((N₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (hβ : ∀ A : SpecialLinearGroup (Fin 2) K, (β A : Matrix (Fin 2) (Fin 2) K) =
      Nb * (A : Matrix (Fin 2) (Fin 2) K) * ((Nb⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (hθ₂ : θ₂ = θ₁ * β)
    (hNb : ¬ ∃ c : K, (Nb : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) c)
    (h₁ : θ₁ ^ 3 = 1) (h₂ : θ₂ ^ 3 = 1) :
    Subgroup.closure ({A | θ₁ A = A} ∪ {A | θ₂ A = A}) = ⊤ := by
  classical
  set φ : Matrix (Fin 2) (Fin 2) K →+* Matrix (Fin 2) (Fin 2) K := τ.toRingHom.mapMatrix with hφ
  have hmap : ∀ M : Matrix (Fin 2) (Fin 2) K, M.map τ = φ M := fun M => rfl
  have hθ₂N : ∀ A : SpecialLinearGroup (Fin 2) K, (θ₂ A : Matrix (Fin 2) (Fin 2) K) =
      ((N₁ : Matrix (Fin 2) (Fin 2) K) * (Nb : Matrix (Fin 2) (Fin 2) K).map τ) *
        (A : Matrix (Fin 2) (Fin 2) K).map τ *
        (((Nb⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map τ *
          ((N₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    intro A
    rw [hθ₂, MulAut.mul_apply, hθ₁, hβ]
    simp only [hmap, map_mul, Matrix.mul_assoc]
  have hN₂ : ((N₁ : Matrix (Fin 2) (Fin 2) K) * (Nb : Matrix (Fin 2) (Fin 2) K).map τ) *
      (((Nb⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map τ *
        ((N₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    have e : φ (Nb : Matrix (Fin 2) (Fin 2) K) *
        φ ((Nb⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    simp only [hmap, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (φ (Nb : Matrix (Fin 2) (Fin 2) K)), e, Matrix.one_mul, Units.mul_inv]
  obtain ⟨g₁, hg₁⟩ := exists_sl2_lang_conj τ hτ θ₁ N₁
    ((N₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (Units.mul_inv N₁) hθ₁ h₁
  have hC₁ := fixed_eq_map_sl2Range hFτ θ₁ g₁ hg₁
  have hne : {A | θ₁ A = A} ≠ {A | θ₂ A = A} := by
    intro heq
    have hcomm : ∀ y ∈ sl2Range F K,
        (((g₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (Nb : Matrix (Fin 2) (Fin 2) K) *
          (g₁ : Matrix (Fin 2) (Fin 2) K)) * (y : Matrix (Fin 2) (Fin 2) K) =
        (y : Matrix (Fin 2) (Fin 2) K) *
          (((g₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (Nb : Matrix (Fin 2) (Fin 2) K) *
            (g₁ : Matrix (Fin 2) (Fin 2) K)) := by
      intro y hy
      have hA1 : θ₁ (sl2Conj g₁ y) = sl2Conj g₁ y := by
        have : sl2Conj g₁ y ∈
            ((sl2Range F K).map (sl2Conj g₁).toMonoidHom : Set (SpecialLinearGroup (Fin 2) K)) :=
          ⟨y, hy, rfl⟩
        rw [← hC₁] at this
        exact this
      have hA2 : θ₂ (sl2Conj g₁ y) = sl2Conj g₁ y := by
        have : sl2Conj g₁ y ∈ {A | θ₁ A = A} := hA1
        rw [heq] at this
        exact this
      have hβA : β (sl2Conj g₁ y) = sl2Conj g₁ y := by
        apply θ₁.injective
        rw [hA1]
        calc θ₁ (β (sl2Conj g₁ y)) = θ₂ (sl2Conj g₁ y) := by rw [hθ₂, MulAut.mul_apply]
          _ = sl2Conj g₁ y := hA2
      have hm : (Nb : Matrix (Fin 2) (Fin 2) K) * (sl2Conj g₁ y : Matrix (Fin 2) (Fin 2) K) *
          ((Nb⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          (sl2Conj g₁ y : Matrix (Fin 2) (Fin 2) K) := by
        rw [← hβ]
        exact congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hβA
      exact commute_of_conj_commute (mul_comm_of_conj_eq_self hm)
    have hu : u2 (1 : K) ∈ sl2Range F K := by simpa using u2_mem_sl2Range (F := F) (K := K) 1
    have hl : l2 (1 : K) ∈ sl2Range F K := by simpa using l2_mem_sl2Range (F := F) (K := K) 1
    obtain ⟨s, hs⟩ := scalar_of_commute_u2_l2 _ (hcomm _ hu) (hcomm _ hl)
    exact hNb ⟨s, eq_scalar_of_conj_eq_scalar hs⟩
  exact sl2_closure_fixed_of_ne hK hτ hFτ hF θ₁ θ₂ N₁
    ((N₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) _ _ (Units.mul_inv N₁) hN₂ hθ₁ hθ₂N h₁ h₂
    hne

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

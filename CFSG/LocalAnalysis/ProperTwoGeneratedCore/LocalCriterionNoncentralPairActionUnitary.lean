module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFrobenius

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

@[expose] def UnitaryAutomorphismRealization : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (J : HermitianForm 3 K) (f : ℕ), 2 ≤ f →
    Nat.card K = (2 ^ f) ^ 2 → Nat.card {x : K // J.conj x = x} = 2 ^ f →
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
    ∀ β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ (σ : K ≃+* K) (A : GL (Fin 3) K), A ∈ J.unitarySubgroup ∧
        ∀ g : J.specialSubgroup,
          ((β ⟨ProjGenLinGroup.mk (g : GL (Fin 3) K), Subgroup.mem_map_of_mem _ g.2⟩ :
              ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
            ProjGenLinGroup.mk (A * GeneralLinearGroup.map σ.toRingHom (g : GL (Fin 3) K) * A⁻¹)

variable {K : Type} [Field K]

theorem exists_smul_of_mk_eq {g₁ g₂ : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk g₁ = ProjGenLinGroup.mk g₂) :
    ∃ c : K, c ≠ 0 ∧ (g₂ : Matrix (Fin 3) (Fin 3) K) = c • (g₁ : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  refine ⟨u, u.ne_zero, ?_⟩
  rw [← hu, Units.val_mul, GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.scalar_apply, mul_comm]

theorem upper_conj_entries {M A N : Matrix (Fin 3) (Fin 3) K} (h : M * A = A * N)
    (hA10 : A 1 0 = 0) (hA20 : A 2 0 = 0) (hA21 : A 2 1 = 0) (hA00 : A 0 0 ≠ 0)
    (hA11 : A 1 1 ≠ 0) (hN10 : N 1 0 = 0) (hN20 : N 2 0 = 0) (hN21 : N 2 1 = 0)
    (hN00 : N 0 0 = 1) (hN11 : N 1 1 = 1) :
    M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 0 = 1 ∧ M 1 1 = 1 ∧
      M 0 1 * A 1 1 = A 0 0 * N 0 1 := by
  have e : ∀ i j, (M * A) i j = (A * N) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e10 := e 1 0
  have e20 := e 2 0
  have e01 := e 0 1
  have e11 := e 1 1
  have e21 := e 2 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hA10, hA20, hA21, hN10, hN20, hN21, hN00,
    hN11, mul_zero, zero_mul, add_zero, zero_add, mul_one] at e00 e10 e20 e01 e11 e21
  have h00 : M 0 0 = 1 := mul_right_cancel₀ hA00 (by rw [one_mul]; exact e00)
  have h10 : M 1 0 = 0 := by
    rcases mul_eq_zero.mp e10 with h | h
    · exact h
    · exact absurd h hA00
  have h20 : M 2 0 = 0 := by
    rcases mul_eq_zero.mp e20 with h | h
    · exact h
    · exact absurd h hA00
  rw [h10, zero_mul, zero_add] at e11
  rw [h20, zero_mul, zero_add] at e21
  refine ⟨h10, h20, ?_, h00, mul_right_cancel₀ hA11 (by rw [one_mul]; exact e11), ?_⟩
  · rcases mul_eq_zero.mp e21 with h | h
    · exact h
    · exact absurd h hA11
  · rw [h00, one_mul] at e01
    exact add_left_cancel (e01.trans (add_comm _ _))

theorem central_root_conj_entries {A : Matrix (Fin 3) (Fin 3) K} {b c : K} (hA : A.det ≠ 0)
    (hb : b ≠ 0)
    (h : A * !![1, 0, 1; 0, 1, 0; 0, 0, 1] = c • (!![1, 0, b; 0, 1, 0; 0, 0, 1] * A)) :
    A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 ∧ A 0 0 = b * A 2 2 := by
  have e : ∀ i j, (A * !![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) i j =
      (c • (!![1, 0, b; 0, 1, 0; 0, 0, 1] * A) : Matrix (Fin 3) (Fin 3) K) i j :=
    fun i j => by rw [h]
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e22 := e 2 2
  have e01 := e 0 1
  have e02 := e 0 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] at e10 e11 e12
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] at e22 e01 e02
  simp at e10 e11 e12 e22 e01 e02
  have hc : c = 1 := by
    by_contra hc
    have hc' : (1 : K) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    have zero_of (x : K) (hx : x = c * x) : x = 0 := by
      have : ((1 : K) - c) * x = 0 := by rw [sub_mul, one_mul, ← hx, sub_self]
      exact (mul_eq_zero.mp this).resolve_left hc'
    have h10 := zero_of _ e10
    have h11 := zero_of _ e11
    rw [h10, zero_add] at e12
    have h12 := zero_of _ e12
    apply hA
    rw [Matrix.det_fin_three, h10, h11, h12]
    ring
  subst hc
  simp only [one_mul] at e12 e22 e01 e02
  have h10 : A 1 0 = 0 := by linear_combination e12
  have h20 : A 2 0 = 0 := by linear_combination e22
  have h21 : A 2 1 = 0 := by
    have : b * A 2 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_left hb
  exact ⟨h10, h20, h21, by linear_combination e02⟩

@[expose] def centralCoord [CharP K 2] (J : HermitianForm 3 K) (s : K) (hs : J.conj s = s) :
    hermitianUnipotentCoord J :=
  ⟨(0, s), by simp [hs, CharTwo.add_self_eq_zero]⟩

theorem centralCoord_matrix [CharP K 2] (J : HermitianForm 3 K) (s : K) (hs : J.conj s = s) :
    (hermitianUnipotentGL J (centralCoord J s hs) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, s; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [centralCoord, hermitianUnipotentMatrix]

variable [Finite K]

theorem unitary_realized_involution_fixed (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (θ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (hθθ : ∀ x, θ (θ x) = x)
    (hθB : ∀ x ∈ unitaryCoordinateStabilizer J 0, θ x ∈ unitaryCoordinateStabilizer J 0)
    (σ : K ≃+* K) (A : GL (Fin 3) K)
    (hθ : ∀ g : J.specialSubgroup,
      ((θ ⟨ProjGenLinGroup.mk (g : GL (Fin 3) K), Subgroup.mem_map_of_mem _ g.2⟩ :
          ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A * GeneralLinearGroup.map σ.toRingHom (g : GL (Fin 3) K) * A⁻¹)) :
    ∀ x ∈ unitaryCoordinateStabilizer J 0, orderOf x = 2 → θ x = x := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hconj : ∀ c : K, J.conj c = c ^ 2 ^ f :=
    huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hcard hfixed
  have hσconj : ∀ c : K, J.conj (σ c) = σ (J.conj c) := fun c => by
    rw [hconj, hconj, map_pow]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinv, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  have hreal : ∀ (y : ProjectiveSpecialUnitaryMatrixGroup J) (M : GL (Fin 3) K),
      (y : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M →
      (θ y : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A * GeneralLinearGroup.map σ.toRingHom M * A⁻¹) := by
    intro y M hyM
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp y.2
    have hy : y = ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ := Subtype.ext hgy.symm
    have key : ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom g) =
        ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom M) := by
      rw [← ProjGenLinGroup.map_mk, ← ProjGenLinGroup.map_mk, hgy, hyM]
    rw [hy, hθ ⟨g, hg⟩, map_mul, map_mul, map_mul, map_mul, key]
  have hdetA : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact (GeneralLinearGroup.det A).ne_zero
  let ψ := hermitianUnipotentPSU J hJ
  have hψ (z : hermitianUnipotentCoord J) : ((ψ z : ProjectiveSpecialUnitaryMatrixGroup J) :
      ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (hermitianUnipotentGL J z) := rfl
  have hone : J.conj 1 = 1 := map_one _
  have h₁ : ψ (centralCoord J 1 hone) ∈ unitaryCoordinateStabilizer J 0 ∧
      orderOf (ψ (centralCoord J 1 hone)) = 2 :=
    (hinv _).mpr ⟨1, _, by rw [hone, CharTwo.add_self_eq_zero], one_ne_zero,
      centralCoord_matrix J 1 hone, hψ _⟩
  obtain ⟨b, M', hb, hb0, hM', hθ₁⟩ := (hinv (θ (ψ (centralCoord J 1 hone)))).mp
    ⟨hθB _ h₁.1, by rw [MulEquiv.orderOf_eq]; exact h₁.2⟩
  have hσ₁ : GeneralLinearGroup.map σ.toRingHom (hermitianUnipotentGL J (centralCoord J 1 hone)) =
      hermitianUnipotentGL J (centralCoord J 1 hone) := by
    apply GeneralLinearGroup.ext
    intro i j
    rw [GeneralLinearGroup.map_apply, centralCoord_matrix]
    fin_cases i <;> fin_cases j <;> simp
  have h₂ := hreal _ _ (hψ (centralCoord J 1 hone))
  rw [hσ₁, hθ₁] at h₂
  obtain ⟨c, -, hc⟩ := exists_smul_of_mk_eq h₂
  have hmat : (A : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 1; 0, 1, 0; 0, 0, 1] =
      c • (!![1, 0, b; 0, 1, 0; 0, 0, 1] * (A : Matrix (Fin 3) (Fin 3) K)) := by
    rw [← centralCoord_matrix J 1 hone, ← hM', ← Units.val_mul, ← Matrix.smul_mul, ← hc,
      ← Units.val_mul, inv_mul_cancel_right]
  obtain ⟨hA10, hA20, hA21, hA00b⟩ := central_root_conj_entries hdetA hb0 hmat
  have hb' : J.conj b = b := (CharTwo.add_eq_zero.mp hb).symm
  have hdet3 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    have h := hdetA
    rw [Matrix.det_fin_three, hA10, hA20, hA21] at h
    simpa using h
  have hA00 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul hdet3)
  have hA11 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hdet3)
  have hcentral : ∀ (s t : K) (hs : J.conj s = s) (ht : J.conj t = t), t = b * σ s →
      θ (ψ (centralCoord J s hs)) = ψ (centralCoord J t ht) := by
    intro s t hs ht hst
    apply Subtype.ext
    rw [hreal _ _ (hψ _), hψ]
    congr 1
    rw [mul_inv_eq_iff_eq_mul]
    apply GeneralLinearGroup.ext
    intro i j
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_three]
    simp only [GeneralLinearGroup.map_apply, centralCoord_matrix]
    fin_cases i <;> fin_cases j <;> simp [hA10, hA20, hA21, hst, hA00b]
    ring
  have hsq : ∀ a : K, σ (σ a) = a := by
    have key : ∀ a : K, a * ((A : Matrix (Fin 3) (Fin 3) K) 1 1 *
        σ ((A : Matrix (Fin 3) (Fin 3) K) 1 1)) = (A : Matrix (Fin 3) (Fin 3) K) 0 0 *
          σ ((A : Matrix (Fin 3) (Fin 3) K) 0 0) * σ (σ a) := by
      intro a
      obtain ⟨y, hy⟩ := huppert_II_10_4_trace_surjective J (2 ^ f) hcard hfixed (a * J.conj a)
        (by rw [map_mul, J.conj_involutive, mul_comm])
      let z : hermitianUnipotentCoord J := ⟨(a, y), by
        change y + J.conj y + a * J.conj a = 0
        rw [hy]
        exact CharTwo.add_self_eq_zero _⟩
      have hNe : ∀ i j, (GeneralLinearGroup.map σ.toRingHom (hermitianUnipotentGL J z) :
          Matrix (Fin 3) (Fin 3) K) i j = σ (!![1, a, y; 0, 1, -J.conj a; 0, 0, 1] i j) :=
        fun i j => by rw [GeneralLinearGroup.map_apply]; rfl
      have hy₁ := hreal (ψ z) _ (hψ z)
      have hy₂ := hreal _ _ hy₁
      rw [hθθ, hψ] at hy₂
      obtain ⟨c₂, -, hc₂⟩ := exists_smul_of_mk_eq hy₂
      set M₁ := A * GeneralLinearGroup.map σ.toRingHom (hermitianUnipotentGL J z) * A⁻¹
      have hM₁A : (M₁ : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
          (A : Matrix (Fin 3) (Fin 3) K) * (GeneralLinearGroup.map σ.toRingHom
            (hermitianUnipotentGL J z) : Matrix (Fin 3) (Fin 3) K) := by
        rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
      obtain ⟨m10, m20, m21, m00, m11, m01⟩ := upper_conj_entries hM₁A hA10 hA20 hA21 hA00 hA11
        (by rw [hNe]; simp) (by rw [hNe]; simp) (by rw [hNe]; simp) (by rw [hNe]; simp)
        (by rw [hNe]; simp)
      have hM₂A : ((A * GeneralLinearGroup.map σ.toRingHom M₁ * A⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
            (A : Matrix (Fin 3) (Fin 3) K) *
              (GeneralLinearGroup.map σ.toRingHom M₁ : Matrix (Fin 3) (Fin 3) K) := by
        rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
      obtain ⟨-, -, -, n00, -, n01⟩ := upper_conj_entries hM₂A hA10 hA20 hA21 hA00 hA11
        (by rw [GeneralLinearGroup.map_apply, m10, map_zero])
        (by rw [GeneralLinearGroup.map_apply, m20, map_zero])
        (by rw [GeneralLinearGroup.map_apply, m21, map_zero])
        (by rw [GeneralLinearGroup.map_apply, m00, map_one])
        (by rw [GeneralLinearGroup.map_apply, m11, map_one])
      have hσapp : ∀ x : K, σ.toRingHom x = σ x := fun _ => rfl
      rw [GeneralLinearGroup.map_apply, hσapp] at n01
      rw [hNe] at m01
      have e00 := congrFun (congrFun hc₂ 0) 0
      have e01 := congrFun (congrFun hc₂ 0) 1
      simp only [Matrix.smul_apply, smul_eq_mul, hermitianUnipotentGL_val,
        hermitianUnipotentMatrix_eq] at e00 e01
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, mul_one] at e00 e01 m01
      rw [n00] at e00
      rw [← e00, one_mul] at e01
      rw [e01] at n01
      have hσm := congrArg σ m01
      rw [map_mul, map_mul] at hσm
      calc a * ((A : Matrix (Fin 3) (Fin 3) K) 1 1 * σ ((A : Matrix (Fin 3) (Fin 3) K) 1 1)) =
            a * (A : Matrix (Fin 3) (Fin 3) K) 1 1 * σ ((A : Matrix (Fin 3) (Fin 3) K) 1 1) := by
              ring
        _ = _ := by rw [n01, mul_assoc, hσm, ← mul_assoc]
    have hP : (A : Matrix (Fin 3) (Fin 3) K) 1 1 * σ ((A : Matrix (Fin 3) (Fin 3) K) 1 1) ≠ 0 :=
      mul_ne_zero hA11 ((map_ne_zero σ).mpr hA11)
    have h1 := key 1
    rw [one_mul, map_one, map_one, mul_one] at h1
    rw [h1] at hP
    intro a
    have h2 := key a
    rw [h1] at h2
    exact (mul_left_cancel₀ hP ((mul_comm _ a).trans h2)).symm
  have hσ2 : σ ^ 2 = 1 := RingEquiv.ext fun a => hsq a
  have hfix₀ : ∀ c : K, J.conj c = c → σ c = c := by
    intro c hc
    by_cases hσ1 : σ = 1
    · rw [hσ1]
      rfl
    · have hcard' : Nat.card K = 2 ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
      obtain ⟨s, -, hs, hfrob, -⟩ := finite_field_involution_exact (by omega) hcard' σ hσ2 hσ1
      rw [hfrob, show s = f by omega, ← hconj, hc]
  have hb1 : b = 1 := by
    have e1 := hcentral 1 b hone hb' (by rw [map_one, mul_one])
    have e2 := hcentral b (b * b) hb' (by rw [map_mul, hb']) (by rw [hfix₀ b hb'])
    have e3 := hθθ (ψ (centralCoord J 1 hone))
    rw [e1, e2] at e3
    have e4 : b * b = 1 :=
      congrArg (fun z : hermitianUnipotentCoord J => z.1.2) (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ e3)
    have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
    have e5 : (b + 1) * (b + 1) = 0 := by linear_combination e4 + (b + 1) * htwo
    exact CharTwo.add_eq_zero.mp (mul_self_eq_zero.mp e5)
  intro x hxB hx2
  obtain ⟨s, M, hs, -, hM, hxM⟩ := (hinv x).mp ⟨hxB, hx2⟩
  have hs' : J.conj s = s := (CharTwo.add_eq_zero.mp hs).symm
  have hx : x = ψ (centralCoord J s hs') := by
    apply Subtype.ext
    rw [hxM, hψ]
    congr 1
    apply GeneralLinearGroup.ext
    intro i j
    rw [hM, centralCoord_matrix]
  rw [hx]
  exact hcentral s s hs' hs' (by rw [hb1, one_mul, hfix₀ s hs'])

end CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

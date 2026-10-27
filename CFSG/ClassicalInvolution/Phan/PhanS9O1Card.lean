module

public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
import TauCeti.Algebra.Group.Units.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open TauCeti QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution

section Spin

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)] [Nontrivial V] {Q : QuadraticForm K V}

theorem ker_spinToOrthogonal_subset (hQ : Q.Nondegenerate) :
    ((spinToOrthogonal Q).ker : Set (spinGroup Q)) ⊆ {1, spinGroup.negOne Q hQ.ne_zero} := by
  intro x hx
  have h1 : spinToOrthogonal Q x = 1 := hx
  have h2 : x ∈ (spinToSpecialOrthogonal Q).ker := by
    rw [MonoidHom.mem_ker]
    apply QuadraticMap.specialOrthogonalToOrthogonal_injective
    rw [specialOrthogonalToOrthogonal_spinToSpecialOrthogonal, h1, map_one]
  exact (mem_ker_spinToSpecialOrthogonal_iff Q hQ x).1 h2

theorem card_ker_spinToOrthogonal_le (hQ : Q.Nondegenerate) :
    Nat.card (spinToOrthogonal Q).ker ≤ 2 := by
  have h : Nat.card (spinToOrthogonal Q).ker =
      ((spinToOrthogonal Q).ker : Set (spinGroup Q)).ncard := Nat.card_coe_set_eq _
  rw [h]
  calc Set.ncard ((spinToOrthogonal Q).ker : Set (spinGroup Q))
      ≤ Set.ncard ({1, spinGroup.negOne Q hQ.ne_zero} : Set (spinGroup Q)) :=
        Set.ncard_le_ncard (ker_spinToOrthogonal_subset hQ) (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem finite_spinGroup [Finite K] (hQ : Q.Nondegenerate) : Finite (spinGroup Q) := by
  rw [MonoidHom.finite_iff_finite_ker_range (spinToOrthogonal Q)]
  refine ⟨((Set.toFinite _).subset (ker_spinToOrthogonal_subset hQ)).to_subtype, ?_⟩
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) := inferInstance
  infer_instance

omit [Nontrivial V] in
theorem spinToOrthogonal_range_le_ker (hQ : Q.Nondegenerate) [Finite K] :
    (spinToOrthogonal Q).range ≤ (detSpinorNorm hQ).ker := by
  rintro _ ⟨x, rfl⟩
  rw [MonoidHom.mem_ker, detSpinorNorm_apply]
  refine Prod.ext ?_ ?_
  · rw [← specialOrthogonalToOrthogonal_spinToSpecialOrthogonal]
    exact QuadraticMap.orthogonalDet_specialOrthogonalToOrthogonal _
  · rw [← specialOrthogonalToOrthogonal_spinToSpecialOrthogonal, ← spinorNorm_apply]
    exact spinorNorm_spinToSpecialOrthogonal Q hQ x

omit [Nontrivial V] in
theorem four_le_card_range_detSpinorNorm [Finite K] (hQ : Q.Nondegenerate) {ν : K}
    (hν : ¬ IsSquare ν) {a b : V} (ha : Q a = 1) (hb : Q b = ν) :
    4 ≤ Nat.card (detSpinorNorm hQ).range := by
  classical
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact ⟨0, by simp⟩)
  have inva : Invertible (Q a) := invertibleOfNonzero (by rw [ha]; exact one_ne_zero)
  have invb : Invertible (Q b) := invertibleOfNonzero (by rw [hb]; exact hν0)
  set Ψ := detSpinorNorm hQ with hΨ
  set sa := TauCeti.QuadraticMap.reflectionOrthogonal Q a with hsa
  set sb := TauCeti.QuadraticMap.reflectionOrthogonal Q b with hsb
  have hu₁ : unitOfInvertible (Q a) = 1 := Units.ext (by simp [ha])
  set c : Multiplicative (SquareClassGroup K) := squareClassHom (unitOfInvertible (Q b)) with hc
  have hΨa : Ψ sa = (-1, 1) := by
    rw [hsa, hΨ, detSpinorNorm_reflectionOrthogonal, hu₁, map_one]
  have hΨb : Ψ sb = (-1, c) := by
    rw [hsb, hΨ, detSpinorNorm_reflectionOrthogonal]
  have hneg : (-1 : Kˣ) ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun u : Kˣ => (u : K)) h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have hc1 : c ≠ 1 := by
    intro h
    have h1 : unitOfInvertible (Q b) ∈ (squareClassHom (K := K)).ker := h
    rw [ker_squareClassHom, Subgroup.mem_square, ← isSquare_units_val_iff] at h1
    exact hν (by simpa [hb] using h1)
  have hΨab : Ψ (sa * sb) = (1, c) := by
    rw [map_mul, hΨa, hΨb]
    ext
    · simp
    · simp
  have hsub : ({(1, 1), (-1, 1), (-1, c), (1, c)} :
      Set (Kˣ × Multiplicative (SquareClassGroup K))) ⊆ (Ψ.range : Set _) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1, by rw [map_one]; rfl⟩
    · exact ⟨sa, hΨa⟩
    · exact ⟨sb, hΨb⟩
    · exact ⟨sa * sb, hΨab⟩
  have hcard : ({(1, 1), (-1, 1), (-1, c), (1, c)} :
      Set (Kˣ × Multiplicative (SquareClassGroup K))).ncard = 4 := by
    have d2 : (((1 : Kˣ), (1 : Multiplicative (SquareClassGroup K))) ∉
        ({(-1, 1), (-1, c), (1, c)} : Set _)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, Prod.mk.injEq]
      exact ⟨fun h => hneg h.1.symm, fun h => hneg h.1.symm, fun h => hc1 h.2.symm⟩
    have d3 : (((-1 : Kˣ), (1 : Multiplicative (SquareClassGroup K))) ∉
        ({(-1, c), (1, c)} : Set _)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, Prod.mk.injEq]
      exact ⟨fun h => hc1 h.2.symm, fun h => hneg h.1⟩
    have d4 : ((-1 : Kˣ), c) ≠ (1, c) := fun h => hneg (congrArg Prod.fst h)
    rw [Set.ncard_insert_of_notMem d2, Set.ncard_insert_of_notMem d3, Set.ncard_pair d4]
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard] at h
  have h' : Nat.card Ψ.range =
      (Ψ.range : Set (Kˣ × Multiplicative (SquareClassGroup K))).ncard :=
    Nat.card_coe_set_eq (Ψ.range : Set (Kˣ × Multiplicative (SquareClassGroup K)))
  rw [h']
  exact h

theorem two_mul_card_spinGroup_le [Finite K] (hQ : Q.Nondegenerate) {ν : K} (hν : ¬ IsSquare ν)
    {a b : V} (ha : Q a = 1) (hb : Q b = ν) :
    2 * Nat.card (spinGroup Q) ≤ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have e1 := Subgroup.card_ker_mul_card_range (spinToOrthogonal Q)
  have e2 := Subgroup.card_ker_mul_card_range (detSpinorNorm hQ)
  have h1 : Nat.card (spinToOrthogonal Q).range ≤ Nat.card (detSpinorNorm hQ).ker :=
    Subgroup.card_le_of_le (spinToOrthogonal_range_le_ker hQ)
  have h2 := card_ker_spinToOrthogonal_le hQ
  have h3 := four_le_card_range_detSpinorNorm hQ hν ha hb
  calc 2 * Nat.card (spinGroup Q)
      = 2 * (Nat.card (spinToOrthogonal Q).ker * Nat.card (spinToOrthogonal Q).range) := by
        rw [e1]
    _ ≤ 2 * (2 * Nat.card (detSpinorNorm hQ).ker) := by gcongr
    _ = 4 * Nat.card (detSpinorNorm hQ).ker := by ring
    _ ≤ Nat.card (detSpinorNorm hQ).range * Nat.card (detSpinorNorm hQ).ker := by gcongr
    _ = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by rw [mul_comm, e2]

end Spin

section Comparison

variable {K : Type*} [Field K] {V₀ V : Type*} [AddCommGroup V₀] [Module K V₀] [AddCommGroup V]
  [Module K V]

theorem card_orthogonalGroup_le_of_similar (Q₀ : QuadraticForm K V₀) (Q : QuadraticForm K V)
    (e : V₀ ≃ₗ[K] V) {c : K} (hc : c ≠ 0) (h : ∀ v, Q (e v) = c * Q₀ v)
    [Finite (TauCeti.QuadraticMap.orthogonalGroup Q₀)] :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) ≤
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₀) := by
  have hmem : ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
      e.trans ((g : V ≃ₗ[K] V).trans e.symm) ∈ TauCeti.QuadraticMap.orthogonalGroup Q₀ := by
    intro g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    have h1 := h (e.symm ((g : V ≃ₗ[K] V) (e v)))
    rw [LinearEquiv.apply_symm_apply, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 g.2,
      h v] at h1
    exact (mul_left_cancel₀ hc h1).symm
  refine Nat.card_le_card_of_injective (fun g => ⟨_, hmem g⟩) fun g g' hgg' => ?_
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  have := congrArg (fun k : TauCeti.QuadraticMap.orthogonalGroup Q₀ =>
    e ((k : V₀ ≃ₗ[K] V₀) (e.symm x))) hgg'
  simpa using this

end Comparison

end CFSG.ClassicalInvolution.PhanB3.S

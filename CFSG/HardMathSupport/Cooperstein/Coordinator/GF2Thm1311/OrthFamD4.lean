module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthKlein

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped Pointwise

theorem exists_conj_mem_of_odd_index {R : Type*} [Group R] [Finite R] {H : Subgroup R}
    (hodd : Odd H.index) {B : Subgroup R} (hB : ∀ b ∈ B, b * b = 1) :
    ∃ β : R, ∀ b ∈ B, β * b * β⁻¹ ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 B := fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hB g g.2)⟩
  have hmod := hP.card_modEq_card_fixedPoints (R ⧸ H)
  have hcard : Nat.card (R ⧸ H) = H.index := (Subgroup.index_eq_card H).symm
  have hfix : (MulAction.fixedPoints B (R ⧸ H)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Nat.card (MulAction.fixedPoints B (R ⧸ H)) = 0 := by simp [hne]
    rw [h0, hcard] at hmod
    have := (Nat.modEq_zero_iff_dvd.mp hmod)
    obtain ⟨m, hm⟩ := hodd
    omega
  obtain ⟨q, hq⟩ := hfix
  induction q using QuotientGroup.induction_on with
  | H x =>
    refine ⟨x⁻¹, fun b hb => ?_⟩
    have h1 : (⟨b, hb⟩ : B) • (QuotientGroup.mk x : R ⧸ H) = QuotientGroup.mk x := hq ⟨b, hb⟩
    have h2 : (QuotientGroup.mk (b * x) : R ⧸ H) = QuotientGroup.mk x := h1
    rw [QuotientGroup.eq] at h2
    have : (b * x)⁻¹ * x = x⁻¹ * b⁻¹ * x := by group
    rw [this] at h2
    have h3 := H.inv_mem h2
    simpa [mul_assoc] using h3

theorem ncard_orbit_odd {A X : Type*} [Group A] [MulAction A X] {F y z : X}
    (hsub : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z) {κ : A} (hκF : κ • F = F)
    (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z) :
    Odd (MulAction.orbit A F).ncard := by
  have hFy : F ≠ y := by
    intro h
    apply hyz
    rw [← hκy, ← h, hκF, h]
  have hFz : F ≠ z := by
    intro h
    apply hyz
    rw [← hκz, ← h, hκF, h]
  by_cases hy : ∃ a : A, a • F = y
  · obtain ⟨a, ha⟩ := hy
    have hz : (κ * a) • F = z := by rw [mul_smul, ha, hκy]
    have : MulAction.orbit A F = {F, y, z} := by
      ext x
      constructor
      · rintro ⟨b, rfl⟩
        rcases hsub b with h | h | h <;> simp [h]
      · intro hx
        rcases hx with rfl | rfl | rfl
        · exact MulAction.mem_orbit_self _
        · exact ⟨a, ha⟩
        · exact ⟨κ * a, hz⟩
    rw [this, Set.ncard_eq_three.mpr ⟨F, y, z, hFy, hFz, hyz, rfl⟩]
    exact ⟨1, rfl⟩
  · push Not at hy
    have hz : ∀ a : A, a • F ≠ z := by
      intro a ha
      apply hy (κ * a)
      rw [mul_smul, ha, hκz]
    have : MulAction.orbit A F = {F} := by
      ext x
      constructor
      · rintro ⟨b, rfl⟩
        rcases hsub b with h | h | h
        · simp [h]
        · exact absurd h (hy b)
        · exact absurd h (hz b)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact MulAction.mem_orbit_self _
    rw [this, Set.ncard_singleton]
    exact ⟨0, rfl⟩


theorem kleinBigInv_POmegaPlus_four {X : Type} [Group X] {m : ℕ} (hm : m ≠ 2)
    (h : StatedClassicalModel X .POmegaPlus 4 2 m) : KleinBigInv X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 2 m h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab' : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := CFSG.RankThree.PartOne.KLC.swap_data_coordinate K
  have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
      (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
    MulAction.index_stabilizer _ _
  have hodd : Odd (matrixProjectiveImage (coordinateQuadPlus 4 K)).index := by
    rw [← hEA, hst]
    refine ncard_orbit_odd (y := plusCX 4 K) (z := plusCXstar 4 K (by omega)) ?_ hκF hκy hκz hyz
    intro a
    have := hsub (MulAction.mem_orbit _ a)
    simpa using this
  have hK4 : Nat.card K = 4 → m = 2 := by
    intro h4
    rw [hK] at h4
    exact Nat.pow_right_injective (le_refl 2) (by simpa using h4)
  have : Finite (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := inferInstance
  exact KleinBigInv.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
    (kleinBigInv_orth (coordinateQuadPlus 4 K) (by omega) (fun h4 => absurd (hK4 h4) hm) hnd hT
      (commutator_coordinateQuadPlus 4 K (by omega)) hab'
      (fun B _ hsq _ _ => exists_conj_mem_of_odd_index hodd (B := B) hsq))

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

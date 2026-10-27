module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftGroup

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly.LowTwoRank

section Count

variable {K : Type} [Field K] [Finite K] {n : ℕ} {Y : Type} [Group Y] {L : Subgroup Y}

theorem card_units_eq_three (hK : Nat.card K = (2 ^ 1) ^ 2) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK]; norm_num

theorem scalar_mem_isoGroup (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n) c ∈
      isoGroup (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n := by
  set h := CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl with hh
  have hc3 : (c : K) ^ 3 = 1 := by
    have : c ^ 3 = 1 := by
      rw [← card_units_eq_three hK]
      exact pow_card_eq_one'
    simpa using congrArg Units.val this
  have hnorm : h.bar c * c = 1 := by
    rw [UnitaryFieldData.bar_apply, pow_one, ← pow_succ]
    exact hc3
  rw [mem_primeFormUnitary_one_iff_isometry]
  intro x y
  have hmv : ∀ z : Fin n → K,
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z =
        (c : K) • z := fun z => by
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    funext i
    simp [Matrix.mulVec_diagonal]
  rw [hmv, hmv]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  linear_combination (stdHermForm h n x y) * hnorm

theorem real_scalar_one (ρ : StatedSU n 2 K →* ↥L) (c : Kˣ) :
    Real ρ (GeneralLinearGroup.scalar (Fin n) c) 1 := fun g => by
  refine ⟨g, ?_, by simp⟩
  have hc : GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  rw [← Subgroup.mem_center_iff.mp hc (g : GL (Fin n) K)]
  group

theorem scalar_mem_liftGroup (hK : Nat.card K = (2 ^ 1) ^ 2) (ρ : StatedSU n 2 K →* ↥L)
    (U : Subgroup Y) (c : Kˣ) : GeneralLinearGroup.scalar (Fin n) c ∈ liftGroup hK ρ U :=
  ⟨scalar_mem_isoGroup hK c, 1, one_mem _, real_scalar_one ρ c⟩

theorem scalar_injective' (hn : 1 ≤ n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) (R := K)) := by
  intro c c' hcc
  have h1 := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hcc
  rw [GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

theorem real_elem_unique {hK : Nat.card K = (2 ^ 1) ^ 2} {ρ : StatedSU n 2 K →* ↥L}
    (hρ : Function.Surjective ρ) {U : Subgroup Y}
    (hUC : U ⊓ Subgroup.centralizer (L : Set Y) = ⊥) {A : GL (Fin n) K} {u u' : Y}
    (hA : A ∈ liftGroup hK ρ U) (hu : u ∈ U) (hu' : u' ∈ U) (hr : Real ρ A u)
    (hr' : Real ρ A u') : u = u' := by
  have h1 : Real ρ (A⁻¹ * A) (u⁻¹ * u') := real_mul (real_inv hA.1 hr) hr'
  rw [inv_mul_cancel] at h1
  have h2 := mem_centralizer_of_real_one ρ hρ h1
  have h3 : u⁻¹ * u' ∈ U ⊓ Subgroup.centralizer (L : Set Y) :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hu) hu', h2⟩
  rw [hUC, Subgroup.mem_bot, inv_mul_eq_one] at h3
  exact h3

theorem exists_liftGroup_hom (hn : 4 ≤ n) (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n 2 K →* ↥L) (hρ : Function.Surjective ρ)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n 2 K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n 2 K)))
    (hρc : ∀ g, ρ g ∈ Subgroup.center ↥L ↔ ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K))
    {U : Subgroup Y} (hU : U ≤ Subgroup.normalizer (L : Set Y)) (hU3 : IsPGroup 3 U)
    (hUC : U ⊓ Subgroup.centralizer (L : Set Y) = ⊥) :
    ∃ π : ↥(liftGroup hK ρ U) →* ↥U, Function.Surjective π ∧
      (∀ A : ↥(liftGroup hK ρ U), Real ρ A.1 (π A : Y)) ∧
      ∀ A, π A = 1 ↔ A.1 ∈ StatedScalars (Fin n) K := by
  have hex : ∀ A : ↥(liftGroup hK ρ U), ∃ u : ↥U, Real ρ A.1 (u : Y) := fun A => by
    obtain ⟨u, hu, hr⟩ := A.2.2
    exact ⟨⟨u, hu⟩, hr⟩
  choose π hπ using hex
  have hmul : ∀ A B : ↥(liftGroup hK ρ U), π (A * B) = π A * π B := fun A B => by
    apply Subtype.ext
    exact real_elem_unique hρ hUC (A * B).2 (π (A * B)).2 (mul_mem (π A).2 (π B).2) (hπ _)
      (real_mul (hπ A) (hπ B))
  refine ⟨MonoidHom.mk' π hmul, ?_, hπ, ?_⟩
  · intro u
    obtain ⟨A, hA, hr⟩ := exists_mem_liftGroup_real hn hK ρ e hρe hU hU3 u u.2
    refine ⟨⟨A, hA⟩, Subtype.ext ?_⟩
    exact real_elem_unique hρ hUC hA (π ⟨A, hA⟩).2 u.2 (hπ ⟨A, hA⟩) hr
  · intro A
    constructor
    · intro h1
      have hr : Real ρ A.1 1 := by
        have := hπ A
        have h2 : π A = 1 := h1
        rwa [h2] at this
      have := real_unique hn hK ρ hρc hr (real_one ρ)
      rw [mul_one] at this
      simpa using inv_mem this
    · rintro ⟨c, hc⟩
      have hAc : A.1 = GeneralLinearGroup.scalar (Fin n) c := hc.symm
      have hr : Real ρ A.1 1 := by
        rw [hAc]
        exact real_scalar_one ρ c
      apply Subtype.ext
      exact real_elem_unique hρ hUC A.2 (π A).2 (one_mem _) (hπ A) hr

theorem card_liftGroup (hn : 4 ≤ n) (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n 2 K →* ↥L) (hρ : Function.Surjective ρ)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n 2 K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n 2 K)))
    (hρc : ∀ g, ρ g ∈ Subgroup.center ↥L ↔ ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K))
    {U : Subgroup Y} (hU : U ≤ Subgroup.normalizer (L : Set Y)) (hU3 : IsPGroup 3 U)
    (hUC : U ⊓ Subgroup.centralizer (L : Set Y) = ⊥) :
    Nat.card (liftGroup hK ρ U) = 3 * Nat.card U := by
  obtain ⟨π, hπs, -, hπk⟩ := exists_liftGroup_hom hn hK ρ hρ e hρe hρc hU hU3 hUC
  have hker : Nat.card π.ker = 3 := by
    rw [← card_units_eq_three hK]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun c : Kˣ => (⟨⟨GeneralLinearGroup.scalar (Fin n) c, scalar_mem_liftGroup hK ρ U c⟩,
        (hπk _).mpr ⟨c, rfl⟩⟩ : π.ker)) ⟨?_, ?_⟩)
    · intro c c' hcc
      exact scalar_injective' (by omega) (congrArg (fun x : π.ker => x.1.1) hcc)
    · rintro ⟨A, hA⟩
      obtain ⟨c, hc⟩ := (hπk A).mp hA
      exact ⟨c, Subtype.ext (Subtype.ext hc)⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker, hker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv, mul_comm]

end Count

end CFSG.HardMathSupport.Curtis.UnitaryLevi

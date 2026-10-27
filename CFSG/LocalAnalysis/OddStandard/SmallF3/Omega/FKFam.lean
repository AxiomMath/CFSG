module

public import CFSG.ClassicalInvolution.Q3.Q3MFODOrb
public import CFSG.ClassicalInvolution.Q3.Q3MFODData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKIso

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution.G2D4Models.Twin (z0 z2 z3 spinAction_z2_mul_z3
  spinAction_z3_mul_z0 spinAction_z0_mul_z2)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance (statedPointFamily)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (stated_pointFamily_orbit_subset)
open CFSG.ClassicalInvolution.Q3
open CFSG.Open (StatedProj StatedOmega StatedQuadPlus)
open CFSG.LieType.Universal.Spin (spinAction quadPlus coe_quadPlus)
open scoped Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Spin₈" => spinGroup (quadPlus 4 (GaloisField 3 1))

local notation "Proj₈" => StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))

local notation "𝔉" => statedPointFamily (coe_quadPlus 4 (GaloisField 3 1))

theorem fk_fix_mul_of_fix (φ : MulAut Spin₈) (h0 : φ (z0 𝔽₃) = z0 𝔽₃) (h2 : φ (z2 𝔽₃) = z2 𝔽₃)
    (h3 : φ (z3 𝔽₃) = z3 𝔽₃) :
    φ (z2 𝔽₃ * z3 𝔽₃) = z2 𝔽₃ * z3 𝔽₃ ∧ φ (z3 𝔽₃ * z0 𝔽₃) = z3 𝔽₃ * z0 𝔽₃ ∧
      φ (z0 𝔽₃ * z2 𝔽₃) = z0 𝔽₃ * z2 𝔽₃ :=
  ⟨by rw [map_mul, h2, h3], by rw [map_mul, h3, h0], by rw [map_mul, h0, h2]⟩

theorem fk_b_mem_center : z2 𝔽₃ * z3 𝔽₃ ∈ Subgroup.center Spin₈ :=
  (fk_mem_center_iff _).mpr (Or.inl spinAction_z2_mul_z3)

theorem fk_b₁_mem_center : z3 𝔽₃ * z0 𝔽₃ ∈ Subgroup.center Spin₈ :=
  (fk_mem_center_iff _).mpr (Or.inr spinAction_z3_mul_z0)

theorem fk_b₂_mem_center : z0 𝔽₃ * z2 𝔽₃ ∈ Subgroup.center Spin₈ :=
  (fk_mem_center_iff _).mpr (Or.inr spinAction_z0_mul_z2)

theorem fk_sim_of_pres (β : MulAut Spin₈) (hβ : Q3MFOD.Pres β) :
    ∃ (A : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) (μ : 𝔽₃), μ ≠ 0 ∧
      (∀ v, quadPlus 4 𝔽₃ (A v) = μ * quadPlus 4 𝔽₃ v) ∧
        ∀ x, spinAction (quadPlus 4 𝔽₃) (β x) = A * spinAction (quadPlus 4 𝔽₃) x * A⁻¹ := by
  have : Group.IsPerfect Spin₈ :=
    CFSG.LieType.Universal.Spin.isPerfect_spinGroup_quadPlus (by norm_num)
  exact Q3MFOD.exists_sim_of_mat3 ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three β
    (Q3MFOD.spin_plus4_sim_of_family β (Q3MFOD.descAut β) (Q3MFOD.descAut_apply β) hβ)

private theorem fk_neg_ne_one :
    (LinearEquiv.neg 𝔽₃ : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) ≠ 1 := by
  intro h
  have h' := congrFun (LinearEquiv.congr_fun h (Pi.single (Sum.inl 0) 1)) (Sum.inl 0)
  exact Q3MFOD.neg_one_ne_one_of_card_three
    ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three (by simpa using h')

private theorem fk_pres_of_fix (α τ : MulAut Spin₈)
    (h : Q3MFOD.descAut α • (Q3MFOD.descAut τ • 𝔉) = Q3MFOD.descAut τ • 𝔉) :
    Q3MFOD.Pres (τ⁻¹ * α * τ) := by
  unfold Q3MFOD.Pres
  rw [Q3MFOD.descAut_mul, Q3MFOD.descAut_mul, Q3MFOD.descAut_inv, mul_smul, mul_smul, h,
    inv_smul_smul]

theorem fk_pres_conj {ρ α : MulAut Spin₈}
    (h1 : ρ (z2 𝔽₃ * z3 𝔽₃) = z3 𝔽₃ * z0 𝔽₃) (h2 : ρ (z3 𝔽₃ * z0 𝔽₃) = z0 𝔽₃ * z2 𝔽₃)
    (h3 : ρ (z0 𝔽₃ * z2 𝔽₃) = z2 𝔽₃ * z3 𝔽₃)
    (a0 : α (z2 𝔽₃ * z3 𝔽₃) = z2 𝔽₃ * z3 𝔽₃) (a1 : α (z3 𝔽₃ * z0 𝔽₃) = z3 𝔽₃ * z0 𝔽₃)
    (a2 : α (z0 𝔽₃ * z2 𝔽₃) = z0 𝔽₃ * z2 𝔽₃) :
    Q3MFOD.Pres (ρ⁻¹ * α * ρ) ∧ Q3MFOD.Pres ((ρ * ρ)⁻¹ * α * (ρ * ρ)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθb : spinAction (quadPlus 4 𝔽₃) (z2 𝔽₃ * z3 𝔽₃) = 1 := spinAction_z2_mul_z3
  have hθb₁ : spinAction (quadPlus 4 𝔽₃) (z3 𝔽₃ * z0 𝔽₃) = LinearEquiv.neg 𝔽₃ :=
    spinAction_z3_mul_z0
  have hθb₂ : spinAction (quadPlus 4 𝔽₃) (z0 𝔽₃ * z2 𝔽₃) = LinearEquiv.neg 𝔽₃ :=
    spinAction_z0_mul_z2
  have hb1 : z2 𝔽₃ * z3 𝔽₃ ≠ 1 := by
    intro h
    have h' : z0 𝔽₃ * z2 𝔽₃ = 1 := ρ.injective (by rw [h3, h, map_one])
    rw [h', map_one] at hθb₂
    exact fk_neg_ne_one hθb₂.symm
  have hbb₁ : z2 𝔽₃ * z3 𝔽₃ ≠ z3 𝔽₃ * z0 𝔽₃ := fun h =>
    fk_neg_ne_one (by rw [← hθb₁, ← h, hθb])
  have hbb₂ : z2 𝔽₃ * z3 𝔽₃ ≠ z0 𝔽₃ * z2 𝔽₃ := fun h =>
    fk_neg_ne_one (by rw [← hθb₂, ← h, hθb])
  have hb₁b₂ : z3 𝔽₃ * z0 𝔽₃ ≠ z0 𝔽₃ * z2 𝔽₃ := fun h =>
    hbb₁ (ρ.injective (h1.trans (h.trans h2.symm)))
  let τ : Fin 3 → MulAut Spin₈ := ![1, ρ, ρ * ρ]
  let bb : Fin 3 → Spin₈ := ![z2 𝔽₃ * z3 𝔽₃, z3 𝔽₃ * z0 𝔽₃, z0 𝔽₃ * z2 𝔽₃]
  have hτb : ∀ i, τ i (z2 𝔽₃ * z3 𝔽₃) = bb i := by
    intro i
    fin_cases i
    · rfl
    · exact h1
    · show ρ (ρ (z2 𝔽₃ * z3 𝔽₃)) = _
      rw [h1, h2]
      rfl
  have hbbfix : ∀ i, α (bb i) = bb i := by
    intro i
    fin_cases i
    · exact a0
    · exact a1
    · exact a2
  have hbbinj : ∀ i j, bb i = bb j → i = j := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp only [bb] at h) <;>
      first
      | exact absurd h hbb₁
      | exact absurd h.symm hbb₁
      | exact absurd h hbb₂
      | exact absurd h.symm hbb₂
      | exact absurd h hb₁b₂
      | exact absurd h.symm hb₁b₂
  set G : Fin 3 → Set (Subgroup Proj₈) := fun i => Q3MFOD.descAut (τ i) • 𝔉 with hG
  have hGne : ∀ i j, i ≠ j → G i ≠ G j := by
    intro i j hij hGij
    apply hij
    apply hbbinj
    rw [← hτb i, ← hτb j]
    by_contra hne
    exact Q3MFOD.smul_ne_of_apply_ne hb1 (τ i) (τ j) hne hGij
  obtain ⟨C₁, C₂, hΦ⟩ : ∃ C₁ C₂ : Set (Subgroup Proj₈),
      ∀ Y ∈ MulAction.orbit (MulAut Proj₈) 𝔉, Y = 𝔉 ∨ Y = C₁ ∨ Y = C₂ :=
    ⟨_, _, fun Y hY => by
      simpa using stated_pointFamily_orbit_subset (K := 𝔽₃) (n := 4) rfl hY⟩
  have hGorb : ∀ i, G i ∈ MulAction.orbit (MulAut Proj₈) 𝔉 := fun i => MulAction.mem_orbit _ _
  have hcl : ∀ i : Fin 3, ∃ j, Q3MFOD.descAut α • G i = G j := by
    intro i
    by_contra hcon
    push Not at hcon
    have hy : Q3MFOD.descAut α • G i ∈ MulAction.orbit (MulAut Proj₈) 𝔉 :=
      ⟨Q3MFOD.descAut α * Q3MFOD.descAut (τ i), by
        show (Q3MFOD.descAut α * Q3MFOD.descAut (τ i)) • 𝔉 = Q3MFOD.descAut α • G i
        rw [mul_smul]⟩
    exact Q3MFOD.not_four_distinct ({𝔉, C₁, C₂} : Finset (Set (Subgroup Proj₈)))
      Finset.card_le_three (by simpa using hΦ _ hy) (by simpa using hΦ _ (hGorb 0))
      (by simpa using hΦ _ (hGorb 1)) (by simpa using hΦ _ (hGorb 2)) (hcon 0) (hcon 1) (hcon 2)
      (hGne 0 1 (by decide)) (hGne 0 2 (by decide)) (hGne 1 2 (by decide))
  have hfixG : ∀ i, Q3MFOD.descAut α • G i = G i := by
    intro i
    obtain ⟨j, hj⟩ := hcl i
    have hj' : Q3MFOD.descAut (α * τ i) • 𝔉 = Q3MFOD.descAut (τ j) • 𝔉 := by
      rw [Q3MFOD.descAut_mul, mul_smul]
      exact hj
    have hne : (α * τ i) (z2 𝔽₃ * z3 𝔽₃) = τ j (z2 𝔽₃ * z3 𝔽₃) := by
      by_contra hne
      exact Q3MFOD.smul_ne_of_apply_ne hb1 _ _ hne hj'
    have hij : i = j := hbbinj i j (by
      rw [← hbbfix i, ← hτb i, ← MulAut.mul_apply, hne, hτb j])
    subst hij
    exact hj
  have hP : ∀ i, Q3MFOD.Pres ((τ i)⁻¹ * α * τ i) := fun i => fk_pres_of_fix α (τ i) (hfixG i)
  exact ⟨hP 1, hP 2⟩

end CFSG.OddStandard.SmallF3.Omega

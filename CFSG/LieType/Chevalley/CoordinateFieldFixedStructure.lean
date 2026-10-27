module

public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.PerfectSimpleRoot

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise commutatorElement

theorem commutator_adjointGroup_eq_of_ringChar
    (τ : Tag) (K : Type) [Field K]
    (hK : ringChar K ≠ 2) : ⁅adjointGroup τ K, adjointGroup τ K⁆ = adjointGroup τ K := by
  have h := odd_characteristic_perfect τ K hK
  rw [commutator_def] at h
  have e := congrArg (Subgroup.map (adjointGroup τ K).subtype) h
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at e

theorem Chevalley_coordinate_field_fixed_structure
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) :
    (∃ e : MulAut (adjointGroup τ K), ∀ g : adjointGroup τ K,
      (e g : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (g : ModGL τ K)) ∧
    Function.Injective (baseChangeGL (τ := τ) (fixSubfield σ).subtype) ∧
    (∀ (g : ModGL τ (fixSubfield σ)) (b : Label τ),
      ((baseChangeGL (fixSubfield σ).subtype g : ModGL τ K) : Module.End K (RootModule τ K))
          (Finsupp.single b 1) =
        Finsupp.mapRange (fixSubfield σ).subtype (map_zero _)
          ((g : Module.End (fixSubfield σ) (RootModule τ (fixSubfield σ))) (Finsupp.single b 1))) ∧
    fixedFieldImage τ σ ≤ entrywiseFixedGroup τ σ ∧
    (entrywiseFixedGroup τ σ : Set (ModGL τ K)) =
      (entrywiseFixedTorus τ σ : Set (ModGL τ K)) * (fixedFieldImage τ σ : Set (ModGL τ K)) ∧
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).Normal ∧
    (∀ a b : ↥(entrywiseFixedGroup τ σ) ⧸
        (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ), a * b = b * a) ∧
    ⁅entrywiseFixedGroup τ σ, entrywiseFixedGroup τ σ⁆ = fixedFieldImage τ σ := by
  obtain ⟨h1, h2, h3, hJΓ, h5, hnormal, hcomm⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  refine ⟨h1, h2, h3, hJΓ, h5, hnormal, hcomm, le_antisymm ?_ ?_⟩
  ·
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hq := hcomm (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hq
    have hmem := Subgroup.mem_subgroupOf.1 hq
    have e : (((⟨a, ha⟩ * ⟨b, hb⟩ : entrywiseFixedGroup τ σ)⁻¹ *
        (⟨b, hb⟩ * ⟨a, ha⟩) : entrywiseFixedGroup τ σ) : ModGL τ K) = b⁻¹ * a⁻¹ * b * a := by
      simp [mul_assoc]
    rw [e] at hmem
    have hJn := hnormal
    have hinv : (b⁻¹ * a⁻¹ * b * a)⁻¹ ∈ fixedFieldImage τ σ := inv_mem hmem
    have hconj : b * a * (b⁻¹ * a⁻¹ * b * a)⁻¹ * (b * a)⁻¹ ∈ fixedFieldImage τ σ := by
      have := hJn.conj_mem ⟨_, hJΓ hinv⟩ (Subgroup.mem_subgroupOf.2 hinv)
        (⟨b, hb⟩ * ⟨a, ha⟩)
      simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
    have e2 : b * a * (b⁻¹ * a⁻¹ * b * a)⁻¹ * (b * a)⁻¹ = ⁅a, b⁆ := by
      rw [commutatorElement_def]
      group
    rwa [e2] at hconj
  ·
    have hk2 : ringChar (fixSubfield σ) ≠ 2 := by
      intro h
      have h0 : ((2 : ℕ) : fixSubfield σ) = 0 := by
        rw [← h]
        exact ringChar.Nat.cast_ringChar
      apply Ring.two_ne_zero hK
      have := congrArg (fixSubfield σ).subtype h0
      rw [map_natCast, map_zero] at this
      exact_mod_cast this
    have hJ : ⁅fixedFieldImage τ σ, fixedFieldImage τ σ⁆ = fixedFieldImage τ σ := by
      rw [fixedFieldImage, ← Subgroup.map_commutator,
        commutator_adjointGroup_eq_of_ringChar τ _ hk2]
    rw [← hJ]
    exact Subgroup.commutator_mono hJΓ hJΓ

end CFSG.LieType.Chevalley

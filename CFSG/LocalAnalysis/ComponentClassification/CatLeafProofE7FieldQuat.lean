module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieQuat

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups commutatorElement

theorem quatComponentForm_entrywiseFixedGroup
    (τ : Tag) (K : Type) [Field K] [Finite K] (hK : ringChar K ≠ 2) (σ : K ≃+* K)
    (i : Fin τ.rank) : QuatComponentForm (entrywiseFixedGroup τ σ) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨-, hinj, -, hJΓ, -, hJn, hcomm⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  let e : (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ) ≃*
      adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJΓ).trans
      (Subgroup.equivMapOfInjective (adjointGroup τ (fixSubfield σ)) _ hinj).symm
  have hk2 := ringChar_fixSubfield_ne_two hK σ
  obtain ⟨hsimp, hnab, -⟩ := odd_pinned_Chevalley_p_components τ (fixSubfield σ) hk2
  have hJq : CFSG.IsQuasisimple ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2
      (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  have hJc : CFSG.IsComponent ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)) :=
    ⟨hJq, Subgroup.Normal.isSubnormal hJn⟩
  have hΓJ : commutator (entrywiseFixedGroup τ σ) ≤
      (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h1 : QuotientGroup.mk'
        ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    exact (QuotientGroup.eq_one_iff _).mp h1
  intro L hL
  have hLL : ⁅L, L⁆ = L := LocalAnalysis.ComponentInitial.commutator_self_of_isQuasisimple
    ((AssemblyBPredicates.isQuasisimple_iff_native _).2 hL.1)
  have hLJ : L ≤ (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ) := by
    rw [← hLL]
    exact (Subgroup.commutator_mono le_top le_top).trans
      ((_root_.commutator_def _).symm.le.trans hΓJ)
  rcases LocalCores.distinct_components_commute hL hJc with h | h
  · rw [h]
    obtain ⟨hle, ⟨eSL⟩, -⟩ :=
      odd_arbitrary_root_pair_SL2_p_components τ (fixSubfield σ) hk2 (isRoot_single τ i)
    let φ : SL(2, fixSubfield σ) →* (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ) :=
      e.symm.toMonoidHom.comp ((Subgroup.inclusion hle).comp eSL.toMonoidHom)
    exact exists_quaternion_of_injective_SL hk2 φ
      (e.symm.injective.comp ((Subgroup.inclusion_injective hle).comp eSL.injective))
  · exfalso
    refine LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple
      ((AssemblyBPredicates.isQuasisimple_iff_native L).2 hL.1) ?_
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans (Subgroup.centralizer_le hLJ)

theorem quatComponentForm_quadratic_field
    (τ : Tag) (i : Fin τ.rank) {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K}
    {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : orderOf α = 2) : QuatComponentForm (fixedSubgroup α) := by
  classical
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2 * e) hp (by omega) (by rw [hKe, ← pow_mul, mul_comm])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq, ← hα, pow_orderOf_eq_one])
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))).map
      (adjointGroup τ K).subtype = entrywiseFixedGroup τ δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ K) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL τ K) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))) ≃*
      ↥(entrywiseFixedGroup τ δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  exact quatComponentForm_of_mulEquiv (e₁.trans e₂)
    (quatComponentForm_entrywiseFixedGroup τ K hK2 δ i)

theorem burgoyneE7FieldQuat_holds :
    ∀ (K : Type) [Field K] [Finite K] (p e : ℕ), p.Prime → p ≠ 2 → 1 ≤ e →
      Nat.card K = (p ^ e) ^ 2 → ∀ δ : K ≃+* K, (∀ c, δ c = c ^ (p ^ e)) →
      ∀ (α : MulAut (adjointGroup .E7 K)) (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ),
        (∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) = (g : ModGL .E7 K) *
          rootDiagUnit .E7 a * Units.map (entrywiseHom δ.toRingHom) (h : ModGL .E7 K) *
            (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹) → orderOf α = 2 →
        QuatComponentForm (fixedSubgroup α) :=
  fun _ _ _ _ _ hp hp2 he hKe δ hδ _ _ _ hαg hα =>
    quatComponentForm_quadratic_field .E7 ⟨0, by decide⟩ hp hp2 he hKe δ hδ hαg hα

end CFSG.ComponentClassification.CatLeafProof

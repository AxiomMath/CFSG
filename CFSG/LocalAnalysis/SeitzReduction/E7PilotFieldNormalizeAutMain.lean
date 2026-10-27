module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutDescent
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeExists

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem normalizationProperty_of_conj_of_extension {A B : Type} [Group A] [Group B] [Finite B]
    {j : A →* B} (hj : Function.Injective j) {β₀ : MulAut B}
    (hj₀ : j.range = perfectCore (fixedSubgroup β₀))
    (hdesc : ∀ β : MulAut B, β * β = 1 → Nonempty (perfectCore (fixedSubgroup β) ≃* A) →
      ∃ ψ : MulAut B, ψ * β * ψ⁻¹ = β₀)
    (hext : ∀ δ : MulAut A, ∃ δ' : MulAut B, ∀ a, δ' (j a) = j (δ a)) :
    NormalizationProperty j := by
  intro β hβ ε hε hεr
  let eε : A ≃* perfectCore (fixedSubgroup β) :=
    (MonoidHom.ofInjective hε).trans (MulEquiv.subgroupCongr hεr)
  obtain ⟨ψ, hψ⟩ := hdesc β hβ ⟨eε.symm⟩
  have hc : MulAut.congr ψ β = β₀ := by
    rw [← hψ]
    exact MulEquiv.ext fun _ => rfl
  have hrange : (ψ.toMonoidHom.comp ε).range = j.range := by
    rw [MonoidHom.range_comp, hεr, CFSG.Quasithin.map_perfectCore,
      ← CFSG.ComponentClassification.ExcSelector.fixedSubgroup_congr, hc, hj₀]
  have hinj : Function.Injective (ψ.toMonoidHom.comp ε) := ψ.injective.comp hε
  let δ : MulAut A := ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans
    (MonoidHom.ofInjective hj).symm
  have hδ : ∀ a, j (δ a) = ψ (ε a) := by
    intro a
    have h1 := (MonoidHom.ofInjective hj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hinj a))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ'⟩ := hext δ⁻¹
  refine ⟨δ' * ψ, fun a => ?_⟩
  rw [MulAut.mul_apply, ← hδ, hδ', MulAut.inv_apply, MulEquiv.symm_apply_apply]

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_natCard_fixSubfield {σ : K ≃+* K} (hσ : orderOf σ = 2) :
    ∃ g : ℕ, 1 ≤ g ∧ Nat.card (fixSubfield σ) = 2 ^ g ∧ Nat.card K = 2 ^ (2 * g) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hσσ : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨⟨m, hm⟩, hk, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.card_descentField hf hK hσσ hσ1
  refine ⟨f / 2, by omega, hk, ?_⟩
  rw [hK]
  congr 1
  omega

theorem natCard_coordinatePlus_fixSubfield_ne {σ : K ≃+* K} (hσ : orderOf σ = 2) (hn : 4 ≤ n) :
    Nat.card (matrixProjectiveDerived (coordinateQuadPlus n (fixSubfield σ))) ≠
      Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  intro hcard
  obtain ⟨g, hg, hk, hK⟩ := exists_natCard_fixSubfield hσ
  obtain ⟨-, -, h⟩ := OmegaPilot.lieModel_POmega_two_unique_classicalOrSuzuki_of_card_eq
    (Or.inl rfl) (lieModel_coordinatePlus (by omega) hK hn) (Or.inl (by decide))
    (lieModel_coordinatePlus hg hk hn) hcard
  omega

theorem normalizationProperty_incl {σ : K ≃+* K} (hσ : orderOf σ = 2) (hn : 5 ≤ n) :
    NormalizationProperty (incl (fixSubfield σ) (isExtension_coordinateQuadPlus n
      (fixSubfield σ)) : matrixProjectiveDerived (coordinateQuadPlus n (fixSubfield σ)) →*
        matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  obtain ⟨g, hg, hk, hK⟩ := exists_natCard_fixSubfield hσ
  have hext := isExtension_coordinateQuadPlus n (fixSubfield σ)
  have hσk : ∀ x, x ∈ fixSubfield σ ↔ σ x = x := fun x => Iff.rfl
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K (by omega)
  have hQne : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    exists_ne_zero_of_nondeg (by omega : 0 < 2 * n) hQ
  have hJ : ⁅subfieldDerivedImage (fixSubfield σ) hext, subfieldDerivedImage (fixSubfield σ) hext⁆ =
      subfieldDerivedImage (fixSubfield σ) hext :=
    commutator_range_of_commutator_top _ (commutator_top_coordinatePlus (by omega))
  refine normalizationProperty_of_conj_of_extension (incl_injective _ hext (by omega))
    (perfectCore_fixedSubgroup_fieldAutT (coordinateQuadPlus_fieldMap n σ) hσk hext hQne hJ).symm
    (fun β hβ hP => ?_) (exists_mulAut_incl_comm hn)
  exact exists_conj_eq_fieldAutT hσ hn (lieModel_coordinatePlus hg hk (by omega))
    (isQuasisimple_coordinatePlus (by omega)) (natCard_coordinatePlus_fixSubfield_ne hσ (by omega))
    hβ hP

end Model

section Transport

@[expose] noncomputable def leviHighModelEquiv (F : Type) [Field F] [Finite F] [CharP F 2] :
    E7Neighbour.high.levi F ≃* matrixProjectiveDerived (coordinateQuadPlus 6 F) :=
  (MulEquiv.subgroupCongr (E7Neighbour.levi_high F)).trans
    ((spinEquivPerpLevi F).symm.trans
      ((QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq (center_spinGroup_quadPlus_eq_bot F)).symm).trans
        ((CFSG.LieType.Universal.Spin.spinQuotientCenterEquivQuadPlus three_le_rank_D6).trans
          (coordinatePlusWitnessEquiv F (MulEquiv.refl _)))))

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

theorem normalizationProperty_leviInclusion_high (hσ : orderOf σ = 2)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) : NormalizationProperty (leviInclusion σ .high) := by
  have := finite_levi K .high
  exact NormalizationProperty.of_mulEquiv (normalizationProperty_incl hσ (by norm_num))
    (leviHighModelEquiv (fixSubfield σ)) (leviHighModelEquiv K) (leviBaseChange_injective _ _)
    (leviEntrywiseEquiv_mul_self hσ) (range_leviInclusion_eq_perfectCore hq)

end Transport

end CFSG.SeitzReduction.E7Pilot

module

public import CFSG.LocalAnalysis.OddStandard.ThmCSylowSL2
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
public import CFSG.LieType.Chevalley.GraphFixedOddPerfect
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.OddStandard.ThmC.Sylow

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.OddStandard.ThmC.T

theorem false_of_derivedCentralQuotient_D4_aux
    {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (σe : F ≃+* F) (h3 : σe ^ 3 = 1) {K : Type} [Group K] [Finite K] (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K))
    (e : K ≃* DerivedCentralQuotient (twistedFixedGroup .D4 F σe.toRingHom)) : False := by
  obtain ⟨ι, η, hι, hη, hcomm⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 F σe h3
  obtain ⟨-, -, hH⟩ := odd_diagram_fixed_root_group_perfect .D4 F hF σe
  have hZ := center_graphFixedRootGroup_eq_bot (t := .D4) (K := F) (σ := σe.toRingHom)
    σe.surjective
  let e₁ : ↥(graphFixedRootGroup .D4 F σe.toRingHom) ≃*
      ↥⁅twistedFixedGroup .D4 F σe.toRingHom, twistedFixedGroup .D4 F σe.toRingHom⁆ :=
    MulEquiv.subgroupCongr hH.symm
  let π : ↥(graphFixedRootGroup .D4 F σe.toRingHom) →*
      DerivedCentralQuotient (twistedFixedGroup .D4 F σe.toRingHom) :=
    (QuotientGroup.mk' _).comp e₁.toMonoidHom
  have hπ : Function.Injective π := by
    refine (injective_iff_map_eq_one π).2 fun x hx => ?_
    have h1 : e₁ x ∈ Subgroup.center
        ↥⁅twistedFixedGroup .D4 F σe.toRingHom, twistedFixedGroup .D4 F σe.toRingHom⁆ :=
      (QuotientGroup.eq_one_iff _).1 hx
    have h2 : x ∈ Subgroup.center ↥(graphFixedRootGroup .D4 F σe.toRingHom) := by
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro g
      apply e₁.injective
      rw [map_mul, map_mul]
      exact h1 (e₁ g)
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have h2 : ringChar (fixSubfield σe) ≠ 2 := by
    have hs : CharP ↥(fixSubfield σe) (ringChar F) :=
      ((fixSubfield σe).subtype.charP_iff Subtype.val_injective (ringChar F)).2 inferInstance
    rwa [ringChar.eq ↥(fixSubfield σe) (ringChar F)]
  exact not_isT_of_commuting_sl2 T hT hF h2 ((e.symm.toMonoidHom.comp π).comp ι)
    ((e.symm.toMonoidHom.comp π).comp η)
    (e.symm.injective.comp (hπ.comp hι)) (e.symm.injective.comp (hπ.comp hη))
    fun A B => by
      have : ι A * η B = η B * ι A := hcomm A B
      exact (Commute.map (Commute.map (show Commute (ι A) (η B) from this) π) e.symm.toMonoidHom)

theorem false_of_lieModel_d4
    {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : LieModel K .trialityD4 0 p f) (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) : False := by
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmodel⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨-, F, _, _, hF, σ, hσ, ⟨e⟩⟩ := hmodel
    have hq : Nat.card F = (p ^ f) ^ 3 := hF
    have hF2 : ringChar F ≠ 2 :=
      CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 (f := f * 3)
        (by rw [hq, ← pow_mul])
    have : Fintype F := Fintype.ofFinite F
    let σe : F ≃+* F :=
      RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
    have hσe : σe.toRingHom = σ := RingHom.ext fun _ => rfl
    have h3 : σe ^ 3 = 1 := by
      refine RingEquiv.ext fun c => ?_
      rw [ringEquiv_pow_three_apply]
      have hc : c ^ ((p ^ f) ^ 3) = c := by
        rw [← hq, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card c
      calc σe (σe (σe c)) = (((c ^ (p ^ f)) ^ (p ^ f)) ^ (p ^ f)) := by
            change σ (σ (σ c)) = _
            rw [hσ, hσ, hσ]
        _ = c ^ ((p ^ f) ^ 3) := by
            rw [← pow_mul, ← pow_mul]
            congr 1
            ring
        _ = c := hc
    rw [← hσe] at e
    exact false_of_derivedCentralQuotient_D4_aux hF2 σe h3 T hT e
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.OddStandard.ThmC.Sylow

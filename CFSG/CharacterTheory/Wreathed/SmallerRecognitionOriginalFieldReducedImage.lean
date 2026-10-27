module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldNested
public import CFSG.CharacterTheory.Wreathed.ReducedCentralizerInclusion

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open ReducedCentralizerInclusion
universe u v
variable {K : Type u} {H : Type v} [Group K] [Group H]

@[expose] def reducedCentralizerImageInclusion [Finite K]
    (O : Subgroup K) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (K ⧸ O)) [L.Normal] (hodd : Odd L.index)
    (v : K) (hv : orderOf v = 2) (D : Subgroup H)
    (E : Subgroup.centralizer {v} ⧸ CFSG.oddCore (Subgroup.centralizer {v}) ≃* D) :=
  E.toMonoidHom.comp (reducedCentralizerInjection O hO L hodd v hv)

theorem reducedCentralizerImageInclusion_data [Finite K]
    (O : Subgroup K) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (K ⧸ O)) [L.Normal] (hodd : Odd L.index)
    (v : K) (hv : orderOf v = 2) (D : Subgroup H)
    (E : Subgroup.centralizer {v} ⧸ CFSG.oddCore (Subgroup.centralizer {v}) ≃* D) :
    Function.Injective (reducedCentralizerImageInclusion O hO L hodd v hv D E) ∧
      (reducedCentralizerImageInclusion O hO L hodd v hv D E).range.Normal ∧
      Odd (reducedCentralizerImageInclusion O hO L hodd v hv D E).range.index ∧
      ∀ c : Subgroup.centralizer {v}, ∀ b : Subgroup.centralizer
        ({(⟨QuotientGroup.mk' O v, quotient_involution_mem O hO L hodd v hv⟩ : L)} : Set L),
        QuotientGroup.mk' O (c : K) = ((b : L) : K ⧸ O) →
        reducedCentralizerImageInclusion O hO L hodd v hv D E
          (QuotientGroup.mk' (CFSG.oddCore _) b) =
          E (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer {v})) c) := by
  let i := reducedCentralizerImageInclusion O hO L hodd v hv D E
  have hi : Function.Injective i :=
    E.injective.comp (reducedCentralizerInjection_injective O hO L hodd v hv)
  have hnormal : i.range.Normal := by
    rw [show i = E.toMonoidHom.comp (reducedCentralizerInjection O hO L hodd v hv) from rfl,
      MonoidHom.range_comp]
    exact (reducedCentralizerInjection_normal O hO L hodd v hv).map _ E.surjective
  have hindex : Odd i.range.index := by
    rw [show i = E.toMonoidHom.comp (reducedCentralizerInjection O hO L hodd v hv) from rfl,
      MonoidHom.range_comp, Subgroup.index_map_of_bijective E.bijective]
    exact reducedCentralizerInjection_odd_index O hO L hodd v hv
  refine ⟨hi, hnormal, hindex, ?_⟩
  intro c b hcb
  have hin : reducedCentralizerInjection O hO L hodd v hv
      (QuotientGroup.mk' (CFSG.oddCore _) b) =
      QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer {v})) c := by
    apply (reducedCentralizerEquiv O hO v hv).injective
    rw [reducedCentralizerInjection_mk, reducedCentralizerEquiv_mk]
    congr 1
    apply Subtype.ext
    exact hcb.symm
  change E (reducedCentralizerInjection O hO L hodd v hv _) = _
  rw [hin]

theorem reduced_centralizer_image_full_center [Finite K] [Finite H]
    (O : Subgroup K) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (K ⧸ O)) [L.Normal] (hodd : Odd L.index)
    (v : K) (hv : orderOf v = 2) (M D : Subgroup H) [M.Normal] [D.Normal]
    (hM : CFSG.IsQuasisimple M)
    (heven : Even (Nat.card (M ⧸ Subgroup.center M)))
    (htwo : IsPGroup 2 (Subgroup.center H))
    (hc : Subgroup.centralizer (M : Set H) = Subgroup.center H) (hDodd : Odd D.index)
    (E : Subgroup.centralizer {v} ⧸ CFSG.oddCore (Subgroup.centralizer {v}) ≃* D) :
    let B := Subgroup.centralizer
      ({(⟨QuotientGroup.mk' O v, quotient_involution_mem O hO L hodd v hv⟩ : L)} : Set L)
    let J := B ⧸ CFSG.oddCore B
    let i := D.subtype.comp (reducedCentralizerImageInclusion O hO L hodd v hv D E)
    (Subgroup.center J).map i = Subgroup.center H ∧
      ∃ hcenter : (Subgroup.center J).map i = Subgroup.center H,
        let j := injectiveFullCenterMap i hcenter
        Function.Injective j ∧
          (∀ b : J, j (QuotientGroup.mk' (Subgroup.center J) b) =
            QuotientGroup.mk' (Subgroup.center H) (i b)) ∧
          (CFSG.generalizedFitting (J ⧸ Subgroup.center J)).map j =
            CFSG.generalizedFitting (H ⧸ Subgroup.center H) ∧
          (∃ F : CFSG.generalizedFitting (J ⧸ Subgroup.center J) ≃*
            CFSG.generalizedFitting (H ⧸ Subgroup.center H),
            ∀ b : CFSG.generalizedFitting (J ⧸ Subgroup.center J),
              (F b : H ⧸ Subgroup.center H) = j (b : J ⧸ Subgroup.center J)) ∧
          IsSimpleGroup (CFSG.generalizedFitting (J ⧸ Subgroup.center J)) ∧
          (∃ a b : CFSG.generalizedFitting (J ⧸ Subgroup.center J), a * b ≠ b * a) ∧
          Subgroup.centralizer (CFSG.generalizedFitting (J ⧸ Subgroup.center J) :
            Set (J ⧸ Subgroup.center J)) = ⊥ := by
  obtain ⟨hi, hnormal, hindex, _⟩ :=
    reducedCentralizerImageInclusion_data O hO L hodd v hv D E
  exact nested_normal_odd_index_full_center_layer M D hM heven htwo hc hDodd
    (reducedCentralizerImageInclusion O hO L hodd v hv D E) hi hnormal hindex

end CFSG.Wreathed.SmallerRecognitionOriginalField

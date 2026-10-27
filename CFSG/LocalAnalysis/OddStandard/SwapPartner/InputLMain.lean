module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputL
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLComponent

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def FixedA8Lookup : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    CFSG.Blueprint.Catalog S → ∀ {σ : MulAut S}, orderOf σ = 2 →
      ∀ {D : Subgroup ↥(fixedSubgroup σ)}, CFSG.IsComponent D →
        Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin 8)) →
          (∃ m : ℕ, 5 ≤ m ∧ Nonempty (S ≃* alternatingGroup (Fin (2 * m)))) ∨
            CFSG.Blueprint.NativeSporadic.IsSporadic S .HS ∨
            CFSG.Blueprint.LieModel S .PSL 4 2 2 ∨
            (CFSG.Blueprint.NativeSporadic.IsSporadic S .McL ∧ Nat.card (center ↥D) = 2)

theorem nonExactShapeEightLookup_of_fixedA8Lookup (hL : FixedA8Lookup) :
    NonExactShapeEightLookup := by
  intro X _ _ t Sg V K hX hO hS hKl hc hA hne
  haveI : K.Characteristic := by
    subst hKl
    exact CFSG.LocalCores.layer_characteristic
  obtain ⟨hKp, hKs, hKn⟩ := hc.1
  haveI : IsSimpleGroup (K ⧸ center K) := hKs
  have hK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKp
  have hcat : CFSG.Blueprint.Catalog (K ⧸ center K) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hX K
      (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  have hσ := hS.orderOf_quotConj_eq_two hK hne hA
  have hD := hS.isComponent_fixedAbar hA
  have hA8 := hS.fixedAbar_quotCenter_equiv hA
  have hcard := hS.card_center_fixedAbar hA
  rcases hL (K ⧸ center K) hKn hcat hσ hD hA8 with
      ⟨m, -, ⟨e⟩⟩ | hHS | hL4 | ⟨-, h2⟩
  · exact Or.inl (nonExactShapeEight_of_alternating hS hKl hc hA hne e).1
  · exact Or.inr (Or.inl hHS)
  · exact Or.inr (Or.inr hL4)
  · rw [hcard] at h2
    omega

end CFSG.OddStandard.AltStdSec.SwapPartner

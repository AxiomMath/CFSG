module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackage
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageFactors
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageAtoms
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageConj

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] {L U P : Subgroup G} {ℳ : Set (Subgroup G)}

theorem exists_isGomiLeviData_of_isGomiLeviPackage [Finite G] (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (h : IsGomiLeviPackage L U P ℳ) :
    ∃ (D : Subgroup G) (𝒦 : Set (Subgroup G)), IsGomiLeviData L U P D 𝒦 := by
  obtain ⟨D, hD⟩ := exists_isGomiLeviCore P
  have hUP : U ≤ P := (le_inf hU.le Subgroup.le_normalizer).trans hBP.le
  have hDB : D ≤ L ⊓ normalizer (U : Set G) := hD.le_inf_normalizer hU hUP hPL
  obtain ⟨M₀, hM₀⟩ := h.nonempty hU hBP hPL
  refine ⟨D, (fun M => D ⊔ M) '' ℳ, ?_⟩
  have hsSup_le : sSup ℳ ≤ sSup ((fun M => D ⊔ M) '' ℳ) :=
    sSup_le fun M hM => le_sup_right.trans (le_sSup ⟨M, hM, rfl⟩)
  refine
    { pCoreOf_le := hD.pCoreOf_le
      le_inf_normalizer := hDB
      not_two_dvd := hD.not_two_dvd_relIndex hU hUP hPL
      commutator_le := hD.commutator_le
      le_of_mem := ?_
      le_parabolic := ?_
      parabolic_le_normalizer := ?_
      two_dvd := ?_
      commutator_le_of_ne := ?_
      inf_sSup_le := ?_
      sylow_le := ?_
      le_sup := ?_
      map_conj := ?_
      existsUnique_factor := ?_
      factor := ?_ }
  · rintro _ ⟨M, hM, rfl⟩; exact le_sup_left
  · rintro _ ⟨M, hM, rfl⟩; exact sup_le hD.le (h.le_parabolic M hM)
  · rintro _ ⟨M, hM, rfl⟩; exact h.le_normalizer_sup hD hM
  · rintro _ ⟨M, hM, rfl⟩; exact h.two_dvd_relIndex hD hM
  · rintro _ ⟨M₁, hM₁, rfl⟩ _ ⟨M₂, hM₂, rfl⟩ hne
    exact h.commutator_le_of_ne hD hM₁ hM₂ hne
  · rintro _ ⟨M, hM, rfl⟩; exact h.inf_sSup_le hD hM
  · have hR : pCoreOf 2 P ⊔ sSup ℳ ≤ sSup ((fun M => D ⊔ M) '' ℳ) :=
      sup_le (hD.pCoreOf_le.trans (le_sup_left.trans (le_sSup ⟨M₀, hM₀, rfl⟩))) hsSup_le
    exact h.sylow_le.trans hR
  · exact (h.le_sup_sSup hU hBP hPL).trans (sup_le_sup_left hsSup_le _)
  · rintro g ⟨⟨_, _⟩, hgP⟩
    exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mp (hD.normalizer_le hgP),
      fun K hK => h.map_conj_mem hU hBP hPL hD hgP hK⟩
  · intro A hA hAP; exact h.existsUnique_factor hD hDB hA hAP
  · rintro K ⟨M, hM, rfl⟩ _; exact h.factor_sup hD hDB hM

theorem gomiChevLeviDecomposition_of_gomiChevLeviPackage (h : GomiChevLeviPackage) :
    GomiChevLeviDecomposition := by
  intro G _ _ L U P hL hZ hU hBP hPL hat
  obtain ⟨ℳ, hℳ⟩ := h G L U P hL hZ hU hBP hPL hat
  exact exists_isGomiLeviData_of_isGomiLeviPackage hU hBP hPL.le hℳ

end CFSG.GroupTheory

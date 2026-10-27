module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinBasic

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

noncomputable def quotientFusionZStarEquiv {Y : Type*} [Group Y] (hZ : Open.fusionZStar Y = ⊥) :
    Y ⧸ Open.fusionZStar Y ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

noncomputable def equivOfFusionZStarEqBot {Y Y' : Type*} [Group Y] [Group Y']
    (hZ : Open.fusionZStar Y = ⊥) (e : Y ⧸ Open.fusionZStar Y ≃* Y') : Y ≃* Y' :=
  (quotientFusionZStarEquiv hZ).symm.trans e

theorem catalog_of_harrisF {p : ℕ} {Y : Type} [Group Y] (h : HarrisF p Y) :
    IsSimpleGroup Y ∧ Blueprint.Catalog Y := by
  unfold HarrisF at h
  cases h with
  | base hY =>
    obtain ⟨n, -, hm⟩ := hY
    exact ⟨isSimpleGroup_of_lieModel_psl2 hm, Blueprint.lieModel_catalog _ _ _ _ _ hm⟩
  | blowup _ hX hb => exact ⟨hb.2.1, hX⟩

theorem catalog_of_isOfType {p : ℕ} {Y : Type} [Group Y] [IsSimpleGroup Y]
    (h : IsOfType (HarrisF p) Y) : Blueprint.Catalog Y := by
  obtain ⟨-, Y', _, hY', ⟨e⟩⟩ := h
  obtain ⟨hs, hcat⟩ := catalog_of_harrisF hY'
  have hZ : Open.fusionZStar Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Open.fusionZStar Y) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (Y ⧸ Open.fusionZStar Y) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        exact QuotientGroup.eq.mpr (by rw [h]; trivial)
      have hsub' : Subsingleton Y' := e.symm.toEquiv.subsingleton
      exact not_nontrivial_iff_subsingleton.mpr hsub' hs.toNontrivial
  exact SectionRank.catalog_of_mulEquiv (equivOfFusionZStarEqBot hZ e) hcat

theorem harris36SimpleInput_of_rows
    (hA : HinFor fun Y _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n)))
    (hC : HinFor fun Y _ => Milestones.ClassicalRep Y)
    (hE : HinFor fun Y _ => Blueprint.ExceptionalRep Y)
    (hS : HinFor fun Y _ => Blueprint.NativeSporadic.SporadicRep Y) :
    Harris36SimpleInput := by
  intro Y _ _ _ hnab p m hp hp2 hm h16 hF h47 τ hτ hL
  rcases catalog_of_isOfType hF with ⟨q, -, ⟨e⟩⟩ | hY | hY | hY | hY
  · obtain ⟨a, b, hab⟩ := hnab
    exact (hab (e.injective (by rw [map_mul, map_mul, mul_comm]))).elim
  · exact hA Y hY hnab p m hp hp2 hm h16 h47 τ hτ hL
  · exact hC Y hY hnab p m hp hp2 hm h16 h47 τ hτ hL
  · exact hE Y hY hnab p m hp hp2 hm h16 h47 τ hτ hL
  · exact hS Y hY hnab p m hp hp2 hm h16 h47 τ hτ hL

end CFSG.ComponentClassification.HarrisLit.Hin

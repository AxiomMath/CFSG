module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Double
public import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

section Pairs

variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

theorem rankOne_twistedE6_zero :
    CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 0) = (nodeHom0 θ).range :=
  rankOne_eq_range_of_param (D := twistedDatum k θ) (i := nf 0) _ (rFixed_upper θ (nd 1) rfl rfl)
    (rFixed_lower θ (nd 1) rfl rfl) (rFixed_param_upper θ (nd 1) rfl rfl)
    (rFixed_param_lower θ (nd 1) rfl rfl)

theorem rankOne_twistedE6_one :
    CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 1) = (nodeHom1 θ).range :=
  rankOne_eq_range_of_param (D := twistedDatum k θ) (i := nf 1) _ (rFixed_upper θ (nd 3) rfl rfl)
    (rFixed_lower θ (nd 3) rfl rfl) (rFixed_param_upper θ (nd 3) rfl rfl)
    (rFixed_param_lower θ (nd 3) rfl rfl)

theorem rankOne_twistedE6_two :
    CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 2) =
      (nodeHom2 θ hθ).range :=
  rankOne_eq_range_of_param (D := twistedDatum k θ) (i := nf 2) _
    (slOrbitHom_upper_mem θ hθ _ rfl) (slOrbitHom_lower_mem θ hθ _ rfl)
    (slOrbitHom_param_upper θ hθ _ rfl) (slOrbitHom_param_lower θ hθ _ rfl)

theorem rankOne_twistedE6_three :
    CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 3) =
      (nodeHom3 θ hθ).range :=
  rankOne_eq_range_of_param (D := twistedDatum k θ) (i := nf 3) _
    (slOrbitHom_upper_mem θ hθ _ rfl) (slOrbitHom_lower_mem θ hθ _ rfl)
    (slOrbitHom_param_upper θ hθ _ rfl) (slOrbitHom_param_lower θ hθ _ rfl)

include hθ in
theorem iSup_rankOne_twistedE6 :
    ⨆ i : Fin (twistedDatum k θ).rank,
      CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup i = ⊤ :=
  iSup_rankOne_eq_top_of_ct (D := twistedDatum k θ)
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)) rfl

include hθ in
theorem commute_rankOne_twistedE6_zero_two :
    ∀ u ∈ CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 0),
      ∀ v ∈ CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 2), u * v = v * u := by
  intro u hu v hv
  rw [rankOne_twistedE6_zero] at hu
  rw [rankOne_twistedE6_two θ hθ] at hv
  obtain ⟨A, rfl⟩ := hu
  obtain ⟨B, rfl⟩ := hv
  exact (commute_rFixed_slOrbitHom θ hθ rfl (Or.inl ⟨rfl, rfl⟩) (by decide) (by decide)
    (by decide) (by decide) A B).eq

include hθ in
theorem commute_rankOne_twistedE6_zero_three :
    ∀ u ∈ CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 0),
      ∀ v ∈ CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 3), u * v = v * u := by
  intro u hu v hv
  rw [rankOne_twistedE6_zero] at hu
  rw [rankOne_twistedE6_three θ hθ] at hv
  obtain ⟨A, rfl⟩ := hu
  obtain ⟨B, rfl⟩ := hv
  exact (commute_rFixed_slOrbitHom θ hθ rfl (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide)
    (by decide) (by decide) A B).eq

include hθ in
theorem commute_rankOne_twistedE6_one_three :
    ∀ u ∈ CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 1),
      ∀ v ∈ CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 3), u * v = v * u := by
  intro u hu v hv
  rw [rankOne_twistedE6_one] at hu
  rw [rankOne_twistedE6_three θ hθ] at hv
  obtain ⟨A, rfl⟩ := hu
  obtain ⟨B, rfl⟩ := hv
  exact (commute_rFixed_slOrbitHom θ hθ rfl (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide)
    (by decide) (by decide) A B).eq

include hθ in
theorem commute_rankOne_twistedE6 :
    ∀ i j : Fin 4, i.val + 1 < j.val →
      ∀ u ∈ CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup i,
        ∀ v ∈ CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup j, u * v = v * u := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | (exfalso; revert hij; simp; done) | skip
  · exact commute_rankOne_twistedE6_zero_two θ hθ
  · exact commute_rankOne_twistedE6_zero_three θ hθ
  · exact commute_rankOne_twistedE6_one_three θ hθ

variable [Finite k]

theorem linearBlockStandardPair_twistedE6_long :
    ∃ W, LinearBlockStandardPair (fixedField θ) W
      (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 0))
      (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 1)) := by
  obtain ⟨emb, hinj, h0, h1⟩ := exists_levi01 θ
  exact linearBlockStandardPair_of_levi emb hinj (by rw [rankOne_twistedE6_zero, h0])
    (by rw [rankOne_twistedE6_one, h1])

include hθ in
theorem linearBlockStandardPair_twistedE6_short :
    ∃ W, LinearBlockStandardPair k W
      (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 2))
      (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 3)) := by
  obtain ⟨emb, hinj, h0, h1⟩ := exists_levi23 θ hθ
  exact linearBlockStandardPair_of_levi emb hinj (by rw [rankOne_twistedE6_two θ hθ, h0])
    (by rw [rankOne_twistedE6_three θ hθ, h1])

theorem unitaryB2BlockStandardPair_twistedE6 :
    ∃ W, UnitaryB2BlockStandardPair θ hθ W
      (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 1))
      (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup (nf 2)) := by
  obtain ⟨emb, hinj, h0, h1⟩ := exists_levi12 θ hθ
  refine ⟨emb.range, emb, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
    exact bot_le
  · change Function.Injective (emb.comp (ulb θ hθ))
    rw [h0]
    exact rFixed_injective θ _ _
  · change Function.Injective (emb.comp (usb θ hθ))
    rw [h1]
    exact slOrbitHom_injective θ hθ _
  · change (ulb θ hθ).range.map emb = _
    rw [← MonoidHom.range_comp, h0, rankOne_twistedE6_one]
  · change (usb θ hθ).range.map emb = _
    rw [← MonoidHom.range_comp, h1, rankOne_twistedE6_two θ hθ]

end Pairs

end CFSG.ClassicalInvolution.WeakCT

module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSpAut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8RootTorus

public section

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

section SLFour

variable {D : Type} [Group D] {K : Type} [Field K]

theorem center_eq_bot_of_mulEquiv_SL_four (hK : Nat.card K = 2)
    (eD : D ≃* Matrix.SpecialLinearGroup (Fin 4) K) : center D = ⊥ := by
  rw [eq_bot_iff_forall]
  intro z hz
  have hz' : eD z ∈ center (Matrix.SpecialLinearGroup (Fin 4) K) := by
    rw [mem_center_iff]
    intro y
    have h := mem_center_iff.1 hz (eD.symm y)
    have h' := congrArg eD h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz'
  rcases eq_zero_or_eq_one_of_card_two hK r with h0 | h1
  · rw [h0, Fintype.card_fin] at hr
    norm_num at hr
  · have h1' : eD z = 1 := by
      apply Subtype.ext
      rw [← hrz, h1, map_one]
      rfl
    rw [← map_one eD] at h1'
    exact eD.injective h1'

theorem isQuasisimple_of_mulEquiv_SL_four (eD : D ≃* Matrix.SpecialLinearGroup (Fin 4) K) :
    IsQuasisimple D :=
  (LocalAnalysis.ComponentInitial.isQuasisimple_congr eD.symm).1
    (LieType.Universal.SpecialLinear.isQuasisimple 3 K (by norm_num))

theorem card_quotient_center_of_mulEquiv_SL_four (hK : Nat.card K = 2)
    (eD : D ≃* Matrix.SpecialLinearGroup (Fin 4) K) : Nat.card (D ⧸ center D) = 20160 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have h := LinearPilot.lieModel_quotient_center_of_mulEquiv_specialLinear (m := 4) hK' (by norm_num) eD
  rw [LinearPilot.card_of_lieModel_PSL_two h]
  decide

theorem card_of_mulEquiv_SL_four (hK : Nat.card K = 2)
    (eD : D ≃* Matrix.SpecialLinearGroup (Fin 4) K) : Nat.card D = 20160 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)
  rw [card_quotient_center_of_mulEquiv_SL_four hK eD, center_eq_bot_of_mulEquiv_SL_four hK eD,
    Subgroup.card_bot, mul_one] at h
  exact h

end SLFour

section Config

variable {S : Type} [Group S] {σ : MulAut S} {D : Subgroup S}

theorem fixedSubgroup_le_of_not_mem_range
    (hC : ∀ k : S, σ k = k → k ∉ D → ∃ s : S, MulAut.conj s = σ ∧ k * s ∈ D)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) : fixedSubgroup σ ≤ D := by
  intro k hk
  by_contra hkD
  obtain ⟨s, hs, -⟩ := hC k hk hkD
  exact hout ⟨s, hs⟩

theorem mem_or_mul_mem_of_conj (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    (hC : ∀ k : S, σ k = k → k ∉ D → ∃ s : S, MulAut.conj s = σ ∧ k * s ∈ D) {s : S}
    (hs : MulAut.conj s = σ) {k : S} (hk : σ k = k) : k ∈ D ∨ k * s ∈ D := by
  by_cases hkD : k ∈ D
  · exact .inl hkD
  · obtain ⟨s', hs', hks'⟩ := hC k hk hkD
    have h : s' = s := hinj (hs'.trans hs.symm)
    exact .inr (h ▸ hks')

theorem eq_one_of_mem_of_commute (hZ : center D = ⊥) {u : S} (huD : u ∈ D)
    (hu : ∀ x ∈ D, x * u = u * x) : u = 1 := by
  have h : (⟨u, huD⟩ : D) ∈ center D := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hu y y.2)
  rw [hZ, mem_bot] at h
  exact congrArg Subtype.val h

theorem exists_component_of_not_sporadicFixed [Finite S]
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S)) (hσ : orderOf σ = 2)
    {K : Type} [Field K] (hK : Nat.card K = 2) (hfix : ∀ x ∈ D, σ x = x)
    (eD : D ≃* Matrix.SpecialLinearGroup (Fin 4) K)
    (hC : ∀ k : S, σ k = k → k ∉ D → ∃ s : S, MulAut.conj s = σ ∧ k * s ∈ D) :
    ∃ D' : Subgroup (fixedSubgroup σ), IsComponent D' ∧ center D' = ⊥ ∧
      Nat.card (D' ⧸ center D') = 20160 ∧ D'.map (fixedSubgroup σ).subtype = D ∧
      ((σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D') ∨
        FixedCentralizerTwoFree σ D') ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range → D' = ⊤) ∧
      (∀ s : S, MulAut.conj s = σ → D'.index = 2) := by
  have hDF : D ≤ fixedSubgroup σ := fun x hx => hfix x hx
  set D' : Subgroup (fixedSubgroup σ) := D.subgroupOf (fixedSubgroup σ) with hD'def
  have eD' : D' ≃* Matrix.SpecialLinearGroup (Fin 4) K := (subgroupOfEquivOfLe hDF).trans eD
  have hZD : center D = ⊥ := center_eq_bot_of_mulEquiv_SL_four hK eD
  have hmap : D'.map (fixedSubgroup σ).subtype = D := by
    rw [hD'def, subgroupOf_map_subtype, inf_of_le_left hDF]
  have hsD : ∀ s : S, MulAut.conj s = σ → ∀ x ∈ D, x * s = s * x := by
    intro s hs x hx
    have h := hfix x hx
    rw [← hs, MulAut.conj_apply] at h
    calc x * s = (s * x * s⁻¹) * s := by rw [h]
      _ = s * x := by group
  have hsnD : ∀ s : S, MulAut.conj s = σ → s ∉ D := by
    intro s hs hsD'
    have h1 : s = 1 := eq_one_of_mem_of_commute hZD hsD' (hsD s hs)
    rw [← hs, h1, map_one, orderOf_one] at hσ
    norm_num at hσ
  have hindex : ∀ s : S, MulAut.conj s = σ → D'.index = 2 := by
    intro s hs
    have hsF : s ∈ fixedSubgroup σ := by
      show σ s = s
      rw [← hs, MulAut.conj_apply, mul_inv_cancel_right]
    rw [index_eq_two_iff]
    refine ⟨⟨s, hsF⟩, fun b => ?_⟩
    have hb : (b : S) ∈ D ∨ (b : S) * s ∈ D := mem_or_mul_mem_of_conj hinj hC hs b.2
    have hnot : ¬ ((b : S) ∈ D ∧ (b : S) * s ∈ D) := by
      rintro ⟨h1, h2⟩
      apply hsnD s hs
      have : s = (b : S)⁻¹ * ((b : S) * s) := by group
      rw [this]
      exact mul_mem (inv_mem h1) h2
    simp only [hD'def, mem_subgroupOf, Subgroup.coe_mul]
    rcases hb with h | h
    · exact Or.inr ⟨h, fun h' => hnot ⟨h, h'⟩⟩
    · exact Or.inl ⟨h, fun h' => hnot ⟨h', h⟩⟩
  have htop : σ ∉ (MulAut.conj : S →* MulAut S).range → D' = ⊤ := by
    intro hout
    rw [eq_top_iff]
    intro x _
    exact mem_subgroupOf.2 (fixedSubgroup_le_of_not_mem_range hC hout x.2)
  refine ⟨D', ⟨isQuasisimple_of_mulEquiv_SL_four eD', ?_⟩, center_eq_bot_of_mulEquiv_SL_four hK eD',
    ?_, hmap, ?_, htop, hindex⟩
  ·
    by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨s, hs⟩ := hin
      exact (normal_of_index_eq_two (hindex s hs)).isSubnormal
    · rw [htop hin]
      exact IsSubnormal.top
  · rw [card_quotient_center_of_mulEquiv_SL_four hK eD']
  · by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
    ·
      refine .inl ⟨hin, ?_⟩
      obtain ⟨s, hs⟩ := hin
      intro U _ hUC hUF
      rw [hmap] at hUC
      have hs2 : orderOf s = 2 := by
        rw [← orderOf_injective _ hinj s, hs, hσ]
      have hUs : U ≤ zpowers s := by
        intro u hu
        have huC : ∀ x ∈ D, x * u = u * x := fun x hx =>
          mem_centralizer_iff.1 (hUC hu) x hx
        rcases mem_or_mul_mem_of_conj hinj hC hs (hUF hu) with h | h
        · rw [eq_one_of_mem_of_commute hZD h huC]
          exact one_mem _
        · have h1 : u * s = 1 := eq_one_of_mem_of_commute hZD h (fun x hx => by
            calc x * (u * s) = u * (x * s) := by rw [← mul_assoc, huC x hx, mul_assoc]
              _ = u * s * x := by rw [hsD s hs x hx, mul_assoc])
          have : u = s⁻¹ := by
            calc u = u * s * s⁻¹ := by group
              _ = s⁻¹ := by rw [h1, one_mul]
          rw [this]
          exact inv_mem (mem_zpowers s)
      calc Nat.card U ≤ Nat.card (zpowers s) := card_le_of_le hUs
        _ = 2 := by rw [Nat.card_zpowers, hs2]
    ·
      refine .inr ?_
      intro U _ hUC hUF
      rw [hmap] at hUC
      rw [eq_bot_iff]
      intro u hu
      have huD : u ∈ D := fixedSubgroup_le_of_not_mem_range hC hin (hUF hu)
      have huC : ∀ x ∈ D, x * u = u * x := fun x hx =>
        mem_centralizer_iff.1 (hUC hu) x hx
      rw [mem_bot]
      exact eq_one_of_mem_of_commute hZD huD huC

end Config

end CFSG.SeitzReduction.SporadicRefine

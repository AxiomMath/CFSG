module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSLFourExact
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCKind
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem nonempty_equiv_SL_four_of_lieModel {X : Type} [Group X] (h : LieModel X .PSL 4 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := hc
    exact ⟨e.trans (QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 4 K
      (by rw [hcard]; norm_num))⟩
  all_goals exact absurd h0 (by norm_num)

theorem card_fixed_bounds_of_witness {S : Type} [Group S] [Finite S] {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hZ : center D = ⊥) {k : S}
    (hk : σ k = k) (hkD : k ∉ D.map (fixedSubgroup σ).subtype)
    (hks : ∀ s : S, MulAut.conj s = σ → k * s ∉ D.map (fixedSubgroup σ).subtype) :
    (Nat.card (fixedSubgroup σ) ≤ Nat.card D → False) ∧
      (σ ∈ (MulAut.conj : S →* MulAut S).range →
        Nat.card (fixedSubgroup σ) ≤ 2 * Nat.card D → False) := by
  set k' : fixedSubgroup σ := ⟨k, hk⟩ with hk'
  have hk'D : k' ∉ D := fun h => hkD ⟨k', h, rfl⟩
  refine ⟨fun hle => hk'D ?_, ?_⟩
  · rw [Subgroup.eq_top_of_le_card D hle]
    exact Subgroup.mem_top _
  · rintro ⟨s, hs⟩ hle
    have hsF : σ s = s := by
      rw [← hs, MulAut.conj_apply, mul_inv_cancel_right]
    set s' : fixedSubgroup σ := ⟨s, hsF⟩ with hs'
    have hs'D : s' ∉ D := by
      intro hsD
      have hcen : (⟨s', hsD⟩ : D) ∈ center D := by
        rw [mem_center_iff]
        intro y
        apply Subtype.ext
        apply Subtype.ext
        have hy : MulAut.conj s ((y : fixedSubgroup σ) : S) = ((y : fixedSubgroup σ) : S) := by
          rw [hs]
          exact (y : fixedSubgroup σ).property
        rw [MulAut.conj_apply] at hy
        show ((y : fixedSubgroup σ) : S) * s = s * ((y : fixedSubgroup σ) : S)
        calc ((y : fixedSubgroup σ) : S) * s
            = (s * ((y : fixedSubgroup σ) : S) * s⁻¹) * s := by rw [hy]
          _ = s * ((y : fixedSubgroup σ) : S) := by group
      rw [hZ, mem_bot] at hcen
      have h1 : s = 1 := congrArg (fun x : D => ((x : fixedSubgroup σ) : S)) hcen
      rw [← hs, h1, map_one, orderOf_one] at hσ
      norm_num at hσ
    have hidx : D.index = 2 := by
      have hmul := D.card_mul_index
      have hpos : 0 < Nat.card D := Nat.card_pos
      have hle2 : D.index ≤ 2 := by
        by_contra hgt
        push Not at hgt
        have : Nat.card D * 3 ≤ Nat.card D * D.index := Nat.mul_le_mul_left _ hgt
        omega
      have hne1 : D.index ≠ 1 := fun h1 => hs'D (by
        rw [Subgroup.index_eq_one.1 h1]
        exact Subgroup.mem_top _)
      have hne0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have hmem : k' * s' ∈ D := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false hk'D hs'D
    exact hks s hs ⟨k' * s', hmem, rfl⟩

section Main


theorem sporadicFixedLFourTwoInput : LinearPilot.SporadicFixedLFourTwoInput := by
  intro S _ _ hsp τ hτ D hDm
  obtain ⟨eD⟩ := nonempty_equiv_SL_four_of_lieModel hDm
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hZ : center D = ⊥ := center_eq_bot_of_mulEquiv_SL_four hK eD
  have eD' : D.map (fixedSubgroup τ).subtype ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    (D.equivMapOfInjective _ (fixedSubgroup τ).subtype_injective).symm.trans eD
  have hfix : ∀ x ∈ D.map (fixedSubgroup τ).subtype, τ x = x := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨k, hk, hkD, hks⟩ :=
    sporadicFixedSLFourInput S hsp τ hτ (ZMod 2) hK _ hfix ⟨eD'⟩
  exact card_fixed_bounds_of_witness hτ hZ hk hkD hks

end Main

end CFSG.SeitzReduction.SporadicRefine

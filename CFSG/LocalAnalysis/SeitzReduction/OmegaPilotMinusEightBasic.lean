module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEight
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSetup

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Assembly.LowTwoRank (StatedSU StatedScalars)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

section Six

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem nonempty_orthDerived_mulEquiv_statedSU_of_six {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hR : (polarBilin R).Nondegenerate) (hdim : finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = 3 → ∃ u ∈ U, R u ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (2 ^ f) ^ 2 ∧
      Nonempty (orthDerived R ≃* StatedSU 4 (2 ^ f) E) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, hinj, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction R hR hdim hts
  obtain ⟨f₁, h, hK1, hbar⟩ := D.exists_unitaryFieldData
  have hff : f₁ = f := Nat.pow_right_injective (le_refl 2) (hK1.symm.trans hKc)
  subst hff
  obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv h hbar
  have hc : orthDerived R = ρ.range := hcomm
  exact ⟨E, inferInstance, h.finite, h.card_eq_sq,
    ⟨(MulEquiv.subgroupCongr hc).trans ((MonoidHom.ofInjective hinj).symm.trans θ)⟩⟩

theorem lieModel_psu_of_mulEquiv_orthDerived_six {G : Type} [Group G] {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hR : (polarBilin R).Nondegenerate) (hdim : finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = 3 → ∃ u ∈ U, R u ≠ 0)
    (φ : G ≃* orthDerived R) : CFSG.Blueprint.LieModel G .PSU 4 2 f := by
  obtain ⟨E, _, _, hE, ⟨θ⟩⟩ := nonempty_orthDerived_mulEquiv_statedSU_of_six hKc hR hdim hts
  have hZ : center (orthDerived R) = ⊥ := (isQuasisimple_orthDerived_of_six hR hdim hts).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  obtain ⟨-, hZc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := 4) hE
    (by norm_num) hnq
  have hZS : center (StatedSU 4 (2 ^ f) E) = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv θ, hZ, Subgroup.map_bot]
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, LinearPilot.one_le_of_card_eq_two_pow hKc,
    by norm_num, hnq⟩, E, inferInstance, inferInstance, hE,
    ⟨(φ.trans θ).trans (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (hZS.symm.trans hZc)))⟩⟩

end Six

section Perp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [CharP K 2] in
theorem exists_ne_zero_coordinateQuadMinus_three {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ U : Submodule K (Fin (2 * (4 - 1)) → K), finrank K U = 3 →
      ∃ u ∈ U, coordinateQuadMinus (4 - 1) K (by omega) b c u ≠ 0 := by
  obtain ⟨-, hW⟩ := regular_wittIndex_coordinateQuadMinus (K := K) (m := 4 - 1) (by omega) hirr
  intro U hU
  by_contra hcon
  push Not at hcon
  have := hW U hcon
  omega

theorem center_minusPairPerp_of_four_le (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    center (minusPairPerp (K := K) (by omega : 1 ≤ n) b c k) = ⊥ := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · obtain ⟨hR, -⟩ := regular_wittIndex_coordinateQuadMinus (K := K) (m := 4 - 1) (by omega) hirr
    obtain ⟨-, hc⟩ := isQuasisimple_orthDerived_of_six hR (by rw [Module.finrank_fin_fun])
      (exists_ne_zero_coordinateQuadMinus_three hirr)
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv
      (minusPairPerpEquivOfLe le_rfl hirr k).symm, hc, Subgroup.map_bot]
  · exact center_minusPairPerp h5 hirr k

theorem lieModel_minusPairPerp_four {f : ℕ} (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (4 - 1)) :
    CFSG.Blueprint.LieModel (minusPairPerp (K := K) (n := 4) (by omega) b c k) .PSU 4 2 f := by
  obtain ⟨hR, -⟩ := regular_wittIndex_coordinateQuadMinus (K := K) (m := 4 - 1) (by omega) hirr
  exact lieModel_psu_of_mulEquiv_orthDerived_six hK hR (by rw [Module.finrank_fin_fun])
    (exists_ne_zero_coordinateQuadMinus_three hirr) (minusPairPerpEquivOfLe le_rfl hirr k)

theorem isSolvable_outer_minusPairPerp_of_four_le {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    Group.IsSolvable (Outer (minusPairPerp (K := K) (by omega : 1 ≤ n) b c k)) := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · exact UnitaryPilot.isSolvable_outer_of_lieModel (lieModel_minusPairPerp_four hK hirr k)
  · exact isSolvable_outer_of_mulEquiv_minus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hK)
      hK hirr (minusPairPerpProjEquiv h5 hirr k)

end Perp

end CFSG.SeitzReduction.OmegaPilot

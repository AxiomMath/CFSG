module

import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGSmallRep
import CFSG.ClassicalInvolution.SmallOrth.Orth3Small
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLinAlg
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SmallSympDLeK

open Module Subgroup

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [Module.Finite (ZMod 3) W]

theorem card_endUnits_dvd_of_finrank_le_four (hW : finrank (ZMod 3) W ≤ 4) :
    Nat.card (Module.End (ZMod 3) W)ˣ ∣ 24261120 := by
  classical
  let b := Module.finBasis (ZMod 3) W
  let e : (Module.End (ZMod 3) W)ˣ ≃* GL (Fin (finrank (ZMod 3) W)) (ZMod 3) :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp only [ZMod.card]
  generalize finrank (ZMod 3) W = n at hW ⊢
  interval_cases n <;> decide

private theorem prime_eq_five_or_thirteen_of_dvd {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (h : d ∣ 24261120) : d = 5 ∨ d = 13 := by
  rw [show (24261120 : ℕ) = 2 ^ 9 * 3 ^ 6 * 5 * 13 by norm_num] at h
  rcases hd.dvd_mul.mp h with h | h
  · rcases hd.dvd_mul.mp h with h | h
    · rcases hd.dvd_mul.mp h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow h)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow h)
        omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp h)

theorem not_sq_dvd_card_endUnits_of_five_le {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hW : finrank (ZMod 3) W ≤ 4) : ¬ d ^ 2 ∣ Nat.card (Module.End (ZMod 3) W)ˣ := by
  intro h
  have hsq : d ^ 2 ∣ 24261120 := h.trans (card_endUnits_dvd_of_finrank_le_four hW)
  have hdvd : d ∣ 24261120 := (dvd_pow_self d (by norm_num : (2 : ℕ) ≠ 0)).trans hsq
  rcases prime_eq_five_or_thirteen_of_dvd hd hd5 hdvd with rfl | rfl <;> norm_num at hsq

private theorem card_endUnits_dvd_of_finrank_le_three (hW : finrank (ZMod 3) W ≤ 3) :
    Nat.card (Module.End (ZMod 3) W)ˣ ∣ 11232 := by
  rw [Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W).toEquiv]
  exact CFSG.OddStandard.SmallF3.Omega.fg_card_linearEquiv_dvd hW

private theorem card_endUnits_dvd_of_finrank_le_two (hW : finrank (ZMod 3) W ≤ 2) :
    Nat.card (Module.End (ZMod 3) W)ˣ ∣ 48 := by
  rw [Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W).toEquiv]
  exact CFSG.ClassicalGroups.Orthogonal.Small.natCard_linearEquiv_dvd_of_finrank_le_two
    (by simp) hW

theorem eq_bot_of_fiveGroup_of_invariant_subspace
    (hW : finrank (ZMod 3) W ≤ 4) {D : Subgroup (Module.End (ZMod 3) W)ˣ}
    (hD : IsPGroup 5 D) (U : Submodule (ZMod 3) W) (hU0 : U ≠ ⊥) (hUt : U ≠ ⊤)
    (hDU : ∀ g ∈ D, ∀ u ∈ U, (g : Module.End (ZMod 3) W) u ∈ U) : D = ⊥ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite W := Module.finite_of_finite (ZMod 3)
  have : Finite (Module.End (ZMod 3) W)ˣ :=
    Finite.of_injective (fun x : (Module.End (ZMod 3) W)ˣ => (x : W → W))
      (fun x y h => Units.ext (LinearMap.ext (congrFun h)))
  by_contra hD0
  have hdvd : 5 ∣ Nat.card D := hD.card_eq_or_dvd.resolve_left fun h =>
    hD0 (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 5 hdvd
  have hxord : orderOf (x : (Module.End (ZMod 3) W)ˣ) = 5 := (Subgroup.orderOf_coe x).trans hx
  have hdim : finrank (ZMod 3) W = 4 := by
    by_contra h4
    have h3 : finrank (ZMod 3) W ≤ 3 := by omega
    have h5 : 5 ∣ 11232 := (hxord ▸ orderOf_dvd_natCard (x : (Module.End (ZMod 3) W)ˣ)).trans
      (card_endUnits_dvd_of_finrank_le_three h3)
    norm_num at h5
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W
  have hxp : e x ^ 5 = 1 := by
    rw [← map_pow]
    have hx5 : (x : (Module.End (ZMod 3) W)ˣ) ^ 5 = 1 := hxord ▸ pow_orderOf_eq_one _
    rw [hx5, map_one]
  have hx1 : e x ≠ 1 := by
    intro h
    have hx1 : (x : (Module.End (ZMod 3) W)ˣ) = 1 := e.injective (h.trans (map_one e).symm)
    rw [hx1, orderOf_one] at hxord
    norm_num at hxord
  have hcases := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KFAE.submodule_eq_bot_or_top_of_ppd
    Nat.prime_five (e x) hxp hx1
    (by rw [hdim]; norm_num)
    (by intro k hk hk4; rw [hdim] at hk4; interval_cases k <;> norm_num)
    U (fun u hu => hDU x x.2 u hu)
  exact hcases.elim hU0 hUt

theorem eq_bot_of_thirteenGroup_of_invariant_subspace
    (hW : finrank (ZMod 3) W ≤ 3) {D : Subgroup (Module.End (ZMod 3) W)ˣ}
    (hD : IsPGroup 13 D) (U : Submodule (ZMod 3) W) (hU0 : U ≠ ⊥) (hUt : U ≠ ⊤)
    (hDU : ∀ g ∈ D, ∀ u ∈ U, (g : Module.End (ZMod 3) W) u ∈ U) : D = ⊥ := by
  classical
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Finite W := Module.finite_of_finite (ZMod 3)
  have : Finite (Module.End (ZMod 3) W)ˣ :=
    Finite.of_injective (fun x : (Module.End (ZMod 3) W)ˣ => (x : W → W))
      (fun x y h => Units.ext (LinearMap.ext (congrFun h)))
  by_contra hD0
  have hdvd : 13 ∣ Nat.card D := hD.card_eq_or_dvd.resolve_left fun h =>
    hD0 (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 13 hdvd
  have hxord : orderOf (x : (Module.End (ZMod 3) W)ˣ) = 13 := (Subgroup.orderOf_coe x).trans hx
  have hdim : finrank (ZMod 3) W = 3 := by
    by_contra h3
    have h2 : finrank (ZMod 3) W ≤ 2 := by omega
    have h13 : 13 ∣ 48 := (hxord ▸ orderOf_dvd_natCard (x : (Module.End (ZMod 3) W)ˣ)).trans
      (card_endUnits_dvd_of_finrank_le_two h2)
    norm_num at h13
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W
  have hxp : e x ^ 13 = 1 := by
    rw [← map_pow]
    have hx13 : (x : (Module.End (ZMod 3) W)ˣ) ^ 13 = 1 := hxord ▸ pow_orderOf_eq_one _
    rw [hx13, map_one]
  have hx1 : e x ≠ 1 := by
    intro h
    have hx1 : (x : (Module.End (ZMod 3) W)ˣ) = 1 := e.injective (h.trans (map_one e).symm)
    rw [hx1, orderOf_one] at hxord
    norm_num at hxord
  have hcases := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KFAE.submodule_eq_bot_or_top_of_ppd
    (by norm_num : Nat.Prime 13) (e x) hxp hx1
    (by rw [hdim]; norm_num)
    (by intro k hk hk3; rw [hdim] at hk3; interval_cases k <;> norm_num)
    U (fun u hu => hDU x x.2 u hu)
  exact hcases.elim hU0 hUt

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SmallSympDLeK

end

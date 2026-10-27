module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8ZA1
public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPfLift
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

theorem centralizes_of_image {Y Q : Type} [Group Y] [Group Q] (ψ : Y →* Q) {Δ : Set (Subgroup Y)}
    (hconj : ∀ g : Y, ∀ L ∈ Δ, conjSub g L ∈ Δ)
    (hinj : ∀ L ∈ Δ, ∀ M ∈ Δ, L.map ψ = M.map ψ → L = M)
    (hmem : ∀ M ∈ Δ, Set.InjOn ψ (M : Set Y)) {M : Subgroup Y} (hM : M ∈ Δ) {a : Y}
    (hc : ∀ w ∈ M, ψ a * ψ w = ψ w * ψ a) : ∀ w ∈ M, a * w = w * a := by
  have hψc : ∀ w ∈ M, ψ (a * w * a⁻¹) = ψ w := by
    intro w hw
    rw [map_mul, map_mul, map_inv, hc w hw, mul_assoc, mul_inv_cancel, mul_one]
  have himg : (conjSub a M).map ψ = M.map ψ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy := mem_conjSub_iff.mp hy
      refine ⟨a⁻¹ * y * a, hy, ?_⟩
      have := hψc (a⁻¹ * y * a) hy
      rw [show a * (a⁻¹ * y * a) * a⁻¹ = y by group] at this
      exact this.symm
    · rintro ⟨w, hw, rfl⟩
      refine ⟨a * w * a⁻¹, mem_conjSub_iff.mpr ?_, hψc w hw⟩
      simpa [mul_assoc] using hw
  have heq : conjSub a M = M := hinj _ (hconj a M hM) M hM himg
  intro w hw
  have h1 : a * w * a⁻¹ ∈ M := by
    rw [← heq]
    exact conj_mem_conjSub hw
  have h2 : a * w * a⁻¹ = w := hmem M hM h1 hw (hψc w hw)
  calc a * w = (a * w * a⁻¹) * a := by group
    _ = w * a := by rw [h2]

theorem exists_const_four_set {m : ℕ} (hm : 6 ≤ m) (v : Fin m → ZMod 2) (hv : ∑ i, v i = 0) :
    ∃ γ : Finset (Fin m), γ.card = 4 ∧ ∃ c : ZMod 2, ∀ i ∈ γ, v i = c := by
  classical
  set S1 : Finset (Fin m) := Finset.univ.filter (fun i => v i = 1) with hS1
  set S0 : Finset (Fin m) := Finset.univ.filter (fun i => v i = 0) with hS0
  have hcard : S1.card + S0.card = m := by
    have : S1.card + S0.card = (S1 ∪ S0).card := by
      rw [Finset.card_union_of_disjoint]
      rw [Finset.disjoint_left]
      intro i h1 h0
      simp only [hS1, hS0, Finset.mem_filter] at h1 h0
      rw [h1.2] at h0
      exact absurd h0.2 (by decide)
    rw [this]
    have hu : S1 ∪ S0 = Finset.univ := by
      ext i
      simp only [hS1, hS0, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      have : ∀ x : ZMod 2, x = 1 ∨ x = 0 := by decide
      exact this (v i)
    rw [hu, Finset.card_univ, Fintype.card_fin]
  have heven : Even S1.card := by
    have h1 : ∑ i, v i = (S1.card : ZMod 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => v i = 1)]
      have e1 : ∑ i ∈ Finset.univ.filter (fun i => v i = 1), v i = (S1.card : ZMod 2) := by
        rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const]
        simp [hS1]
      have e2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ v i = 1), v i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have := (Finset.mem_filter.mp hi).2
        have h' : ∀ x : ZMod 2, ¬ x = 1 → x = 0 := by decide
        exact h' _ this
      rw [e1, e2, add_zero]
    rw [hv] at h1
    exact (ZMod.natCast_eq_zero_iff_even).mp h1.symm
  by_cases h4 : 4 ≤ S1.card
  · obtain ⟨γ, hγ, hc⟩ := Finset.exists_subset_card_eq h4
    exact ⟨γ, hc, 1, fun i hi => (Finset.mem_filter.mp (hγ hi)).2⟩
  by_cases h0 : 4 ≤ S0.card
  · obtain ⟨γ, hγ, hc⟩ := Finset.exists_subset_card_eq h0
    exact ⟨γ, hc, 0, fun i hi => (Finset.mem_filter.mp (hγ hi)).2⟩
  exfalso
  obtain ⟨k, hk⟩ := heven
  omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

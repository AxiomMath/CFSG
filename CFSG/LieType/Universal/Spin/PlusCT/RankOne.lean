module

public import CFSG.LieType.Universal.Spin.PlusCT.Basic

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
open CFSG.LieType.Universal.Spin.PlusCT

namespace PlusCT

section SL2

variable {K : Type*} [Field K]

theorem exists_eq_diagSL2_mul_upperSL2_or (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    (∃ (τ : Kˣ) (b : K), M = diagSL2 τ * upperSL2 b) ∨
      ∃ (a : K) (τ : Kˣ) (d : K), M = upperSL2 a * weylSL2 1 * diagSL2 τ * upperSL2 d := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact M.2
  by_cases hc : M 1 0 = 0
  · left
    have ha : M 0 0 ≠ 0 := by
      intro ha
      rw [ha, hc] at hdet
      simp at hdet
    have hd : M 1 1 = (M 0 0)⁻¹ := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact eq_inv_of_mul_eq_one_right hdet
    refine ⟨Units.mk0 (M 0 0) ha, M 0 1 / M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    field_simp
  · right
    refine ⟨M 0 0 / M 1 0, Units.mk0 (-M 1 0) (neg_ne_zero.mpr hc), M 1 1 / M 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · field_simp
    · field_simp
      linear_combination -hdet
    · field_simp

end SL2

section Frame

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : HypFrame Q n)

theorem eq_zero_of_conj_longRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) {c d : K}
    (h : F.longRoot hij s t (.ofAdd c) * F.longRoot hij.symm (!t) (!s) (.ofAdd 1) *
        (F.longRoot hij s t (.ofAdd c))⁻¹ = F.longRoot hij.symm (!t) (!s) (.ofAdd d)) :
    c = 0 := by
  rw [← map_inv, ← ofAdd_neg] at h
  have hneg : ∀ e : K, spinAction Q (F.longRoot hij.symm (!t) (!s) (.ofAdd e)) (F.vec i s) =
      F.vec i s + e • F.vec j (!t) := fun e => by
    have := F.spinAction_longRoot_vec_not_right hij.symm (!t) (!s) e
    rwa [Bool.not_not] at this
  have h1 := congrArg (fun g => spinAction Q g (F.vec i s)) h
  simp only [map_mul, LinearEquiv.mul_apply, F.spinAction_longRoot_vec_left, hneg, map_add,
    map_smul, F.spinAction_longRoot_vec_not_right] at h1
  have h2 := congrArg (fun v => polar Q v (F.vec i (!s))) h1
  simp only [polar_add_left, polar_smul_left, F.polar_vec_not, F.polar_vec_of_ne hij.symm,
    smul_eq_mul, mul_one, mul_zero, add_zero] at h2
  linear_combination h2

end Frame

end PlusCT

variable {n : ℕ} {K : Type} [Field K]

private theorem rankOne_bruhat_aux (hn : 3 ≤ n) (k : Fin n) (g : spinGroup (quadPlus n K))
    (hg : g ∈ rankOne (plusRootGroup n K hn) k) :
    (∃ h ∈ (torusD K hn k).range, ∃ u ∈ plusRootGroup n K hn (Pi.single k 1), g = h * u) ∨
      ∃ u ∈ plusRootGroup n K hn (Pi.single k 1), ∃ h ∈ (torusD K hn k).range,
        ∃ v ∈ plusRootGroup n K hn (Pi.single k 1), g = u * weylD K hn k * h * v := by
  rw [rankOne_plusRootGroup] at hg
  obtain ⟨M, rfl⟩ := hg
  have hU : ∀ c : K, rankOneD K hn k (upperSL2 c) ∈ plusRootGroup n K hn (Pi.single k 1) :=
    fun c => by
      rw [plusRootGroup_single, rankOneD_upperSL2]
      exact ⟨_, rfl⟩
  rcases exists_eq_diagSL2_mul_upperSL2_or M with ⟨τ, b, rfl⟩ | ⟨a, τ, d, rfl⟩
  · exact Or.inl ⟨_, ⟨τ, rfl⟩, _, hU b, map_mul _ _ _⟩
  · refine Or.inr ⟨_, hU a, _, ⟨τ, rfl⟩, _, hU d, ?_⟩
    rw [map_mul, map_mul, map_mul, weylD_eq_rankOneD, torusD_apply]

theorem plusDatum_rankOne_bruhat (hn : 3 ≤ n) :
    ∀ i, ∀ g ∈ rankOne (plusDatum n K hn).rootGroup i,
      (∃ h ∈ (torusD K hn i).range, ∃ u ∈ (plusDatum n K hn).rootGroup (Pi.single i 1),
          g = h * u) ∨
        ∃ u ∈ (plusDatum n K hn).rootGroup (Pi.single i 1), ∃ h ∈ (torusD K hn i).range,
          ∃ v ∈ (plusDatum n K hn).rootGroup (Pi.single i 1), g = u * weylD K hn i * h * v :=
  fun k g hg => rankOne_bruhat_aux hn k g hg

private theorem eq_one_of_mem_normalizer_aux (hn : 3 ≤ n) (k : Fin n)
    (u : spinGroup (quadPlus n K)) (hu : u ∈ plusRootGroup n K hn (Pi.single k 1))
    (hN : u ∈ Subgroup.normalizer
      (plusRootGroup n K hn (-Pi.single k 1) : Set (spinGroup (quadPlus n K)))) :
    u = 1 := by
  rw [plusRootGroup_single] at hu
  rw [plusRootGroup_neg_single] at hN
  obtain ⟨c, rfl⟩ := hu
  obtain ⟨d, hd⟩ := (Subgroup.mem_normalizer_iff.mp hN (negRootD K hn k (.ofAdd 1))).mp ⟨_, rfl⟩
  have h0 : Multiplicative.toAdd c = 0 :=
    eq_zero_of_conj_longRoot (plusFrame n K hn) (rootIdxD_ne n (by omega) k) true (rootSignD n k)
      (d := Multiplicative.toAdd d) hd.symm
  rw [← ofAdd_toAdd c, h0, ofAdd_zero, map_one]

theorem plusDatum_eq_one_of_mem_normalizer (hn : 3 ≤ n) :
    ∀ i, ∀ u ∈ (plusDatum n K hn).rootGroup (Pi.single i 1),
      u ∈ Subgroup.normalizer
          ((plusDatum n K hn).rootGroup (-Pi.single i 1) : Set (spinGroup (quadPlus n K))) →
        u = 1 :=
  fun k u hu hN => eq_one_of_mem_normalizer_aux hn k u hu hN

theorem plusDatum_torus_commute (hn : 3 ≤ n) :
    ∀ i j : Fin (plusDatum n K hn).rank, ∀ h ∈ (torusD K hn i).range,
      ∀ h' ∈ (torusD K hn j).range, Commute h h' := by
  rintro i j _ ⟨τ, rfl⟩ _ ⟨σ, rfl⟩
  exact commute_torusD K hn i j τ σ

end CFSG.LieType.Universal.Spin

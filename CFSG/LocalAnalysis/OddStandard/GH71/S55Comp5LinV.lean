module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3LAlg

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {K : Type} [Field K] {n : ℕ}

namespace C5

theorem conj_mem_elat {W : Submodule K (Fin n → K)} {g h : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ stabilizer W) (hh : h ∈ StepH3L.elat W) : g * h * g⁻¹ ∈ StepH3L.elat W := by
  have hmem : ∀ x ∈ stabilizer W, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    intro x hx w hw
    rw [mem_stabilizer] at hx
    rw [← hx]
    exact ⟨w, hw, rfl⟩
  have key := StepH3L.slConjugation_mem_elat (A := SpecialLinearGroup.toGL g)
    (hmem g hg) (by
      intro w hw
      rw [← map_inv]
      exact hmem _ (inv_mem hg) w hw) hh
  have e : CatalogueBHigherLinearAction.slConjugation n K (SpecialLinearGroup.toGL g) h =
      g * h * g⁻¹ := by
    apply SpecialLinearGroup.toGL_injective
    rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]
  rwa [e] at key

end C5

open C5

theorem projStabilizer_le_normalizer [Finite K] (W : Submodule K (Fin n → K)) :
    projStabilizer W ≤
      normalizer (((StepH3L.elat W).map (proj n K) : Subgroup (projectiveSL n K)) :
        Set (projectiveSL n K)) := by
  have : Fintype K := Fintype.ofFinite K
  rintro _ ⟨g, hg, rfl⟩
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨h, hh, rfl⟩
  exact ⟨g * h * g⁻¹, conj_mem_elat hg hh, by simp only [map_mul, map_inv]⟩

theorem not_rFree_of_not_dvd_index [Finite K] {r p : ℕ} [Fact p.Prime] [CharP K r]
    {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hp : ¬ p ∣ (projStabilizer W).index) {y : projectiveSL n K} (hy : orderOf y = p) :
    ¬ RFree r y := by
  have : Fintype K := Fintype.ofFinite K
  exact not_rFree_of_le_normalizer ((StepH3L.isPGroup_elat W).map _)
    (StepH3L.map_elat_ne_bot hW0 hWt) (projStabilizer_le_normalizer W) hp hy

theorem flagSpace_ne_bot {k : ℕ} (hk0 : 0 < k) (hkn : k ≤ n) : flagSpace n K k ≠ ⊥ := by
  intro h
  have := finrank_flagSpace (K := K) hkn
  rw [h, finrank_bot] at this
  omega

theorem flagSpace_ne_top {k : ℕ} (hkn : k < n) : flagSpace n K k ≠ ⊤ := by
  intro h
  have := finrank_flagSpace (K := K) hkn.le
  rw [h, finrank_top, Module.finrank_fin_fun] at this
  omega

theorem index_eq_of_gauss [Finite K] {k : ℕ} (hkn : k ≤ n) {N : ℕ}
    (hN : gaussianCoeff n k (Nat.card K) = N) : (projStabilizer (flagSpace n K k)).index = N := by
  have h := (subspace_index (n := n) (K := K) hkn).2 _ (finrank_flagSpace hkn)
  rw [hN] at h
  exact_mod_cast h

theorem index_three_one [Finite K] :
    (projStabilizer (flagSpace 3 K 1)).index = Nat.card K ^ 2 + Nat.card K + 1 := by
  refine index_eq_of_gauss (by norm_num) ?_
  have hq : (1 : ℚ) < Nat.card K := by exact_mod_cast Finite.one_lt_card
  rw [gaussianCoeff, Finset.prod_range_one, div_eq_iff (by norm_num; linarith)]
  push_cast
  ring

theorem index_four_one [Finite K] :
    (projStabilizer (flagSpace 4 K 1)).index = (Nat.card K + 1) * (Nat.card K ^ 2 + 1) := by
  refine index_eq_of_gauss (by norm_num) ?_
  have hq : (1 : ℚ) < Nat.card K := by exact_mod_cast Finite.one_lt_card
  rw [gaussianCoeff, Finset.prod_range_one, div_eq_iff (by norm_num; linarith)]
  push_cast
  ring

theorem index_four_two [Finite K] :
    (projStabilizer (flagSpace 4 K 2)).index =
      (Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 + Nat.card K + 1) := by
  refine index_eq_of_gauss (by norm_num) ?_
  have hq : (1 : ℚ) < Nat.card K := by exact_mod_cast Finite.one_lt_card
  have h1 : (Nat.card K : ℚ) - 1 ≠ 0 := by linarith
  have h2 : (Nat.card K : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [gaussianCoeff, Finset.prod_range_succ, Finset.prod_range_one]
  norm_num
  field_simp
  ring

end CFSG.OddStandard.GH71.S55

module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

theorem SpPoint.line_ne_bot (L : SpPoint r K) : L.line ≠ ⊥ := fun h => by
  have := L.finrank_line
  rw [h, finrank_bot] at this
  exact zero_ne_one this

theorem index_projStabilizer_eq_isoGaussian [Finite K] {q : ℕ} (hq : Nat.card K = q)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hW : IsTotallyIsotropic (pairedSympForm K r) W) :
    ((projStabilizer r K W).index : ℚ) = isoGaussian r (finrank K W) q :=
  (isotropic_subspace_index hq (finrank_le_of_isTotallyIsotropic
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
    finrank_standard hW)).2.1 W hW rfl

theorem mem_spExtremalParabolics_iff [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 3 ≤ r) {M : Subgroup (StatedProj (StatedSp r K))} :
    M ∈ spExtremalParabolics r K p ↔ ∃ L : SpPoint r K, M = projStabilizer r K L.line := by
  classical
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨hM, -, -⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ r)
  have hMeq := Set.ext_iff.mp hM
  have hLM : ∀ L : SpPoint r K, projStabilizer r K L.line ∈ spMaximalParabolics r K p :=
    fun L => (hMeq _).mpr ⟨L.line, L.line_ne_bot, isTotallyIsotropic_line L, rfl⟩
  have hidx : ∀ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ →
      IsTotallyIsotropic (pairedSympForm K r) W → finrank K W ≠ 1 →
      isoGaussian r 1 (Nat.card K) < ((projStabilizer r K W).index : ℚ) := by
    intro W h0 hW hW1
    have hk := finrank_le_of_isTotallyIsotropic SymplecticFlag.pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate finrank_standard hW
    have hk1 : 1 ≤ finrank K W := Nat.one_le_iff_ne_zero.mpr fun h => h0 (finrank_eq_zero.mp h)
    rw [index_projStabilizer_eq_isoGaussian rfl hW]
    exact isotropic_gaussian_minimum hq2 hr (by omega) hk
  have hle : ∀ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ →
      IsTotallyIsotropic (pairedSympForm K r) W →
      isoGaussian r 1 (Nat.card K) ≤ ((projStabilizer r K W).index : ℚ) := by
    intro W h0 hW
    by_cases hW1 : finrank K W = 1
    · rw [index_projStabilizer_eq_isoGaussian rfl hW, hW1]
    · exact (hidx W h0 hW hW1).le
  have hpt : ∀ L : SpPoint r K,
      ((projStabilizer r K L.line).index : ℚ) = isoGaussian r 1 (Nat.card K) := fun L => by
    rw [index_projStabilizer_eq_isoGaussian rfl (isTotallyIsotropic_line L), L.finrank_line]
  constructor
  · rintro ⟨hMM, hmin⟩
    obtain ⟨W, h0, hW, rfl⟩ := (hMeq _).mp hMM
    by_cases hW1 : finrank K W = 1
    · exact ⟨⟨W, hW1⟩, rfl⟩
    · exfalso
      set L₀ : SpPoint r K := SpPoint.ofVec _ (single_ne_zero (K := K) (Sum.inl ⟨0, by omega⟩))
      have h1 : ((projStabilizer r K W).index : ℚ) ≤ (projStabilizer r K L₀.line).index := by
        exact_mod_cast hmin _ (hLM L₀)
      have h2 := hidx W h0 hW hW1
      rw [hpt L₀] at h1
      linarith
  · rintro ⟨L, rfl⟩
    refine ⟨hLM L, fun M' hM' => ?_⟩
    obtain ⟨W, h0, hW, rfl⟩ := (hMeq _).mp hM'
    have h1 := hle W h0 hW
    rw [← hpt L] at h1
    exact_mod_cast h1

theorem intrinsic_points [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] {q : ℕ}
    (hq : Nat.card K = q) (hr : 3 ≤ r) :
    spExtremalParabolics r K p = Set.range (fun L : SpPoint r K => projStabilizer r K L.line) ∧
    (∀ M ∈ spExtremalParabolics r K p,
      (M.index : ℚ) = ((q : ℚ) ^ (2 * r) - 1) / ((q : ℚ) - 1)) ∧
    Set.BijOn (fun L : SpPoint r K => projStabilizer r K L.line) Set.univ
      (spExtremalParabolics r K p) ∧
    ∀ α : MulAut (StatedProj (StatedSp r K)),
      (fun M => M.map (α : StatedProj (StatedSp r K) →* StatedProj (StatedSp r K))) ''
        spExtremalParabolics r K p = spExtremalParabolics r K p := by
  classical
  have hmem := fun M => mem_spExtremalParabolics_iff (K := K) (M := M) p hr
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ r)
  refine ⟨Set.ext fun M => (hmem M).trans ?_, fun M hM => ?_, ⟨fun L _ => (hmem _).mpr ⟨L, rfl⟩,
    fun L _ L' _ h => SpPoint.ext (hinj _ _ L.line_ne_bot (isTotallyIsotropic_line L)
      L'.line_ne_bot (isTotallyIsotropic_line L') h), fun M hM => ?_⟩, fun α => ?_⟩
  · exact exists_congr fun L => eq_comm
  · obtain ⟨L, rfl⟩ := (hmem M).mp hM
    rw [index_projStabilizer_eq_isoGaussian hq (isTotallyIsotropic_line L), L.finrank_line,
      isoGaussian_one]
  · obtain ⟨L, rfl⟩ := (hmem M).mp hM
    exact ⟨L, Set.mem_univ _, rfl⟩
  · refine Set.Subset.antisymm ?_ fun M hM => ⟨M.map (α.symm : StatedProj (StatedSp r K) →*
      StatedProj (StatedSp r K)), LinearFlag.map_mem_extremalParabolics α.symm hM, ?_⟩
    · rintro _ ⟨M, hM, rfl⟩
      exact LinearFlag.map_mem_extremalParabolics α hM
    · exact (MulEquiv.mapSubgroup α).apply_symm_apply M

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

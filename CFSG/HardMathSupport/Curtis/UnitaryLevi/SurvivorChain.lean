module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainFaithful
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.TailTrivialThree

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module CFSG.LocalAnalysis.ComponentInitial

section Filtration

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

theorem chainFil_trivial_of_pieces {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} {W : ℕ → Submodule K V}
    (hW0 : W 0 = ⊥) (hs : 1 ≤ s) (g : LinearMap.GeneralLinearGroup K V)
    (hiso : ∀ v w, B ((g : Module.End K V) v) ((g : Module.End K V) w) = B v w)
    (hinv : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j,
      ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ W j)
    (hP : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (g : Module.End K V) v - v ∈ W (j - 1))
    (hM : ∀ v, (∀ w ∈ W s, B w v = 0) → (g : Module.End K V) v - v ∈ W s) :
    ∀ i, ∀ v ∈ chainFil B s W (i + 1),
      (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1) v ∈ chainFil B s W i := by
  have hdual : ∀ a, a < s → ∀ v, (∀ w ∈ W a, B w v = 0) →
      ∀ w ∈ W (a + 1), B w ((g : Module.End K V) v - v) = 0 := by
    intro a has v hv w hw
    have h1 : ((g : Module.End K V) w - w) ∈ W a := by
      have := hP (a + 1) (by omega) (by omega) w hw
      simpa using this
    have h2 : ∀ u ∈ W a, B u ((g : Module.End K V) v) = 0 := by
      intro u hu
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [hW0, Submodule.mem_bot] at hu
        simp [hu]
      · have := hiso (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) u) v
        have e : (g : Module.End K V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) :
            Module.End K V) u) = u := by
          rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
          rfl
        rw [e] at this
        rw [this]
        exact hv _ (hinv a ha (by omega) u hu)
    have h3 := hiso w v
    rw [map_sub, ← h3]
    have e : B w ((g : Module.End K V) v) - B ((g : Module.End K V) w) ((g : Module.End K V) v) =
        - B ((g : Module.End K V) w - w) ((g : Module.End K V) v) := by
      rw [map_sub, LinearMap.sub_apply]
      ring
    rw [e, h2 _ h1, neg_zero]
  intro i v hv
  have hgm : ((g : Module.End K V) - 1) v = (g : Module.End K V) v - v := by simp
  rw [hgm]
  by_cases hi0 : i = 0
  · subst hi0
    rw [chainFil_zero]
    rw [chainFil_of_le (by omega) hs] at hv
    simpa [hW0] using hP 1 le_rfl hs v hv
  · by_cases hi1 : i < s
    · rw [chainFil_of_le (by omega) (by omega)] at hv
      rw [chainFil_of_le (by omega) (by omega)]
      simpa using hP (i + 1) (by omega) (by omega) v hv
    · by_cases his : i = s
      · subst his
        rw [chainFil_of_le (by omega) le_rfl]
        rw [chainFil_of_dual (by omega) (by omega)] at hv
        have : 2 * i + 1 - (i + 1) = i := by omega
        rw [this, Submodule.mem_orthogonalBilin] at hv
        exact hM v fun w hw => hv w hw
      · have hi2 : s < i := by omega
        by_cases hi3 : i < 2 * s
        · rw [chainFil_of_dual hi2 (by omega)]
          rw [chainFil_of_dual (by omega) (by omega)] at hv
          have e1 : 2 * s + 1 - (i + 1) = 2 * s - i := by omega
          have e2 : 2 * s + 1 - i = (2 * s - i) + 1 := by omega
          rw [e1, Submodule.mem_orthogonalBilin] at hv
          rw [e2, Submodule.mem_orthogonalBilin]
          intro w hw
          exact hdual (2 * s - i) (by omega) v (fun w' hw' => hv w' hw') w hw
        · by_cases hi4 : i = 2 * s
          · subst hi4
            rw [chainFil_of_dual (by omega) le_rfl]
            have e2 : 2 * s + 1 - 2 * s = 0 + 1 := by omega
            rw [e2, Submodule.mem_orthogonalBilin]
            intro w hw
            exact hdual 0 (by omega) v (fun w' hw' => by
              rw [hW0, Submodule.mem_bot] at hw'; simp [hw']) w hw
          · rw [chainFil_of_gt (by omega)]
            trivial

theorem exists_pow_two_pow_eq_one_of_trivial_on_pieces [CharP K 2] {B : V →ₛₗ[σ] V →ₗ[K] K}
    {s : ℕ} {W : ℕ → Submodule K V} (hW0 : W 0 = ⊥) (hs : 1 ≤ s)
    (g : LinearMap.GeneralLinearGroup K V)
    (hiso : ∀ v w, B ((g : Module.End K V) v) ((g : Module.End K V) w) = B v w)
    (hinv : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j,
      ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ W j)
    (hP : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (g : Module.End K V) v - v ∈ W (j - 1))
    (hM : ∀ v, (∀ w ∈ W s, B w v = 0) → (g : Module.End K V) v - v ∈ W s) :
    ∃ k, g ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * s + 1 ≤ 2 ^ k := ⟨2 * s + 1, (Nat.lt_two_pow_self).le⟩
  refine ⟨k, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact pow_two_pow_eq_one_of_trivial_graded (g : Module.End K V) (chainFil B s W)
    (chainFil_zero B s W) (chainFil_trivial_of_pieces hW0 hs g hiso hinv hP hM)
    (N := 2 * s + 1) (chainFil_of_gt (by omega)) hk

end Filtration

section Perfect

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_pow_two_pow_eq_one_of_lines (h : UnitaryFieldData 2 1 K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBs : B.SeparatingLeft) {s : ℕ} (hs : 1 ≤ s)
    {W : ℕ → Submodule K V} (hW0 : W 0 = ⊥)
    (hWiso : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, ∀ w ∈ W j, B v w = 0)
    (Δ : Subgroup (LinearMap.GeneralLinearGroup K V)) (hperf : ⁅Δ, Δ⁆ = Δ)
    (hΔiso : ∀ d ∈ Δ, ∀ v w, B ((d : Module.End K V) v) ((d : Module.End K V) w) = B v w)
    (hΔst : ∀ d ∈ Δ, ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (d : Module.End K V) v ∈ W j)
    (hline : ∀ j, 1 ≤ j → j ≤ s → finrank K (PieceQ (W (j - 1)) (W j)) = 1)
    (htail : finrank K (PieceQ (W s) ((W s).orthogonalBilin B)) ≤ 3) :
    ∀ d ∈ Δ, ∃ k, d ^ 2 ^ k = 1 := by
  have := h.charP
  have hW : ∀ d ∈ Δ, ∀ a, a ≤ s → ∀ v ∈ W a, (d : Module.End K V) v ∈ W a := by
    intro d hd a ha v hv
    rcases Nat.eq_zero_or_pos a with rfl | h0
    · rw [hW0, Submodule.mem_bot] at hv ⊢
      simp [hv]
    · exact hΔst d hd a h0 ha v hv
  intro d hd
  refine exists_pow_two_pow_eq_one_of_trivial_on_pieces hW0 hs d (hΔiso d hd)
    (fun j hj1 hjs v hv => hΔst d⁻¹ (Δ.inv_mem hd) j hj1 hjs v hv) ?_ ?_
  · intro j hj1 hjs v hv
    exact perfect_trivial_on_line_piece (hline j hj1 hjs) Δ hperf
      (fun d hd => hW d hd (j - 1) (by omega)) (fun d hd => hW d hd j hjs) d hd v hv
  · intro v hv
    exact isometry_perfect_trivial_on_tail' h hB hBs (hWiso s hs le_rfl) htail Δ
      (fun d hd => ⟨hΔiso d hd, hW d hd s le_rfl⟩) hperf d hd v
      (Submodule.mem_orthogonalBilin.mpr hv)

theorem exists_mem_not_mem_of_finrank_pieceQ_pos {F F' : Submodule K V}
    (h : 0 < finrank K (PieceQ F F')) : ∃ v ∈ F', v ∉ F := by
  by_contra hcon
  push Not at hcon
  have : Subsingleton (PieceQ F F') := by
    refine ⟨fun p q => ?_⟩
    induction p using Submodule.Quotient.induction_on with
    | H x =>
      induction q using Submodule.Quotient.induction_on with
      | H y =>
        rw [Submodule.Quotient.eq]
        simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_sub]
        exact F.sub_mem (hcon _ x.2) (hcon _ y.2)
  have := Module.finrank_zero_of_subsingleton (R := K) (M := PieceQ F F')
  omega

theorem scalar_cube_eq_one_of_trivial_piece {F F' : Submodule K V} {g : Module.End K V}
    (hF : ∀ v ∈ F, g v ∈ F) (htriv : ∀ v ∈ F', g v - v ∈ F) {c : K}
    (hc : ∀ v, g (g (g v)) = c • v) {v : V} (hv : v ∈ F') (hvF : v ∉ F) : c = 1 := by
  have h1 : g v - v ∈ F := htriv v hv
  have h2 : g (g v) - v ∈ F := by
    have : g (g v) - v = g (g v - v) + (g v - v) := by rw [map_sub]; abel
    rw [this]
    exact F.add_mem (hF _ h1) h1
  have h3 : g (g (g v)) - v ∈ F := by
    have : g (g (g v)) - v = g (g (g v) - v) + (g v - v) := by
      rw [map_sub]; abel
    rw [this]
    exact F.add_mem (hF _ h2) h1
  by_contra hne
  have h4 : (c - 1) • v ∈ F := by
    rw [sub_smul, one_smul, ← hc]
    exact h3
  exact hvF ((F.smul_mem_iff (sub_ne_zero.mpr hne)).mp h4)

end Perfect

end CFSG.HardMathSupport.Curtis.UnitaryLevi

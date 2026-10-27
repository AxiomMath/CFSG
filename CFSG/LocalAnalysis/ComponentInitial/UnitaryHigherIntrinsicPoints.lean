module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

variable (h : UnitaryFieldData p f K)

theorem map_mem_maxParabolics (α : hypPSU h r ε ≃* hypPSU h r ε)
    {M : Subgroup (hypPSU h r ε)} (hM : M ∈ maxParabolics h r ε) :
    M.map (α : hypPSU h r ε →* hypPSU h r ε) ∈ maxParabolics h r ε := by
  obtain ⟨hM, hmax⟩ := hM
  refine ⟨LinearFlag.map_mem_maximalParabolics α hM, fun M' hM' => ?_⟩
  have h1 := hmax _ (LinearFlag.map_mem_maximalParabolics α.symm hM')
  rw [Subgroup.index_map_equiv] at h1 ⊢
  exact h1

theorem map_mem_intrinsicParabolics (α : hypPSU h r ε ≃* hypPSU h r ε)
    {M : Subgroup (hypPSU h r ε)} (hM : M ∈ intrinsicParabolics h r ε) :
    M.map (α : hypPSU h r ε →* hypPSU h r ε) ∈ intrinsicParabolics h r ε := by
  by_cases hn : 2 * r + ε = 4
  · rw [intrinsicParabolics_of_eq_four hn] at hM ⊢
    exact map_mem_maxParabolics h α hM
  · rw [intrinsicParabolics_of_ne_four hn] at hM ⊢
    exact LinearFlag.map_mem_extremalParabolics α hM

theorem ne_bot_and_isotropic_of_mem_hypIsotropicLines {L : Submodule K (HypIndex r ε → K)}
    (hL : L ∈ hypIsotropicLines h r ε) :
    L ≠ ⊥ ∧ ∀ x ∈ L, ∀ y ∈ L, hypForm h r ε x y = 0 := by
  refine ⟨fun h0 => ?_, isTotIso_of_mem_isoLines (B := hypForm h r ε) hL⟩
  have h1 := hL.1
  rw [h0, finrank_bot] at h1
  exact zero_ne_one h1

theorem index_projIsoStabilizer_eq {W : Submodule K (HypIndex r ε → K)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) :
    ((projIsoStabilizer h r ε W).index : ℚ) =
      isoIndexCount (p ^ f) (2 * r + ε) (Module.finrank K W) := by
  obtain ⟨h1, h2, -⟩ := isotropic_stabilizer_index h W hW
  rw [h1, h2]

theorem intrinsicParabolics_eq (hr : 1 ≤ r) (hε : ε ≤ 1) :
    intrinsicParabolics h r ε = Set.range fun L : hypIsotropicLines h r ε =>
      projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K)) := by
  obtain ⟨hmax, -, -⟩ := unitary_maximal_parabolics h hr hε
  have hq : 2 ≤ p ^ f :=
    h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  obtain ⟨-, hcmp5, hcmp4, hcmp23⟩ := isotropic_index_comparison (n := 2 * r + ε) hq
  have hdimr : ∀ {W : Submodule K (HypIndex r ε → K)}, W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) →
      1 ≤ Module.finrank K W ∧ Module.finrank K W ≤ (2 * r + ε) / 2 := fun hW0 hW => by
    obtain ⟨h1, h2, -⟩ := exists_smul_hypFlag_eq h hε hW0 hW
    exact ⟨h1, by omega⟩
  have hF1 : hypFlag h r ε 1 ∈ hypIsotropicLines h r ε := by
    rw [hypFlag_eq_posFlag h hε (by omega)]
    refine ⟨finrank_posFlag hr, fun a ha => posFlag_isotropic h hr a ha a ha⟩
  have hF1' := ne_bot_and_isotropic_of_mem_hypIsotropicLines h hF1
  have hF1dim : Module.finrank K (hypFlag h r ε 1) = 1 := hF1.1
  have hmemM : ∀ {W : Submodule K (HypIndex r ε → K)}, W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) →
      projIsoStabilizer h r ε W ∈ maximalParabolics h r ε := fun hW0 hW => by
    rw [hmax]
    exact ⟨_, ⟨hW0, hW⟩, rfl⟩
  have hline : ∀ {W : Submodule K (HypIndex r ε → K)},
      (∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) → Module.finrank K W = 1 →
      W ∈ hypIsotropicLines h r ε := fun hW hd => ⟨hd, fun a ha => hW a ha a ha⟩
  ext M
  constructor
  · intro hM
    have hM𝓜 : M ∈ maximalParabolics h r ε := by
      by_cases hn : 2 * r + ε = 4
      · rw [intrinsicParabolics_of_eq_four hn] at hM
        exact hM.1
      · rw [intrinsicParabolics_of_ne_four hn] at hM
        exact hM.1
    rw [hmax] at hM𝓜
    obtain ⟨W, ⟨hW0, hW⟩, rfl⟩ := hM𝓜
    obtain ⟨hd1, hdr⟩ := hdimr hW0 hW
    suffices hd : Module.finrank K W = 1 from ⟨⟨W, hline hW hd⟩, rfl⟩
    by_contra hd
    have hd2 : 2 ≤ Module.finrank K W := by omega
    have hiW := index_projIsoStabilizer_eq h hW
    have hiF := index_projIsoStabilizer_eq h hF1'.2
    rw [hF1dim] at hiF
    by_cases hn : 2 * r + ε = 4
    · rw [intrinsicParabolics_of_eq_four hn] at hM
      have hle := hM.2 _ (hmemM hF1'.1 hF1'.2)
      have hle' : ((projIsoStabilizer h r ε (hypFlag h r ε 1)).index : ℚ) ≤
          ((projIsoStabilizer h r ε W).index : ℚ) := by exact_mod_cast hle
      rw [hiW, hiF] at hle'
      have hk : Module.finrank K W = 2 := by omega
      rw [hk] at hle'
      obtain ⟨-, -, hlt⟩ := hcmp4 hn
      rw [hn] at hle'
      exact absurd hle' (not_le.mpr hlt)
    · rw [intrinsicParabolics_of_ne_four hn] at hM
      have hle := hM.2 _ (hmemM hF1'.1 hF1'.2)
      have hle' : ((projIsoStabilizer h r ε W).index : ℚ) ≤
          ((projIsoStabilizer h r ε (hypFlag h r ε 1)).index : ℚ) := by exact_mod_cast hle
      rw [hiW, hiF] at hle'
      by_cases hn5 : 5 ≤ 2 * r + ε
      · exact absurd hle' (not_le.mpr (hcmp5 hn5 _ hd2 hdr))
      · have := hcmp23 (by omega) _ hd1 hdr
        omega
  · rintro ⟨L, rfl⟩
    obtain ⟨hL0, hL⟩ := ne_bot_and_isotropic_of_mem_hypIsotropicLines h L.2
    have hLdim : Module.finrank K (L : Submodule K (HypIndex r ε → K)) = 1 := L.2.1
    have hiL := index_projIsoStabilizer_eq h hL
    rw [hLdim] at hiL
    by_cases hn : 2 * r + ε = 4
    · rw [intrinsicParabolics_of_eq_four hn]
      refine ⟨hmemM hL0 hL, fun M' hM' => ?_⟩
      rw [hmax] at hM'
      obtain ⟨W, ⟨hW0, hW⟩, rfl⟩ := hM'
      obtain ⟨hd1, hdr⟩ := hdimr hW0 hW
      have hiW := index_projIsoStabilizer_eq h hW
      suffices hq' : ((projIsoStabilizer h r ε W).index : ℚ) ≤
          ((projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K))).index : ℚ) by
        exact_mod_cast hq'
      rw [hiW, hiL]
      rcases Nat.lt_or_ge (Module.finrank K W) 2 with hk | hk
      · rw [show Module.finrank K W = 1 by omega]
      · obtain ⟨-, -, hlt⟩ := hcmp4 hn
        rw [show Module.finrank K W = 2 by omega, hn]
        exact hlt.le
    · rw [intrinsicParabolics_of_ne_four hn]
      refine ⟨hmemM hL0 hL, fun M' hM' => ?_⟩
      have hM'' : M' ∈ maximalParabolics h r ε := hM'
      rw [hmax] at hM''
      obtain ⟨W, ⟨hW0, hW⟩, rfl⟩ := hM''
      obtain ⟨hd1, hdr⟩ := hdimr hW0 hW
      have hiW := index_projIsoStabilizer_eq h hW
      suffices hq' : ((projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K))).index : ℚ) ≤
          ((projIsoStabilizer h r ε W).index : ℚ) by
        exact_mod_cast hq'
      rw [hiW, hiL]
      rcases Nat.lt_or_ge (Module.finrank K W) 2 with hk | hk
      · rw [show Module.finrank K W = 1 by omega]
      · by_cases hn5 : 5 ≤ 2 * r + ε
        · exact (hcmp5 hn5 _ hk hdr).le
        · have := hcmp23 (by omega) _ hd1 hdr
          omega

theorem unitary_intrinsic_point_stabilizers (hr : 1 ≤ r) (hε : ε ≤ 1) :
    intrinsicParabolics h r ε = Set.range (fun L : hypIsotropicLines h r ε =>
      projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K))) ∧
    (intrinsicParabolics h r ε).Nonempty ∧
    (∀ α : hypPSU h r ε ≃* hypPSU h r ε, ∀ M : Subgroup (hypPSU h r ε),
      M ∈ intrinsicParabolics h r ε ↔
        M.map (α : hypPSU h r ε →* hypPSU h r ε) ∈ intrinsicParabolics h r ε) ∧
    ∀ α : hypPSU h r ε ≃* hypPSU h r ε, ∃ φ : Equiv.Perm (hypIsotropicLines h r ε),
      ∀ L L' : hypIsotropicLines h r ε,
        (projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K))).map
            (α : hypPSU h r ε →* hypPSU h r ε) =
          projIsoStabilizer h r ε (L' : Submodule K (HypIndex r ε → K)) ↔ L' = φ L := by
  classical
  have hE := intrinsicParabolics_eq h hr hε
  obtain ⟨-, -, hinj⟩ := unitary_maximal_parabolics h hr hε
  have hinj' : Function.Injective fun L : hypIsotropicLines h r ε =>
      projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K)) := by
    intro L L' hLL'
    have h1 := ne_bot_and_isotropic_of_mem_hypIsotropicLines h L.2
    have h2 := ne_bot_and_isotropic_of_mem_hypIsotropicLines h L'.2
    exact Subtype.ext (hinj h1 h2 hLL')
  have hperm : ∀ α : hypPSU h r ε ≃* hypPSU h r ε, ∀ M : Subgroup (hypPSU h r ε),
      M ∈ intrinsicParabolics h r ε ↔
        M.map (α : hypPSU h r ε →* hypPSU h r ε) ∈ intrinsicParabolics h r ε := by
    intro α M
    refine ⟨map_mem_intrinsicParabolics h α, fun hM => ?_⟩
    have := map_mem_intrinsicParabolics h α.symm hM
    rwa [show (M.map (α : hypPSU h r ε →* hypPSU h r ε)).map
      (α.symm : hypPSU h r ε →* hypPSU h r ε) = M from
      (MulEquiv.mapSubgroup α).symm_apply_apply M] at this
  have hF1 : hypFlag h r ε 1 ∈ hypIsotropicLines h r ε := by
    rw [hypFlag_eq_posFlag h hε (by omega)]
    exact ⟨finrank_posFlag hr, fun a ha => posFlag_isotropic h hr a ha a ha⟩
  have hmemE : ∀ L : hypIsotropicLines h r ε,
      projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K)) ∈
        intrinsicParabolics h r ε := fun L => by
    rw [hE]
    exact ⟨L, rfl⟩
  refine ⟨hE, ⟨_, hmemE ⟨_, hF1⟩⟩, hperm, fun α => ?_⟩
  have himg : ∀ L : hypIsotropicLines h r ε, ∃ L' : hypIsotropicLines h r ε,
      (projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K))).map
          (α : hypPSU h r ε →* hypPSU h r ε) =
        projIsoStabilizer h r ε (L' : Submodule K (HypIndex r ε → K)) := by
    intro L
    have hmem := (hperm α _).mp (hmemE L)
    rw [hE] at hmem
    obtain ⟨L', hL'⟩ := hmem
    exact ⟨L', hL'.symm⟩
  choose φf hφf using himg
  have := h.finite
  have : Finite (HypIndex r ε → K) := inferInstance
  have hφinj : Function.Injective φf := by
    intro L₁ L₂ h12
    apply hinj'
    have h1 := hφf L₁
    have h2 := hφf L₂
    rw [h12] at h1
    exact (MulEquiv.mapSubgroup α).injective (h1.trans h2.symm)
  set φ : Equiv.Perm (hypIsotropicLines h r ε) :=
    Equiv.ofBijective φf (Finite.injective_iff_bijective.mp hφinj)
  refine ⟨φ, fun L L' => ⟨fun hLL' => hinj' (hLL'.symm.trans (hφf L)), fun hLL' => ?_⟩⟩
  rw [hLL']
  exact hφf L

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

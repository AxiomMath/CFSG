module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module Subgroup

open scoped Pointwise

variable {K : Type*} [Field K] {n : ℕ}

theorem flagStabilizer_singleton (d : ℕ) :
    flagStabilizer n K {d} = stabilizer (flagSpace n K d) := by
  ext g
  rw [mem_flagStabilizer]
  exact ⟨fun h => h d rfl, fun h i hi => (Set.mem_singleton_iff.mp hi) ▸ h⟩

theorem stabilizer_map_conj (g : SpecialLinearGroup (Fin n) K) (W : Submodule K (Fin n → K)) :
    (stabilizer W).map (MulAut.conj g : SpecialLinearGroup (Fin n) K →*
      SpecialLinearGroup (Fin n) K) =
      stabilizer (W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) := by
  rw [stabilizer_eq_mulAction_stabilizer, stabilizer_eq_mulAction_stabilizer,
    ← smul_submodule_eq_map, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rfl

theorem projStabilizer_map_conj (g : SpecialLinearGroup (Fin n) K)
    (W : Submodule K (Fin n → K)) :
    (projStabilizer W).map (MulAut.conj (proj n K g) : projectiveSL n K →* projectiveSL n K) =
      projStabilizer (W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) := by
  rw [projStabilizer, projStabilizer, ← stabilizer_map_conj, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem comap_projStabilizer (W : Submodule K (Fin n → K)) :
    (projStabilizer W).comap (proj n K) = stabilizer W := by
  rw [projStabilizer, Subgroup.comap_map_eq_self]
  rw [ker_proj]
  exact scalars_le_stabilizer W

theorem reflection_notMem_stabilizer {d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    reflection n K d hd hdn ∉ stabilizer (flagSpace n K d) := by
  rw [← flagStabilizer_singleton]
  exact fun h => ((subflag_stabilizer_generation (K := K) (n := n) {d}).2.2 d hd hdn).mp h rfl

theorem stabilizer_flagSpace_ne_top {d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    stabilizer (flagSpace n K d) ≠ ⊤ := fun h =>
  reflection_notMem_stabilizer hd hdn (h ▸ mem_top _)

theorem upperTriangular_le_stabilizer_flagSpace (d : ℕ) :
    upperTriangular n K ≤ stabilizer (flagSpace n K d) := by
  rw [← flagStabilizer_singleton]
  exact upperTriangular_le_flagStabilizer {d}

theorem eq_of_stabilizer_flagSpace_le {d : ℕ} (A : Subgroup (SpecialLinearGroup (Fin n) K))
    (hA : stabilizer (flagSpace n K d) ≤ A) :
    A = stabilizer (flagSpace n K d) ∨ A = ⊤ := by
  obtain ⟨hAI, -⟩ := borel_overgroups A ((upperTriangular_le_stabilizer_flagSpace d).trans hA)
  have hsub : borelOvergroupCuts A ⊆ {d} := by
    rintro e ⟨he, hen, hnot⟩
    by_contra hed
    exact hnot (hA (reflection_mem_stabilizer_of_ne he hen fun h =>
      hed (Set.mem_singleton_iff.mpr h.symm)))
  rcases Set.subset_singleton_iff_eq.mp hsub with h | h
  · right
    rw [hAI, h, flagStabilizer_empty]
  · left
    rw [hAI, h, flagStabilizer_singleton]

theorem isCoatom_projStabilizer_flagSpace {d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    IsCoatom (projStabilizer (flagSpace n K d)) := by
  refine ⟨fun h => stabilizer_flagSpace_ne_top (K := K) hd hdn ?_, fun M hM => ?_⟩
  · rw [← comap_projStabilizer, h, comap_top]
  · have hle : stabilizer (flagSpace n K d) ≤ M.comap (proj n K) := by
      rw [← comap_projStabilizer]
      exact comap_mono hM.le
    rcases eq_of_stabilizer_flagSpace_le _ hle with h | h
    · refine absurd ?_ hM.ne'
      rw [projStabilizer, ← h, map_comap_eq_self_of_surjective (proj_surjective n K)]
    · rw [← map_comap_eq_self_of_surjective (proj_surjective n K) M, h,
        map_top_of_surjective _ (proj_surjective n K)]

theorem one_le_finrank_and_lt {W : Submodule K (Fin n → K)} (h0 : ⊥ < W) (htop : W < ⊤) :
    1 ≤ finrank K W ∧ finrank K W < n := by
  refine ⟨Nat.one_le_iff_ne_zero.mpr fun h => h0.ne' (Submodule.finrank_eq_zero.mp h), ?_⟩
  have := Submodule.finrank_lt htop.ne
  rwa [finrank_fin_fun] at this

theorem isCoatom_projStabilizer {W : Submodule K (Fin n → K)} (h0 : ⊥ < W) (htop : W < ⊤) :
    IsCoatom (projStabilizer W) := by
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq W
  obtain ⟨hd, hdn⟩ := one_le_finrank_and_lt h0 htop
  rw [← hg, ← projStabilizer_map_conj]
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj (proj n K g))) _).mpr
    (isCoatom_projStabilizer_flagSpace hd hdn)

theorem eq_projStabilizer_of_isCoatom {M : Subgroup (projectiveSL n K)} (hM : IsCoatom M)
    (hBM : projUpperTriangular n K ≤ M) :
    ∃ d, 1 ≤ d ∧ d < n ∧ M = projStabilizer (flagSpace n K d) := by
  set A := M.comap (proj n K) with hAdef
  have hBA : upperTriangular n K ≤ A := by
    rw [hAdef, ← Subgroup.map_le_iff_le_comap]
    exact hBM
  have hMA : M = A.map (proj n K) := (map_comap_eq_self_of_surjective (proj_surjective n K) M).symm
  obtain ⟨hAI, -⟩ := borel_overgroups A hBA
  obtain ⟨d, hdmem⟩ : (borelOvergroupCuts A).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    apply hM.1
    rw [hMA, hAI, h, flagStabilizer_empty, map_top_of_surjective _ (proj_surjective n K)]
  obtain ⟨hd, hdn, -⟩ := id hdmem
  refine ⟨d, hd, hdn, ?_⟩
  have hle : M ≤ projStabilizer (flagSpace n K d) := by
    rw [hMA, projStabilizer]
    refine map_mono ?_
    rw [hAI, ← flagStabilizer_singleton]
    exact fun g hg => mem_flagStabilizer.mpr fun i hi =>
      mem_flagStabilizer.mp hg i ((Set.mem_singleton_iff.mp hi) ▸ hdmem)
  rcases hM.le_iff.mp hle with h | h
  · exact absurd h (isCoatom_projStabilizer_flagSpace hd hdn).1
  · exact h.symm

theorem projUpperTriangular_le_projStabilizer (d : ℕ) :
    projUpperTriangular n K ≤ projStabilizer (flagSpace n K d) :=
  map_mono (upperTriangular_le_stabilizer_flagSpace d)

theorem sylowNormalizers_eq [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hn : 1 ≤ n) :
    sylowNormalizers (projectiveSL n K) p =
      {B₀ | ∃ x : projectiveSL n K, B₀ = (projUpperTriangular n K).map
        (MulAut.conj x : projectiveSL n K →* projectiveSL n K)} := by
  obtain ⟨-, -, h3, -, h5⟩ := sylow_normalizers (K := K) p hn
  rw [h5, h3]

theorem maximal_parabolics [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hn : 1 ≤ n) :
    maximalParabolics (projectiveSL n K) p =
      projStabilizer '' {W : Submodule K (Fin n → K) | ⊥ < W ∧ W < ⊤} ∧
    Set.InjOn projStabilizer {W : Submodule K (Fin n → K) | ⊥ < W ∧ W < ⊤} ∧
    ∀ W : Submodule K (Fin n → K), ⊥ < W → W < ⊤ → IsCoatom (projStabilizer W) := by
  classical
  have hsyl := sylowNormalizers_eq (K := K) p hn
  refine ⟨?_, ?_, fun W h0 htop => isCoatom_projStabilizer h0 htop⟩
  · ext M
    constructor
    · rintro ⟨hM, B₀, hB₀, hle⟩
      rw [hsyl] at hB₀
      obtain ⟨x, rfl⟩ := hB₀
      obtain ⟨g, rfl⟩ := proj_surjective n K x
      set e := MulEquiv.mapSubgroup (MulAut.conj (proj n K g)) with he
      have hM' : IsCoatom (e.symm M) := by
        rw [← OrderIso.isCoatom_iff e, OrderIso.apply_symm_apply]
        exact hM
      have hBM' : projUpperTriangular n K ≤ e.symm M := by
        rw [← e.le_iff_le, OrderIso.apply_symm_apply]
        exact hle
      obtain ⟨d, hd, hdn, hMd⟩ := eq_projStabilizer_of_isCoatom hM' hBM'
      refine ⟨(flagSpace n K d).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)), ?_, ?_⟩
      · have hfin : finrank K ((flagSpace n K d).map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) =
            d :=
          (LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) _).trans
            (finrank_flagSpace hdn.le)
        refine ⟨bot_lt_iff_ne_bot.mpr fun h => ?_, lt_top_iff_ne_top.mpr fun h => ?_⟩
        · rw [h, finrank_bot] at hfin
          omega
        · rw [h, finrank_top, finrank_fin_fun] at hfin
          omega
      · rw [← projStabilizer_map_conj, ← hMd]
        exact e.apply_symm_apply M
    · rintro ⟨W, ⟨h0, htop⟩, rfl⟩
      refine ⟨isCoatom_projStabilizer h0 htop, ?_⟩
      obtain ⟨g, hg⟩ := exists_map_flagSpace_eq W
      refine ⟨(projUpperTriangular n K).map
        (MulAut.conj (proj n K g) : projectiveSL n K →* projectiveSL n K), ?_, ?_⟩
      · rw [hsyl]
        exact ⟨_, rfl⟩
      · rw [← hg, ← projStabilizer_map_conj]
        exact map_mono (projUpperTriangular_le_projStabilizer _)
  · rintro W ⟨h0, htop⟩ W' ⟨h0', htop'⟩ hWW'
    have hS : stabilizer W = stabilizer W' := by
      rw [← comap_projStabilizer, hWW', comap_projStabilizer]
    obtain ⟨g, hg⟩ := exists_map_flagSpace_eq W
    obtain ⟨hd, hdn⟩ := one_le_finrank_and_lt h0 htop
    set d := finrank K W with hddef
    have hgg : (g : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
      congrArg Subtype.val (mul_inv_cancel g)
    set X := W'.map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))
      with hX
    have hXW' : X.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W' := by
      rw [hX, ← Submodule.map_comp, ← mulVecLin_mul, hgg, mulVecLin_one, Submodule.map_id]
    have hinv : ∀ k ∈ flagStabilizer n K {d}, ∀ v ∈ X, (k : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ X := by
      rintro k hk _ ⟨w, hw, rfl⟩
      rw [flagStabilizer_singleton] at hk
      have hconj : g * k * g⁻¹ ∈ stabilizer W' := by
        rw [← hS, ← hg, ← stabilizer_map_conj]
        exact ⟨k, hk, rfl⟩
      have hmem : ((g * k * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈
          W' := by
        rw [← mem_stabilizer.mp hconj]
        exact ⟨w, hw, rfl⟩
      refine ⟨_, hmem, ?_⟩
      change ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((g * k * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) =
        (k : Matrix (Fin n) (Fin n) K) *ᵥ
          (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w)
      have hmat : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g * k * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (k : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        congrArg Subtype.val (show g⁻¹ * (g * k * g⁻¹) = k * g⁻¹ by group)
      rw [mulVec_mulVec, hmat, ← mulVec_mulVec]
    have hfinX : finrank K X = finrank K W' :=
      LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g⁻¹) W'
    obtain ⟨hd', hdn'⟩ := one_le_finrank_and_lt h0' htop'
    rcases ((subflag_stabilizer_generation (K := K) (n := n) {d}).2.1 X).mp hinv with
      hXb | hXt | ⟨i, hi, hXi⟩
    · rw [hXb, finrank_bot] at hfinX
      omega
    · rw [hXt, finrank_top, finrank_fin_fun] at hfinX
      omega
    · rw [Set.mem_singleton_iff.mp hi] at hXi
      rw [← hXW', hXi, hg]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial

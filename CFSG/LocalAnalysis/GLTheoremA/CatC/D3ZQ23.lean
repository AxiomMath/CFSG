module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ4

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.StandardType.GGOppRadExc


section Degree

variable {K : Type} [Field K] [Finite K]

theorem parabolicDegree_permLattice {J : Set (Fin Tag.D4.rank)} {ε : ℕ}
    (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J) (β : Fin Tag.D4.rank → ℤ) :
    parabolicDegree Tag.D4 J (permLattice (d4Rho ^ ε) β) = parabolicDegree Tag.D4 J β := by
  classical
  unfold parabolicDegree
  refine Fintype.sum_equiv (d4Rho ^ ε).symm _ _ (fun i => ?_)
  have hi : i ∈ J ↔ (d4Rho ^ ε).symm i ∈ J := by
    have := hJρ ((d4Rho ^ ε).symm i)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  by_cases h : i ∈ J
  · rw [if_pos h, if_pos (hi.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hi.2 h'))]
    rfl

theorem permLattice_degSet {J : Set (Fin Tag.D4.rank)} {ε : ℕ}
    (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J) {d : ℤ} {β : Fin Tag.D4.rank → ℤ}
    (hβ : β ∈ degSet Tag.D4 J d) : permLattice (d4Rho ^ ε) β ∈ degSet Tag.D4 J d := by
  obtain ⟨h1, h2⟩ := hβ
  refine ⟨permLattice_radical hJρ h1, ?_⟩
  rw [parabolicDegree_permLattice hJρ β]
  exact h2

theorem phi_degSeries_le {J : Set (Fin Tag.D4.rank)} {g : ModGL Tag.D4 K}
    (hg : g ∈ borelGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) {ε : ℕ}
    (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J) (d : ℤ) :
    ∀ q ∈ degSeries Tag.D4 K J d, phiG g a σ ε q ∈ degSeries Tag.D4 K J d := by
  have hgN : g ∈ Subgroup.normalizer (degSeries Tag.D4 K J d : Set (ModGL Tag.D4 K)) :=
    parabolicSubgroup_le_normalizer_degSeries d (borelGroup_le_parabolicSubgroup J hg)
  have hle : degSeries Tag.D4 K J d ≤ (degSeries Tag.D4 K J d).comap (phiG g a σ ε) := by
    unfold degSeries rootSpan
    refine iSup₂_le fun β hβ => ?_
    unfold rootSubgroup
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨e, he⟩ := exists_d4F_pinnedX (K := K) a σ ε
    have hroot := (mem_parabolicRadicalRoots_iff.1 hβ.1).1
    show phiG g a σ ε (pinnedX Tag.D4 K β c) ∈ rootSpan Tag.D4 K (degSet Tag.D4 J d)
    rw [phiG_apply, he β hroot c]
    have hmem : pinnedX Tag.D4 K (permLattice (d4Rho ^ ε) β) (e β * σ c) ∈
        rootSpan Tag.D4 K (degSet Tag.D4 J d) :=
      Subgroup.mem_iSup_of_mem (permLattice (d4Rho ^ ε) β)
        (Subgroup.mem_iSup_of_mem (permLattice_degSet hJρ hβ) (Subgroup.subset_closure ⟨_, rfl⟩))
    exact (Subgroup.mem_normalizer_iff.1 hgN _).1 hmem
  exact fun q hq => hle hq

end Degree

section PCore

variable {τ : Tag} {K : Type} [Field K]

theorem pCoreOf_parabolicSubgroup_three [Finite K] [CharP K 3] (J : Set (Fin τ.rank)) :
    pCoreOf 3 (parabolicSubgroup τ K J) = parabolicRadical τ K J :=
  pCoreOf_parabolicSubgroup_prime 3 J

theorem parabolicRadical_empty_three : parabolicRadical τ K ∅ = posUnipotent τ K := by
  unfold parabolicRadical posUnipotent
  congr 1
  ext α
  simp only [parabolicRadicalRoots, parabolicPosRoots, parabolicRoots, Set.mem_sdiff,
    Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_empty_iff_false, not_false_eq_true,
    forall_const]
  exact ⟨fun h => h.1, fun h => ⟨h, fun h' => h.1.ne_zero (funext h'.1.2)⟩⟩

end PCore

end CFSG.LocalAnalysis.GLTheoremA

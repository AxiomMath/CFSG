module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Flags

variable {K : Type} [Field K]

theorem borelOvergroupCuts_upperTriangular_full (n : ℕ) :
    borelOvergroupCuts (upperTriangular n K) = {i | 1 ≤ i ∧ i < n} := by
  ext i
  constructor
  · rintro ⟨hi, hin, -⟩
    exact ⟨hi, hin⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, h3, by
      rw [← reflElt_of_lt h1 h3]
      exact reflElt_not_mem_upperTriangular h1 h3⟩

theorem upperTriangular_eq_flagStabilizer_full (n : ℕ) :
    upperTriangular n K = flagStabilizer n K {i | 1 ≤ i ∧ i < n} := by
  have := (borel_overgroups (upperTriangular n K) le_rfl).1
  rwa [borelOvergroupCuts_upperTriangular_full] at this

theorem stabilizer_flagSpace_two_one : stabilizer (flagSpace 2 K 1) = upperTriangular 2 K := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer_singleton (n := 2) (K := K) 1,
    upperTriangular_eq_flagStabilizer_full]
  congr 1
  ext i
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
  omega

end Flags

theorem isSolvable_of_overgroup_two {K : Type} [Field K] [Finite K]
    (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (M : Subgroup (projectiveSL 2 K))
    (hU : projUnitriangular 2 K ≤ M) (hne : M ≠ ⊤) : Group.IsSolvable ↥M := by
  obtain ⟨i, hi1, hi2, hM⟩ :=
    (linear_unitriangular_overgroup_subflag_containment (n := 2) (K := K)).2 M hne hU
  have hi : i = 1 := by omega
  subst hi
  have h2 : Group.IsSolvable ↥(projStabilizer (flagSpace 2 K 1)) := by
    rw [projStabilizer, stabilizer_flagSpace_two_one]
    exact isSolvable_map_hom (proj 2 K) _ (isSolvable_upperTriangular hK)
  have := h2
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hM)
    (Subgroup.inclusion_injective hM)

theorem l2even : FamL2even := by
  intro X _ _ f hq hf hX
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  let e' : X ≃* projectiveSL 2 K := e.trans (statedSLEquivProjectiveSL 2 K)
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 2) (by norm_num)
  have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hqP : CFSG.IsQuasisimple (projectiveSL 2 K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq
  exact A312For.of_mulEquiv e'
    (A312For.of_solvable_overgroups hqP _ hT₀
      (fun M hM hne => isSolvable_of_overgroup_two ⟨f, hcard⟩ M hM hne))

end CFSG.QuasithinUnique.Vol2Native.A312L

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.Pair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherExtremalParabolics

public section

namespace CFSG.Quasithin

namespace B69K

open CFSG.QuasithinUnique CFSG.QuasithinUnique.B113Lie CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem parabolicPair_projectiveSL {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) :
    ∃ U : Subgroup (projectiveSL n K), IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  obtain ⟨P0, hP0⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := n) (by omega)
  have hU0 : IsSylowTwoOf (projUnitriangular n K) ⊤ :=
    hP0 ▸ CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow P0
  have hUP : ∀ d : ℕ, projUnitriangular n K ≤ projStabilizer (flagSpace n K d) := fun d =>
    ((Subgroup.map_mono (unitriangular_le_upperTriangular n K)).trans
      (projUpperTriangular_le_projStabilizer d))
  have hco : ∀ d : ℕ, 1 ≤ d → d < n → IsCoatom (projStabilizer (flagSpace n K d)) :=
    fun d hd hdn => isCoatom_projStabilizer_flagSpace (K := K) (n := n) hd hdn
  refine ⟨projUnitriangular n K, hU0, ?_⟩
  refine parabolicPair_of_coatoms
    (Ps := (fun d : ℕ => projStabilizer (flagSpace n K d)) '' {d | 1 ≤ d ∧ d < n}) ?_ ?_ ?_ ?_
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    exact ⟨hco d hd hdn, hUP d⟩
  · intro A hUA hA
    obtain ⟨i, hi1, hin, hAi⟩ :=
      (CFSG.QuasithinUnique.Setup.X7a.linear_unitriangular_overgroup_subflag_containment
        (n := n) (K := K)).2 A hA hUA
    exact ⟨projStabilizer (flagSpace n K i), ⟨i, ⟨hi1, hin⟩, rfl⟩, hAi⟩
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    refine ⟨proj n K (reflection n K d hd hdn), ?_, ?_⟩
    · intro h
      have h' : reflection n K d hd hdn ∈
          (projStabilizer (flagSpace n K d)).comap (proj n K) := h
      rw [comap_projStabilizer] at h'
      exact reflection_notMem_stabilizer hd hdn h'
    · rintro P' ⟨j, ⟨hj, hjn⟩, rfl⟩ hne
      have hjd : j ≠ d := fun h => hne (by rw [h])
      have hmem : reflection n K d hd hdn ∈ stabilizer (flagSpace n K j) :=
        reflection_mem_stabilizer_of_ne hd hdn hjd
      have h' : reflection n K d hd hdn ∈
          (projStabilizer (flagSpace n K j)).comap (proj n K) := by
        rw [comap_projStabilizer]
        exact hmem
      exact h'
  · refine ⟨projStabilizer (flagSpace n K 1), ⟨1, ⟨le_rfl, by omega⟩, rfl⟩,
      projStabilizer (flagSpace n K 2), ⟨2, ⟨by norm_num, by omega⟩, rfl⟩, ?_⟩
    intro h
    have h1 := index_projStabilizer (K := K) (n := n) (flagSpace n K 1)
    have h2 := index_projStabilizer (K := K) (n := n) (flagSpace n K 2)
    rw [finrank_flagSpace (by omega)] at h1 h2
    have hq : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
    have hg := (gaussian_minimum hq (by omega : 3 ≤ n) (k := 2) (by norm_num) (by omega)).2.2
    have heq : gaussianCoeff n 2 (Nat.card K) = gaussianCoeff n 1 (Nat.card K) := by
      rw [← h1, ← h2, h]
    rcases hg.mp heq with h | h <;> omega

end B69K

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Tags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieLinCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.B113Lie CFSG.LocalAnalysis.ComponentInitial

  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem la_sylowFacts_projective {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) [IsSimpleGroup (projectiveSL n K)] :
    SylowFacts (projectiveSL n K) (projUnitriangular n K) := by
  obtain ⟨P0, hP0⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := n) (by omega)
  have hU0 : IsSylowTwoOf (projUnitriangular n K) ⊤ :=
    hP0 ▸ CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow P0
  have hUP : ∀ d : ℕ, projUnitriangular n K ≤ projStabilizer (flagSpace n K d) := fun d =>
    ((Subgroup.map_mono (unitriangular_le_upperTriangular n K)).trans
      (projUpperTriangular_le_projStabilizer d))
  have hco : ∀ d : ℕ, 1 ≤ d → d < n → projStabilizer (flagSpace n K d) ⋖ ⊤ := fun d hd hdn =>
    (isCoatom_projStabilizer_flagSpace (K := K) (n := n) hd hdn).covBy_top
  have hne : projStabilizer (flagSpace n K 1) ≠ projStabilizer (flagSpace n K 2) := by
    intro heq
    have h1 := congrArg (Subgroup.comap (proj n K)) heq
    rw [comap_projStabilizer, comap_projStabilizer] at h1
    have hmem : reflection n K 1 (le_refl _) (by omega) ∈ stabilizer (flagSpace n K 2) :=
      reflection_mem_stabilizer_of_ne (by norm_num) (by omega) (by norm_num)
    exact reflection_notMem_stabilizer (n := n) (K := K) (le_refl 1) (by omega) (h1 ▸ hmem)
  have hX : pCoreOf 2 (⊤ : Subgroup (projectiveSL n K)) = ⊥ :=
    pCoreOf_top_eq_bot_of_simple hU0 (hUP 1) (hco 1 (le_refl _) (by omega)).lt.ne
  have hU1 : projUnitriangular n K ≠ ⊥ :=
    ne_bot_of_two_dvd hU0 (Lin.two_dvd_card_projectiveSL (n := n) (K := K) (by omega))
  refine (ParabolicData.of_coatoms
    (Ps := (fun d : ℕ => projStabilizer (flagSpace n K d)) '' {d | 1 ≤ d ∧ d < n})
    hU0 hU1 hX ?_ ?_ ?_ ?_).sylowFacts
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    exact ⟨hco d hd hdn, hUP d⟩
  · exact ⟨projStabilizer (flagSpace n K 1), ⟨1, ⟨le_refl _, by omega⟩, rfl⟩,
      projStabilizer (flagSpace n K 2), ⟨2, ⟨by norm_num, by omega⟩, rfl⟩, hne⟩
  · intro A hUA hA
    obtain ⟨i, hi1, hin, hAi⟩ :=
      (CFSG.QuasithinUnique.Setup.X7a.linear_unitriangular_overgroup_subflag_containment
        (n := n) (K := K)).2 A hA hUA
    exact ⟨projStabilizer (flagSpace n K i), ⟨i, ⟨hi1, hin⟩, rfl⟩, hAi⟩
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    exact Lin.charTwo_projStabilizer (by omega) hdn

theorem asLieTwoPSLGe4_holds : AsLieTwoPSLGe4 := by
  intro n f X _ _ hn hS hadm hmod
  have hmc : StatedClassicalModel X .PSL n 2 f := hmod.statedClassicalModel (by decide)
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hmc
  have hCh : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hadm.2.1 hcard
  let e' : X ≃* projectiveSL n K := e.trans (Setup.X7a.statedSLEquivProjectiveSL n K)
  have hsimp : IsSimpleGroup (projectiveSL n K) := e'.symm.isSimpleGroup
  have hall : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → SylowFacts X T := fun T hT =>
    SylowFacts.of_mulEquiv_isSylow e' (la_sylowFacts_projective (n := n) (K := K) (by omega)) hT
  exact ⟨overgroups_of_forall_sylowFacts hall, oddAut_of_forall_sylowFacts hall⟩

end CFSG.Quasithin.LieOver

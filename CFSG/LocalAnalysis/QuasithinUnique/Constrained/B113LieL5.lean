module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieLinCent
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.QuasithinUnique.B113Lie

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem l5_sylowFacts_concrete {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    [IsSimpleGroup (projectiveSL 5 K)] [CharP K 2] :
    SylowFacts (projectiveSL 5 K) (projUnitriangular 5 K) := by
  obtain ⟨P0, hP0⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 5) (by norm_num)
  have hU0 : IsSylowTwoOf (projUnitriangular 5 K) ⊤ := hP0 ▸ isSylowTwoOf_top_of_sylow P0
  have hUP : ∀ d : ℕ, projUnitriangular 5 K ≤ projStabilizer (flagSpace 5 K d) := fun d =>
    ((Subgroup.map_mono (unitriangular_le_upperTriangular 5 K)).trans
      (projUpperTriangular_le_projStabilizer d))
  have hco : ∀ d : ℕ, 1 ≤ d → d < 5 → projStabilizer (flagSpace 5 K d) ⋖ ⊤ := fun d hd hd5 =>
    (isCoatom_projStabilizer_flagSpace hd hd5).covBy_top
  have hne : projStabilizer (flagSpace 5 K 1) ≠ projStabilizer (flagSpace 5 K 2) := by
    intro heq
    have h1 := congrArg (Subgroup.comap (proj 5 K)) heq
    rw [comap_projStabilizer, comap_projStabilizer] at h1
    have hmem : reflection 5 K 1 (le_refl _) (by norm_num) ∈ stabilizer (flagSpace 5 K 2) :=
      reflection_mem_stabilizer_of_ne (by norm_num) (by norm_num) (by norm_num)
    exact reflection_notMem_stabilizer (K := K) (le_refl 1) (by norm_num) (h1 ▸ hmem)
  have hX : pCoreOf 2 (⊤ : Subgroup (projectiveSL 5 K)) = ⊥ :=
    pCoreOf_top_eq_bot_of_simple hU0 (hUP 1) (hco 1 (le_refl _) (by norm_num)).lt.ne
  have hU1 : projUnitriangular 5 K ≠ ⊥ :=
    ne_bot_of_two_dvd hU0 (Lin.two_dvd_card_projectiveSL (by norm_num))
  refine (ParabolicData.of_coatoms
    (Ps := (fun d : ℕ => projStabilizer (flagSpace 5 K d)) '' {d | 1 ≤ d ∧ d < 5})
    hU0 hU1 hX ?_ ?_ ?_ ?_).sylowFacts
  · rintro P ⟨d, ⟨hd, hd5⟩, rfl⟩
    exact ⟨hco d hd hd5, hUP d⟩
  · exact ⟨_, ⟨1, ⟨le_refl _, by norm_num⟩, rfl⟩, _, ⟨2, ⟨by norm_num, by norm_num⟩, rfl⟩, hne⟩
  · intro A hUA hA
    obtain ⟨M, hAM, hM⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.2 hA)
    have hBM : projUpperTriangular 5 K ≤ M :=
      ((Subgroup.map_mono (Vol2Native.A312L.upperTriangular_le_unitriangular hK)).trans
        hUA).trans hAM
    obtain ⟨d, hd, hd5, hMd⟩ := eq_projStabilizer_of_isCoatom hM.isCoatom hBM
    exact ⟨_, ⟨d, ⟨hd, hd5⟩, rfl⟩, show A ≤ projStabilizer (flagSpace 5 K d) from hMd ▸ hAM⟩
  · rintro P ⟨d, ⟨hd, hd5⟩, rfl⟩
    exact Lin.charTwo_projStabilizer (by omega) hd5

theorem l5_sylowFacts {S : Type} [Group S] [Finite S] (hX : StatedClassicalModel S .PSL 5 2 1)
    {T : Subgroup S} (hT : IsSylowTwoOf T ⊤) : SylowFacts S T := by
  have hS : IsSimpleGroup S := (CFSG.LieType.Simplicity.fam_PSL_simplicity S 5 2 1 hX).2
  obtain ⟨⟨-, hf, -⟩, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have hCh : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  let e' : S ≃* projectiveSL 5 K := e.trans (Setup.X7a.statedSLEquivProjectiveSL 5 K)
  have : IsSimpleGroup (projectiveSL 5 K) := e'.symm.isSimpleGroup
  exact SylowFacts.of_mulEquiv_isSylow e' (l5_sylowFacts_concrete hK2) hT

end CFSG.QuasithinUnique.B113Lie

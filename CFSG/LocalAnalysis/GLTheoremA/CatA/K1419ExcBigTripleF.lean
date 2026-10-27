module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcBigDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section Levi

@[expose] def k1419eVecF4 (a b c d : ℤ) : Fin Tag.F4.rank → ℤ := ![a, b, c, d]

theorem k1419e_f4_B3_data :
    (List.ofFn (k1419eVecF4 1 0 0 0) ∈ Tag.F4.artifactRoots ∧
      List.ofFn (k1419eVecF4 0 0 1 0) ∈ Tag.F4.artifactRoots ∧
      List.ofFn (k1419eVecF4 1 2 2 0) ∈ Tag.F4.artifactRoots) ∧
    (k1419eSoList Tag.F4 (k1419eVecF4 1 0 0 0) (k1419eVecF4 0 0 1 0) ∧
      k1419eSoList Tag.F4 (k1419eVecF4 1 0 0 0) (k1419eVecF4 1 2 2 0) ∧
      k1419eSoList Tag.F4 (k1419eVecF4 0 0 1 0) (k1419eVecF4 1 2 2 0)) := by
  decide +kernel

theorem k1419e_f4_C3_data :
    (List.ofFn (k1419eVecF4 0 1 0 0) ∈ Tag.F4.artifactRoots ∧
      List.ofFn (k1419eVecF4 0 1 2 0) ∈ Tag.F4.artifactRoots ∧
      List.ofFn (k1419eVecF4 0 1 2 2) ∈ Tag.F4.artifactRoots) ∧
    (k1419eSoList Tag.F4 (k1419eVecF4 0 1 0 0) (k1419eVecF4 0 1 2 0) ∧
      k1419eSoList Tag.F4 (k1419eVecF4 0 1 0 0) (k1419eVecF4 0 1 2 2) ∧
      k1419eSoList Tag.F4 (k1419eVecF4 0 1 2 0) (k1419eVecF4 0 1 2 2)) := by
  decide +kernel

theorem k1419e_f4_B3_coord : ∀ i : Fin Tag.F4.rank, ¬ i.val ≤ 2 →
    k1419eVecF4 1 0 0 0 i = 0 ∧ k1419eVecF4 0 0 1 0 i = 0 ∧ k1419eVecF4 1 2 2 0 i = 0 := by
  decide

theorem k1419e_f4_C3_coord : ∀ i : Fin Tag.F4.rank, ¬ 1 ≤ i.val →
    k1419eVecF4 0 1 0 0 i = 0 ∧ k1419eVecF4 0 1 2 0 i = 0 ∧ k1419eVecF4 0 1 2 2 i = 0 := by
  decide


theorem k1419e_f4_hasTriple_B3 :
    k1419eHasTriple Tag.F4 (parabolicRoots Tag.F4 {j : Fin Tag.F4.rank | j.val ≤ 2}) := by
  obtain ⟨⟨r₁, r₂, r₃⟩, o₁₂, o₁₃, o₂₃⟩ := k1419e_f4_B3_data
  refine ⟨k1419eVecF4 1 0 0 0, ⟨isRoot_iff_mem_artifactRoots.2 r₁, fun i hi => ?_⟩,
    k1419eVecF4 0 0 1 0, ⟨isRoot_iff_mem_artifactRoots.2 r₂, fun i hi => ?_⟩,
    k1419eVecF4 1 2 2 0, ⟨isRoot_iff_mem_artifactRoots.2 r₃, fun i hi => ?_⟩,
    o₁₂.strongOrth, o₁₃.strongOrth, o₂₃.strongOrth⟩
  · exact (k1419e_f4_B3_coord i hi).1
  · exact (k1419e_f4_B3_coord i hi).2.1
  · exact (k1419e_f4_B3_coord i hi).2.2

theorem k1419e_f4_hasTriple_C3 :
    k1419eHasTriple Tag.F4 (parabolicRoots Tag.F4 {j : Fin Tag.F4.rank | 1 ≤ j.val}) := by
  obtain ⟨⟨r₁, r₂, r₃⟩, o₁₂, o₁₃, o₂₃⟩ := k1419e_f4_C3_data
  refine ⟨k1419eVecF4 0 1 0 0, ⟨isRoot_iff_mem_artifactRoots.2 r₁, fun i hi => ?_⟩,
    k1419eVecF4 0 1 2 0, ⟨isRoot_iff_mem_artifactRoots.2 r₂, fun i hi => ?_⟩,
    k1419eVecF4 0 1 2 2, ⟨isRoot_iff_mem_artifactRoots.2 r₃, fun i hi => ?_⟩,
    o₁₂.strongOrth, o₁₃.strongOrth, o₂₃.strongOrth⟩
  · exact (k1419e_f4_C3_coord i hi).1
  · exact (k1419e_f4_C3_coord i hi).2.1
  · exact (k1419e_f4_C3_coord i hi).2.2

theorem k1419e_f4_hasTriple_univ :
    k1419eHasTriple Tag.F4 (parabolicRoots Tag.F4 (Set.univ : Set (Fin Tag.F4.rank))) :=
  k1419e_f4_hasTriple_B3.mono fun _ h => ⟨h.1, fun i hi => (hi (Set.mem_univ i)).elim⟩

end Levi

section Dispatch


theorem k1419e_hasTriple_F4 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    k1419eHasTriple Tag.F4 (componentRoots (rootCharHom a) i) := by
  classical
  have hT3 : rootDiagUnit Tag.F4 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨v, μ, x, c, hμ, hc, hcomp, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S Nat.prime_three
      (k1419e_natCast_three_ne_zero L) hT3 i
  have hnonA' : ¬ (1 ≤ c.length ∧ kacCount Tag.F4 ![2, 3, 4, 2]
      (c.map (idxNode (r := Tag.F4.rank))).toFinset = c.length * (c.length + 1)) := by
    rw [hrank, hncard] at hnonA
    exact hnonA
  rcases f4_nonA_cases c hc hlen hnonA' with rfl | rfl | rfl | rfl | rfl
  · exact (not_comp_eq_B2_F4 (p := 3) le_rfl hμ hcomp).elim
  · rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4
      (J := {j : Fin Tag.F4.rank | j.val ≤ 2}) (by decide)
      (fun j => by simp only [Set.mem_setOf_eq]; revert j; decide)]
    exact k1419e_f4_hasTriple_B3.image_smul v
  · rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4
      (J := {j : Fin Tag.F4.rank | 1 ≤ j.val}) (by decide)
      (fun j => by simp only [Set.mem_setOf_eq]; revert j; decide)]
    exact k1419e_f4_hasTriple_C3.image_smul v
  · exact (not_comp_eq_B4_F4 hμ hcomp).elim
  · rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4
      (J := (Set.univ : Set (Fin Tag.F4.rank))) (by decide)
      (fun j => by simp only [Set.mem_univ, iff_true]; revert j; decide)]
    exact k1419e_f4_hasTriple_univ.image_smul v

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end

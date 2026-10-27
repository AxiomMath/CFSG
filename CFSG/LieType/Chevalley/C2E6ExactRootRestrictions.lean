module

public import CFSG.LieType.Chevalley.C2E6RootRestrictionTorus

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.ExteriorCube CFSG.LocalAnalysis.ComponentInitial exteriorPower Set

theorem e6_a5_d4_exact_root_restrictions
    :
    (∃ (φA : moduleA ≃ₗ[K] ⋀[K]^3 (Fin 6 → K)) (φD : moduleD ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)),
      (∀ α, IsRoot Tag.E6 α → α (1 : Fin 6) = 1 → rootVec Tag.E6 K α ∈ moduleA ∧
        ∃! I : powersetCard (Fin 6) 3, ∀ t : Fin 5,
          rootWeight (jA t) α = subsetPattern I.val t) ∧
      (∀ α, IsRoot Tag.E6 α → α (1 : Fin 6) = 1 → ∀ (hmem : rootVec Tag.E6 K α ∈ moduleA)
        (I : powersetCard (Fin 6) 3), (∀ t : Fin 5, rootWeight (jA t) α = subsetPattern I.val t) →
          φA ⟨rootVec Tag.E6 K α, hmem⟩ = wedgeBasis I) ∧
      (∀ g ∈ groupA, ∀ v ∈ moduleA, (g : Module.End K (RootModule Tag.E6 K)) v ∈ moduleA) ∧
      (∀ (t : Fin 5) (c : K) (v : RootModule Tag.E6 K) (hv : v ∈ moduleA),
        φA ⟨xOp Tag.E6 K (jA t) c v, xOp_mem_moduleA t c v hv⟩ =
            exteriorPower.map 3 (transvLin t.castSucc t.succ c) (φA ⟨v, hv⟩) ∧
          φA ⟨yOp Tag.E6 K (jA t) c v, yOp_mem_moduleA t c v hv⟩ =
            exteriorPower.map 3 (transvLin t.succ t.castSucc c) (φA ⟨v, hv⟩)) ∧
      (OrthogonalSplit.simpleRoot 4 0 = OrthogonalSplit.eps 4 0 - OrthogonalSplit.eps 4 1 ∧
        OrthogonalSplit.simpleRoot 4 1 = OrthogonalSplit.eps 4 1 - OrthogonalSplit.eps 4 2 ∧
        OrthogonalSplit.simpleRoot 4 2 = OrthogonalSplit.eps 4 2 - OrthogonalSplit.eps 4 3 ∧
        OrthogonalSplit.simpleRoot 4 3 = OrthogonalSplit.eps 4 2 + OrthogonalSplit.eps 4 3) ∧
      (∀ α, IsRoot Tag.E6 α → α (0 : Fin 6) = 1 → α (5 : Fin 6) = 1 →
        rootVec Tag.E6 K α ∈ moduleD ∧
          ∃! s : Fin 4 ⊕ Fin 4, ∀ k : Fin 4, rootWeight (jD k) α = natWeight s k) ∧
      (∀ α, IsRoot Tag.E6 α → α (0 : Fin 6) = 1 → α (5 : Fin 6) = 1 →
        ∀ (hmem : rootVec Tag.E6 K α ∈ moduleD) (s : Fin 4 ⊕ Fin 4),
          (∀ k : Fin 4, rootWeight (jD k) α = natWeight s k) →
            φD ⟨rootVec Tag.E6 K α, hmem⟩ = Pi.single s 1) ∧
      (∀ g ∈ groupD, ∀ v ∈ moduleD, (g : Module.End K (RootModule Tag.E6 K)) v ∈ moduleD) ∧
      (∀ (k : Fin 4) (c : K) (v : RootModule Tag.E6 K) (hv : v ∈ moduleD),
        φD ⟨xOp Tag.E6 K (jD k) c v, xOp_mem_moduleD k c v hv⟩ =
            OrthogonalSplit.rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c (φD ⟨v, hv⟩) ∧
          φD ⟨yOp Tag.E6 K (jD k) c v, yOp_mem_moduleD k c v hv⟩ =
            OrthogonalSplit.rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c (φD ⟨v, hv⟩)) ∧
      (∀ I : powersetCard (Fin 6) 3, diagA (wedgeBasis I) = wedgeBasis (R := K) (compRevPC I)) ∧
      (∀ (v : RootModule Tag.E6 K) (hv : v ∈ moduleA),
        φA ⟨diagE6 v, diagramMap_mem_moduleA v hv⟩ = diagA (φA ⟨v, hv⟩)) ∧
      (∀ s : Fin 4 ⊕ Fin 4,
        swapE4F4 (Pi.single s (1 : K)) = Pi.single (Equiv.swap (.inl 3) (.inr 3) s) 1) ∧
      (∀ (v : RootModule Tag.E6 K) (hv : v ∈ moduleD),
        φD ⟨diagE6 v, diagramMap_mem_moduleD v hv⟩ = swapE4F4 (φD ⟨v, hv⟩))) ∧
    (∀ c : Fin 5 → ZMod 3, torusWord jA c ∈ torusA) ∧
    (∀ c d : Fin 5 → ZMod 3, torusWord jA (c + d) = torusWord jA c * torusWord jA d) ∧
    (∀ c : Fin 5 → ZMod 3,
      torusWord jA c = 1 ↔ c = 0 ∨ c = ![1, 2, 0, 1, 2] ∨ c = ![2, 1, 0, 2, 1]) ∧
    (∀ c : Fin 5 → ZMod 3,
      (∀ v ∈ moduleA, (torusWord jA c : Module.End K (RootModule Tag.E6 K)) v = v) ↔
        torusWord jA c = 1) ∧
    (∀ c : Fin 4 → ZMod 3, torusWord jD c ∈ torusD) ∧
    (∀ c d : Fin 4 → ZMod 3, torusWord jD (c + d) = torusWord jD c * torusWord jD d) ∧
    (∀ c : Fin 4 → ZMod 3, torusWord jD c = 1 ↔ c = 0) ∧
    (∀ c : Fin 4 → ZMod 3,
      (∀ v ∈ moduleD, (torusWord jD c : Module.End K (RootModule Tag.E6 K)) v = v) ↔
        torusWord jD c = 1) ∧
    (∀ c : Fin 6 → ZMod 3,
      torusWord i6 c = 1 ↔ c = 0 ∨ c = ![1, 0, 2, 0, 1, 2] ∨ c = ![2, 0, 1, 0, 2, 1]) ∧
    ((posFixedRoots Set.univ).ncard = 12 ∧ (posPairedOrbits Set.univ).ncard = 12) ∧
    ((posFixedRoots setA).ncard = 3 ∧ (posPairedOrbits setA).ncard = 6) ∧
    ((posFixedRoots setD).ncard = 6 ∧ (posPairedOrbits setD).ncard = 3) :=
  ⟨⟨phiA, phiD,
    fun _ hα h1 => ⟨Submodule.subset_span ⟨_, hα, h1, rfl⟩, existsUnique_subset hα h1⟩,
    fun _ hα h1 hmem I hI => phiA_rootVec hα h1 hmem I hI,
    fun _ hg => mem_moduleA_of_mem_groupA hg,
    fun t c _ hv => ⟨phiA_xOp t c hv, phiA_yOp t c hv⟩,
    ⟨simpleRoot_zero, simpleRoot_one, simpleRoot_two, simpleRoot_three⟩,
    fun _ hα h0 h5 => ⟨Submodule.subset_span ⟨_, hα, h0, h5, rfl⟩, existsUnique_natWeight hα h0 h5⟩,
    fun _ hα h0 h5 hmem s hs => phiD_rootVec hα h0 h5 hmem s hs,
    fun _ hg => mem_moduleD_of_mem_groupD hg,
    fun k c _ hv => ⟨phiD_xOp k c hv, phiD_yOp k c hv⟩,
    diagA_wedgeBasis, fun _ hv => phiA_diagramMap hv, swapE4F4_single,
    fun _ hv => phiD_diagramMap hv⟩,
    torusWordA_mem, torusWord_add jA, torusWordA_eq_one_iff, fix_moduleA_iff,
    torusWordD_mem, torusWord_add jD, torusWordD_eq_one_iff, fix_moduleD_iff,
    torusWord6_eq_one_iff, ⟨ncard_posFixed_univ, ncard_posPaired_univ⟩,
    ⟨ncard_posFixed_setA, ncard_posPaired_setA⟩, ⟨ncard_posFixed_setD, ncard_posPaired_setD⟩⟩

end CFSG.LieType.Chevalley.C2E6Std

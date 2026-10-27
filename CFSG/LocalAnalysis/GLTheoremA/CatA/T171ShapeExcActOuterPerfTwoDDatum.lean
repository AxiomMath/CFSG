module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinDatum

public section

namespace CFSG.RankThree.Lattice.GenFixedRootDatum

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M] (D : GenFixedRootDatum τ p₀ k M)

theorem roots_eq_of_simpleRootsJ_eq {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hΔ : D.simpleRootsJ = (simpleRoots Ψ : Set (Fin τ.rank → ℤ))) : D.roots = Ψ := by
  have hΔ' : (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) = unionSimpleRoots D.χ D.J := by
    rw [← hΔ, simpleRootsJ_eq]
  refine Set.Subset.antisymm ?_ ?_
  · rintro γ hγ
    obtain ⟨j, hj, hγj⟩ := mem_unionRoots_iff.1 hγ
    obtain ⟨w, hw, β, hβ, rfl⟩ :=
      exists_smul_simpleRoot (isRootComponent_componentRoots j) hγj
    have hβΨ : β ∈ simpleRoots Ψ := by
      rw [← Finset.mem_coe, hΔ']
      exact ⟨j, hj, hβ⟩
    have hle : componentWeylGroup (componentRoots D.χ j) ≤ componentWeylGroup Ψ := by
      refine Subgroup.closure_mono ?_
      rintro _ ⟨β', hβ', rfl⟩
      exact ⟨β', by rw [hΔ']; exact ⟨j, hj, hβ'⟩, rfl⟩
    exact smul_mem_of_mem_componentWeylGroup hΨ (hle hw) β (simpleRoots_subset hβΨ)
  · intro γ hγ
    obtain ⟨w, hw, β, hβ, rfl⟩ := exists_smul_simpleRoot hΨ hγ
    have hβu : β ∈ unionSimpleRoots D.χ D.J := by
      rw [← hΔ']
      exact Finset.mem_coe.2 hβ
    have hw' : w ∈ unionWeylGroup D.χ D.J := by
      have hEq : componentWeylGroup Ψ = unionWeylGroup D.χ D.J := by
        simp only [componentWeylGroup, unionWeylGroup, hΔ']
      rwa [hEq] at hw
    exact smul_mem_unionRoots hw' (mem_unionRoots_of_mem_unionSimpleRoots hβu)

end CFSG.RankThree.Lattice.GenFixedRootDatum

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDExport
open scoped commutatorElement


variable {τ : Tag} {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L]

theorem exists_twoD_datum_fixed_roots (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ}
    (he : 1 ≤ e)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ componentRoots χ i, δ γ ∈ componentRoots χ i)
    (hpos : ∀ γ ∈ posRoots (componentRoots χ i), δ γ ∈ posRoots (componentRoots χ i))
    (hG : IsGraphTwist (componentRoots χ i) δ) {c : ModGL τ L}
    (hcT : c ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hcG : (adjointGroup τ L).map (MulAut.conj c).toMonoidHom = adjointGroup τ L)
    (hU : ∀ γ ∈ componentRoots χ i,
      (rootSubgroup τ L γ).map (frobTwistGL τ L r e c) = rootSubgroup τ L (δ γ))
    (hpin : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ A : SL2 L,
      frobTwistGL τ L r e c (rootSL2 τ L β A) =
        rootSL2 τ L (δ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A)) :
    ∃ D : GenFixedRootDatum τ r L (SpanQuot (componentRoots χ i)),
      D.e = e ∧
      D.roots = componentRoots χ i ∧
      D.simpleRootsJ = ((simpleRoots (componentRoots χ i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) ∧
      Group.IsPerfect D.orbitGroup ∧
      D.torusJ = rootSpan τ L (componentRoots χ i) ⊓ torusGroup τ L ∧
      D.fixedGroup.map (adjointGroup τ L).subtype =
        rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)) := by
  obtain ⟨D, hDe, hDΔ, hPerf, hDT, hDF⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.exists_twoD_datum_fixed
      hτ he i δ hiso hmaps hpos hG hcT hcG hU hpin
  exact ⟨D, hDe, D.roots_eq_of_simpleRootsJ_eq (isRootComponent_componentRoots i) hDΔ, hDΔ, hPerf,
    hDT, hDF⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

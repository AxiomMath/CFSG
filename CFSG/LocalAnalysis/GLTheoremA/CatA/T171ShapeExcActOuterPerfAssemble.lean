module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfGap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen
open scoped Pointwise commutatorElement


section Torus

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {M : Type} [CommGroup M]

theorem fixedTorus_le_orbitGroupC_of_cartan_det_four
    (D : CFSG.RankThree.Lattice.GenFixedRootDatum τ 2 L M)
    (Δ : Finset (Fin τ.rank → ℤ))
    (hΔ : (Δ : Set (Fin τ.rank → ℤ)) = D.simpleRootsJ)
    (hΔroot : ∀ β ∈ Δ, IsRoot τ β)
    (hdet : (Matrix.of fun β γ : Δ => corootPair (β : Fin τ.rank → ℤ) γ).det = 4)
    (hspan : ∀ γ ∈ D.roots, ∃ cc : (Fin τ.rank → ℤ) → ℤ,
      γ = ∑ β ∈ Δ, cc β • β)
    (hcenter : Subgroup.center (rootSpan τ L D.roots) = ⊥) :
    D.fixedTorus ≤ D.orbitGroupC :=
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.fixedTorus_le_orbitGroupC_of_coords
    D Δ hΔ
    (fun t ht =>
      exists_rootDiagUnit_coordTuple_of_mem_torusJ D Δ hΔ hΔroot hdet hspan hcenter ht)
    (fun c c' h => coordTuple_injective_of_det_four Δ hΔroot hdet h)

end Torus

section Assembly

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
  {i : KernelComponent (rootCharHom a)} {s : ℕ}

theorem twoDExcFixedPointsPerfect_of_datum
    {M : Type} [CommGroup M]
    (D : CFSG.RankThree.Lattice.GenFixedRootDatum τ 2 L M)
    (Δ : Finset (Fin τ.rank → ℤ))
    (hΔ : (Δ : Set (Fin τ.rank → ℤ)) = D.simpleRootsJ)
    (hΔroot : ∀ β ∈ Δ, IsRoot τ β)
    (hdet : (Matrix.of fun β γ : Δ => corootPair (β : Fin τ.rank → ℤ) γ).det = 4)
    (hspan : ∀ γ ∈ D.roots, ∃ cc : (Fin τ.rank → ℤ) → ℤ,
      γ = ∑ β ∈ Δ, cc β • β)
    (hcenter : Subgroup.center (rootSpan τ L D.roots) = ⊥)
    (z : ModGL τ L)
    (hHmap : (fixedPointSubgroup (iterHom S.D.step s)
        (rootSpan τ L (componentRoots (rootCharHom a) i))).map
          (MulAut.conj z⁻¹).toMonoidHom =
      D.fixedGroup.map (adjointGroup τ L).subtype)
    (hperf : Group.IsPerfect ↥D.orbitGroup) :
    TwoDExcFixedPointsPerfect S a i s :=
  CFSG.LocalAnalysis.GLTheoremA.T171Sh.twoDExcFixedPointsPerfect_of_fixedGroup_map
    (S := S) (i := i) (s := s) D z hHmap
    (fixedTorus_le_orbitGroupC_of_cartan_det_four D Δ hΔ hΔroot hdet hspan hcenter) hperf

@[expose] def TwoDExcFixedPointsDatum : Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ},
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (i : KernelComponent (rootCharHom a)),
      twistKind S.ρ (rootCharHom a) i = .twoD →
      ∃ (D : CFSG.RankThree.Lattice.GenFixedRootDatum τ 2 L
          (SpanQuot (componentRoots (rootCharHom a) i)))
        (Δ : Finset (Fin τ.rank → ℤ)) (z : ModGL τ L),
        Group.IsPerfect ↥D.orbitGroup ∧
        (Δ : Set (Fin τ.rank → ℤ)) = D.simpleRootsJ ∧
        (Matrix.of fun β γ : Δ => corootPair (β : Fin τ.rank → ℤ) γ).det = 4 ∧
        (∀ γ ∈ D.roots, ∃ cc : (Fin τ.rank → ℤ) → ℤ, γ = ∑ β ∈ Δ, cc β • β) ∧
        Subgroup.center (rootSpan τ L D.roots) = ⊥ ∧
        D.torusJ = rootSpan τ L D.roots ⊓ torusGroup τ L ∧
        (fixedPointSubgroup (iterHom S.D.step
            (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
          (rootSpan τ L (componentRoots (rootCharHom a) i))).map
            (MulAut.conj z⁻¹).toMonoidHom =
          D.fixedGroup.map (adjointGroup τ L).subtype

theorem twoDExcFixedPointsPerfect_holds_of_datum (h : TwoDExcFixedPointsDatum)
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .twoD) :
    TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  obtain ⟨D, Δ, z, hperf, hΔ, hdet, hspan, hcenter, -, hHmap⟩ := h S hT i hkind
  have hΔroot : ∀ β ∈ Δ, IsRoot τ β := by
    intro β hβ
    have hβJ : β ∈ D.simpleRootsJ := by rw [← hΔ]; exact hβ
    exact isRoot_of_mem_unionSimpleRoots hβJ.1
  exact twoDExcFixedPointsPerfect_of_datum S D Δ hΔ hΔroot hdet hspan hcenter z hHmap hperf

@[expose] def ExcRankFourTrialityPerfect : Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ},
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (i : KernelComponent (rootCharHom a)),
      twistKind S.ρ (rootCharHom a) i = .exc →
      compRank (componentRoots (rootCharHom a) i) = 4 →
      TwoDExcFixedPointsPerfect S a i
        (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))

theorem twoDExcFixedPointsPerfectAll_of_data (hTwoD : TwoDExcFixedPointsDatum)
    (hExc : ExcRankFourTrialityPerfect) : TwoDExcFixedPointsPerfectAll := by
  intro τ L _ _ _ p₀ S a hT i hkind
  rcases hkind with hk | ⟨hk, hr⟩
  · exact twoDExcFixedPointsPerfect_holds_of_datum hTwoD S hT i hk
  · exact hExc S hT i hk hr

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

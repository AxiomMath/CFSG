module

public import CFSG.RankThree.Lattice.SteinbergBIGenCells
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterFix
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀]
  [IsAlgClosed k] {M : Type} [CommGroup M]

theorem fixedGroup_eq_orbitGroupC_of_fixedTorus_le
    (D : GenFixedRootDatum τ p₀ k M) (h : D.fixedTorus ≤ D.orbitGroupC) :
    D.fixedGroup = D.orbitGroupC := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    change (g : adjointGroup τ k) ∈ (D.fixedGroup : Set (adjointGroup τ k)) at hg
    rw [D.coe_fixedGroup_eq_mul] at hg
    obtain ⟨t, ht, c, hc, rfl⟩ := hg
    exact D.orbitGroupC.mul_mem (h ht) hc
  · intro hg
    change (g : adjointGroup τ k) ∈ (D.fixedGroup : Set (adjointGroup τ k))
    rw [D.coe_fixedGroup_eq_mul]
    exact ⟨1, D.fixedTorus.one_mem, g, hg, by simp⟩

theorem fixedGroup_perfect_of_fixedTorus_le_orbitGroup
    (D : GenFixedRootDatum τ p₀ k M) (h : D.fixedTorus ≤ D.orbitGroupC)
    (hperf : Group.IsPerfect ↥D.orbitGroup) :
    Group.IsPerfect ↥D.fixedGroup := by
  have hGC : Group.IsPerfect ↥D.orbitGroupC := by
    let e : ↥D.orbitGroupC ≃* ↥D.orbitGroup :=
      Subgroup.subgroupOfEquivOfLe D.orbitGroup_le_adjointGroup
    haveI : Group.IsPerfect ↥D.orbitGroup := hperf
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rw [fixedGroup_eq_orbitGroupC_of_fixedTorus_le D h]
  exact hGC

end CFSG.RankThree.Lattice

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
open scoped Pointwise

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
  (i : KernelComponent (rootCharHom a)) {s : ℕ}

theorem twoDExcFixedPointsPerfect_of_fixedGroup_map
    {M : Type} [CommGroup M] (D : CFSG.RankThree.Lattice.GenFixedRootDatum τ 2 L M)
    (z : ModGL τ L)
    (hHmap : (fixedPointSubgroup (iterHom S.D.step s)
        (rootSpan τ L (componentRoots (rootCharHom a) i))).map
          (MulAut.conj z⁻¹).toMonoidHom =
      D.fixedGroup.map (adjointGroup τ L).subtype)
    (hFT : D.fixedTorus ≤ D.orbitGroupC)
    (hperf : Group.IsPerfect ↥D.orbitGroup) :
    TwoDExcFixedPointsPerfect S a i s := by
  have hperfFG : Group.IsPerfect ↥D.fixedGroup :=
    CFSG.RankThree.Lattice.fixedGroup_perfect_of_fixedTorus_le_orbitGroup D hFT hperf
  let e : ↥D.fixedGroup ≃* ↥(D.fixedGroup.map (adjointGroup τ L).subtype) :=
    Subgroup.equivMapOfInjective D.fixedGroup (adjointGroup τ L).subtype
      (adjointGroup τ L).subtype_injective
  have hperfMapD : Group.IsPerfect ↥(D.fixedGroup.map (adjointGroup τ L).subtype) := by
    haveI := hperfFG
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hperfHmap : Group.IsPerfect ↥((fixedPointSubgroup (iterHom S.D.step s)
      (rootSpan τ L (componentRoots (rootCharHom a) i))).map
        (MulAut.conj z⁻¹).toMonoidHom) := by
    rw [hHmap]
    exact hperfMapD
  have hcommMap : ⁅(fixedPointSubgroup (iterHom S.D.step s)
      (rootSpan τ L (componentRoots (rootCharHom a) i))).map
        (MulAut.conj z⁻¹).toMonoidHom,
      (fixedPointSubgroup (iterHom S.D.step s)
        (rootSpan τ L (componentRoots (rootCharHom a) i))).map
          (MulAut.conj z⁻¹).toMonoidHom⁆ =
      (fixedPointSubgroup (iterHom S.D.step s)
        (rootSpan τ L (componentRoots (rootCharHom a) i))).map
          (MulAut.conj z⁻¹).toMonoidHom :=
    Subgroup.isPerfect_iff.1 hperfHmap
  have hcomm : ⁅fixedPointSubgroup (iterHom S.D.step s)
      (rootSpan τ L (componentRoots (rootCharHom a) i)),
      fixedPointSubgroup (iterHom S.D.step s)
        (rootSpan τ L (componentRoots (rootCharHom a) i))⁆ =
      fixedPointSubgroup (iterHom S.D.step s)
        (rootSpan τ L (componentRoots (rootCharHom a) i)) := by
    apply Subgroup.map_injective (f := (MulAut.conj z⁻¹).toMonoidHom)
      (MulAut.conj z⁻¹).injective
    rw [Subgroup.map_commutator, hcommMap]
  exact Subgroup.isPerfect_iff.2 hcomm

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

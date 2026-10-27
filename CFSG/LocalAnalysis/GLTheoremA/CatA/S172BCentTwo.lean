module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentPlane
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentUni

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X
  CFSG.LocalAnalysis.ComponentInitial

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {R : QuadraticForm (ZMod 2) W}

theorem primaryMultiplicity_cyc3_eq {x : W ≃ₗ[ZMod 2] W} (hx : OddOrderIsometry R 3 x) {m : ℕ}
    (hdim : finrank (ZMod 2) W = 2 * m) (hfix : finrank (ZMod 2) (fixedSpace x) = 2) :
    primaryMultiplicity x.toLinearMap (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2)) =
      m - 1 := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have h1 := Submodule.finrank_add_eq_of_isCompl
    (CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.isCompl_fixedSpace_cyc3 hK hx)
  have h2 := CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.finrank_cyc3 (x := x) hK
  omega

theorem isQuasisimple_specialBlock_cyc3 {x : W ≃ₗ[ZMod 2] W} (hx : OddOrderIsometry R 3 x)
    (hm : 4 ≤ primaryMultiplicity x.toLinearMap (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2))) :
    CFSG.IsQuasisimple ↥(specialBlock R x (X ^ 2 + X + 1)) := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X])) :=
    ⟨CFSG.HardMathSupport.Timmesfeld.CrossChar.irreducible_cyc3 hK⟩
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.orth2_isQuasisimple_specialBlock_selfDual hx
    (Nat.odd_iff.2 rfl)
    (CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.cyc3_mem_primaryFactors hK (by omega))
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3_ne_X_sub_one _)
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.reciprocal_cyc3 _).symm hm

theorem isSolvable_orthDerived_of_finrank_two (hW : finrank (ZMod 2) W = 2) :
    Group.IsSolvable ↥(orthDerived R) := by
  haveI := isSolvable_linearEquiv_of_finrank_two hW
  exact Group.isSolvable_of_isSolvable_injective (f := (orthDerived R).subtype)
    (orthDerived R).subtype_injective

theorem not_isSolvable_of_isQuasisimple_aux {X : Type*} [Group X] (hX : CFSG.IsQuasisimple X) :
    ¬ Group.IsSolvable X := by
  intro hs
  haveI : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hX
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := X)).ne
    (@Group.IsPerfect.commutator_eq_top _ _ hX.1)

theorem layerIs_of_glaLayer_eq {G : Type} [Group G] {X D : Subgroup G} (hD : GLALayer X = D)
    (hc : IsComponentOf D X) {p : ℕ} {Qq : TauCeti.CFSGIndex → Prop}
    (h : catalogIs (PSimple p D) Qq) : LayerIs p X Qq := by
  subst hD
  exact ⟨hc, h⟩

private theorem oddOrderIsometry_three_of_orderOf_eq_three (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {x : ↥(orthDerived R)} (hx3 : orderOf x = 3) :
    OddOrderIsometry R 3 (x : W ≃ₗ[ZMod 2] W) := by
  have hx3' : (x : W ≃ₗ[ZMod 2] W) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx3] at this
    exact congrArg Subtype.val this
  exact oddOrderIsometry_three hR (orthDerived_le_orthogonalGroup x.2) hx3'

private theorem natCard_adjoinRoot_cyc3
    [Fact (Irreducible (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2)))] :
    Nat.card (AdjoinRoot (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2))) = 2 ^ 2 := by
  haveI : Finite (AdjoinRoot (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2))) :=
    finite_adjoinRoot_of_fact _
  have h1 : finrank (ZMod 2) (AdjoinRoot (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2))) =
      2 := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2))).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, CFSG.HardMathSupport.Timmesfeld.CrossChar.natDegree_cyc3]
  rw [← FiniteField.pow_finrank_eq_natCard 2, h1]

theorem exists_mulEquiv_specialBlock_sesqSpecialUnitary
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) {x : ↥(orthDerived R)} (hx3 : orderOf x = 3)
    [Fact (Irreducible (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2)))] {k : ℕ} (hk : 4 ≤ k)
    (hmult : primaryMultiplicity (x : W ≃ₗ[ZMod 2] W).toLinearMap
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2)) = k) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ f
        (AdjoinRoot (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2))))
      (B : primaryComponent (x : W ≃ₗ[ZMod 2] W).toLinearMap
          (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2)) →ₛₗ[hU.bar]
        primaryComponent (x : W ≃ₗ[ZMod 2] W).toLinearMap
          (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2)) →ₗ[AdjoinRoot
          (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2))]
        AdjoinRoot (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2))),
      ℓ ^ f = 2 ∧ B.IsSymm ∧ B.SeparatingLeft ∧
        Nonempty (↥((specialBlock R (x : W ≃ₗ[ZMod 2] W) (X ^ 2 + X + 1)).subgroupOf (orthDerived R)) ≃*
          ↥(sesqSpecialUnitaryGroup B)) := by
  have hx := oddOrderIsometry_three_of_orderOf_eq_three hR hx3
  have hh : CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2) ∈
      primaryFactors (x : W ≃ₗ[ZMod 2] W).toLinearMap :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.cyc3_mem_primaryFactors (by simp) (by omega)
  have hq := isQuasisimple_specialBlock_cyc3 hx (by omega)
  obtain ⟨d, ℓ, f, hU, B, -, -, hBs, hBl, hrange⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.orth2_exists_unitary_model hx (Nat.odd_iff.2 rfl) hh
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3_ne_X_sub_one _)
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.reciprocal_cyc3 _).symm
  have hleΩ : specialBlock R (x : W ≃ₗ[ZMod 2] W) (X ^ 2 + X + 1) ≤ orthDerived R :=
    specialBlock_le_orthDerived_of_perfect hq.1 fun g hg =>
      (Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer _ hg)).1
  refine ⟨ℓ, f * d, hU, B, ?_, hBs, hBl, ⟨?_⟩⟩
  · have hcard := hU.card
    rw [natCard_adjoinRoot_cyc3, pow_mul'] at hcard
    exact Nat.pow_left_injective (n := 2) (by norm_num) hcard.symm
  · exact (Subgroup.subgroupOfEquivOfLe hleΩ).trans
      ((MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange))

theorem catalogIs_pSimple_specialBlock_isUnA (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {x : ↥(orthDerived R)} (hx3 : orderOf x = 3) {k : ℕ} (hk : 4 ≤ k)
    (hmult : primaryMultiplicity (x : W ≃ₗ[ZMod 2] W).toLinearMap
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2)) = k) :
    catalogIs (PSimple 3 ((specialBlock R (x : W ≃ₗ[ZMod 2] W) (X ^ 2 + X + 1)).subgroupOf
      (orthDerived R))) (isUnA k 2) := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  haveI : Fact (Irreducible (CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2))) :=
    ⟨CFSG.HardMathSupport.Timmesfeld.CrossChar.irreducible_cyc3 hK⟩
  obtain ⟨ℓ, f, hU, B, hℓf, hBs, hBl, ⟨φ⟩⟩ :=
    exists_mulEquiv_specialBlock_sesqSpecialUnitary hR hx3 hk hmult
  exact (catalogIs_pSimple_congr_mulEquiv φ 3 _).2
    (catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA hU hℓf hBs hBl hk hmult)

private theorem eq_specialBlock_of_isComponentOf_centralizer (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {x : ↥(orthDerived R)} (hx3 : orderOf x = 3)
    (hfix : finrank (ZMod 2) (fixedSpace (x : W ≃ₗ[ZMod 2] W)) = 2)
    {L : Subgroup ↥(orthDerived R)}
    (hL : IsComponentOf L (Subgroup.centralizer ({x} : Set ↥(orthDerived R)))) :
    L = (specialBlock R (x : W ≃ₗ[ZMod 2] W) (X ^ 2 + X + 1)).subgroupOf (orthDerived R) := by
  have hx := oddOrderIsometry_three_of_orderOf_eq_three hR hx3
  rcases comp_cases_orthDerived hR hx3 hL with ⟨-, -, hLeq⟩ | ⟨F, hFq, hFle, -, -, hLeq⟩
  · exact hLeq
  · exfalso
    haveI := isSolvable_orthDerived_of_finrank_two
      (R := R.comp (fixedSpace (x : W ≃ₗ[ZMod 2] W)).subtype) hfix
    haveI : Group.IsSolvable ↥(supportedFixedDerived R (x : W ≃ₗ[ZMod 2] W)) :=
      Group.isSolvable_of_isSolvable_injective (f := (restrictDerivedEquiv hx).toMonoidHom)
        (restrictDerivedEquiv hx).injective
    haveI : Group.IsSolvable ↥F :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hFle)
        (Subgroup.inclusion_injective hFle)
    exact not_isSolvable_of_isQuasisimple_aux hFq inferInstance

theorem layerIs_centralizer_of_finrank_fixed_two (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {m : ℕ} (hm : 5 ≤ m) (hdim : finrank (ZMod 2) W = 2 * m) {x : ↥(orthDerived R)}
    (hx3 : orderOf x = 3) (hfix : finrank (ZMod 2) (fixedSpace (x : W ≃ₗ[ZMod 2] W)) = 2) :
    LayerIs 3 (Subgroup.centralizer ({x} : Set ↥(orthDerived R))) (isUnA (m - 1) 2) := by
  have hx := oddOrderIsometry_three_of_orderOf_eq_three hR hx3
  have hmult := primaryMultiplicity_cyc3_eq hx hdim hfix
  have hh : CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 (ZMod 2) ∈
      primaryFactors (x : W ≃ₗ[ZMod 2] W).toLinearMap :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.cyc3_mem_primaryFactors (by simp) (by omega)
  have hT := CFSG.StandardType.OrthRestOdd.exists_totallySingular_three R hR
    (by omega : 8 ≤ finrank (ZMod 2) W)
  have hq := isQuasisimple_specialBlock_cyc3 hx (by omega)
  have hSΩ : specialBlock R (x : W ≃ₗ[ZMod 2] W) (X ^ 2 + X + 1) ≤ orthDerived R :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.specialBlock_le_orthDerived (by simp) hx hR hT hh
  set S := specialBlock R (x : W ≃ₗ[ZMod 2] W) (X ^ 2 + X + 1) with hS
  set S' : Subgroup ↥(orthDerived R) := S.subgroupOf (orthDerived R) with hS'
  set C : Subgroup ↥(orthDerived R) := Subgroup.centralizer ({x} : Set ↥(orthDerived R)) with hC
  have hS'q : CFSG.IsQuasisimple ↥S' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSΩ).symm hq
  have hS'C : S' ≤ C := fun g hg =>
    mem_centralizer_of_mem_isometryCentralizer (specialBlock_le_isometryCentralizer _
      (Subgroup.mem_subgroupOf.1 hg))
  have hnorm : (S'.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hS'C]
    intro g n hg hn
    exact Subgroup.mem_subgroupOf.2 (conj_mem_specialBlock
      (mem_isometryCentralizer_of_mem_centralizer hn) (Subgroup.mem_subgroupOf.1 hg))
  have hcompS' : IsComponentOf S' C :=
    ⟨hS'C, IsSubnormal.step hS'C hnorm (IsSubnormal.refl C), open_isQuasisimple_of hS'q⟩
  have hcomp : ∀ L : Subgroup ↥(orthDerived R), IsComponentOf L C → L = S' := fun L hL =>
    eq_specialBlock_of_isComponentOf_centralizer hR hx3 hfix hL
  have hlayer : GLALayer C = S' := by
    have hset : {L | IsComponentOf L C} = {S'} :=
      Set.ext fun L => ⟨hcomp L, fun h => h ▸ hcompS'⟩
    show sSup {L | IsComponentOf L C} = S'
    rw [hset, sSup_singleton]
  exact layerIs_of_glaLayer_eq hlayer hcompS' (catalogIs_pSimple_specialBlock_isUnA hR hx3 (by omega) hmult)

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end

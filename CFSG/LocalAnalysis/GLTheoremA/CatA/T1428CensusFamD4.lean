module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamD4Comps

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

set_option linter.unusedSectionVars false


theorem censusBodyD4Graph : CensusBodyD4Graph := by
  intro q hv hq2 η hmem hη3 hinn r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  classical
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFcard : Nat.card F = 2 ^ q.exponent := by
    change Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 2 ^ q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_D, TauCeti.LieTypeIndex.fieldExponent_D, hq2]
  let ε : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group ≃* adjointGroup Tag.D4 F :=
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv).trans
      (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F).some
  let β : MulAut (adjointGroup Tag.D4 F) := MulAut.congr ε η
  have hβmem : β ∈ innAutDerived (adjointGroup Tag.D4 F) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr ε).2 hmem
  have hβ3 : β ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr ε) η 3
    rw [hη3, map_one] at h3
    exact h3.symm
  rcases CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_D4_three_cases hβmem hβ3
    with ⟨h, hβeq⟩ | ⟨g, a, ε', hε', hβeq⟩
  ·
    refine hinn (ε.symm h) ?_
    apply (MulAut.congr ε).injective
    show MulAut.congr ε (MulAut.conj (ε.symm h)) = β
    rw [hβeq]
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply, map_mul]
  · obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv
        (ℓ := 2) (f := q.exponent) q.exponent_pos F hFcard β hβ3 g a hε' hβeq
    have hC := compsWith_notL2_triality_outer q.exponent_pos hr hK₃ Fr hFr φ hφ3 hφout
    have hβ' : CompsWith (NotL2 r) ↥(fixSubgroup β) :=
      CompsWith.of_mulEquiv (isComponentProperty_notL2 r) e hC
    have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup ε η
    have hJ' : CFSG.Open.IsComponentOf (J₁.map ε.toMonoidHom) (fixSubgroup β) := by
      have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ε hJ₁
      exact hfix ▸ h1
    have hJ'' : CFSG.Open.IsComponentOf
        ((J₁.map ε.toMonoidHom).subgroupOf (fixSubgroup β)) ⊤ :=
      (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hJ'.1).1 hJ'
    have hN : NotL2 r ↥(J₁.map ε.toMonoidHom) :=
      (isComponentProperty_notL2 r).of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ'.1)
        (hβ' _ hJ'')
    have hN' : NotL2 r ↥J₁ :=
      (isComponentProperty_notL2 r).of_mulEquiv
        (J₁.equivMapOfInjective ε.toMonoidHom ε.injective).symm hN
    exact (show ¬ catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r) from hN') hL1

end CFSG.LocalAnalysis.GLTheoremA.T1428

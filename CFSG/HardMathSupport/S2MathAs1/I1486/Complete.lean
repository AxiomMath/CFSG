module

public import CFSG.HardMathSupport.S2MathAs1.I1486.Geometry
public import CFSG.HardMathSupport.S2MathAs1.I1486.BroadAction
public import CFSG.HardMathSupport.S2MathAs1.I1486.Assembly

public section

namespace CFSG.HardMathSupport.S2MathAs1.I1486

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.GroupActions
open CFSG.StandardType CFSG.StandardType.KGA

theorem ggF4GeomCoreInput_holds
    : GGF4GeomCoreInput := by
  intro p₀ p f L hL hAlg hChar S a hp hp2
  intro hSq hT hap h1 hTame i hqs hlab y hy
  have hyM : y ∈ S.D.model := (Subgroup.commutator_le_self S.D.model) hy.1
  have hyM' := S.D.mem_model.1 hyM
  have hyAdj : y ∈ adjointGroup Tag.F4 L := hyM'.1
  have hyF : S.D.step y = y := by
    simpa [LangDatum.step, MulAut.conj_apply] using hyM'.2
  have hyTC : y ∈ toralCentralizer Tag.F4 L a := by
    rw [mem_toralCentralizer]
    exact ⟨hyAdj, conj_eq_iff_mem_centralizer.2 hy.2⟩
  have hyZ : y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (kernelRoots (rootCharHom a)) :=
    f4_toral_centralizer_le_rootGroup hp hp2 hap h1 hyTC
  have hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    conj_mem_subgroupStabAut_rationalComponent S hT i hyZ hyF
  have hf : 1 ≤ f :=
    (CFSG.StandardType.KG.kg_inLambda2_C
      (X := ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      (by omega) hlab).1
  exact f4_rational_C3_inner_action hp hp2 S hT hap h1 i hqs hf hlab y hyZ hyF hyStab

theorem ggF4CoreInput_holds
    : CFSG.StandardType.KGA.GGF4CoreInput :=
  ggF4CoreInput_of_geom ggF4GeomCoreInput_holds

end CFSG.HardMathSupport.S2MathAs1.I1486

end

module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverLift
public import CFSG.LieType.Steinberg.Minuscule.RankOne
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.Quasithin.Background.SmithCurtisBasic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

abbrev N6 := Fin (Tag.rank .E6)


variable {K : Type} [Field K]

theorem slHom_mem (s : N6) (M : SL(2, K)) : e6Data_valid.slHom K s M ∈ e6Data_valid.minGroup K := by
  have hcl := CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)
  have hM : M ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) := by
    rw [hcl]; exact Subgroup.mem_top M
  induction hM using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have e : e6Data_valid.slHom K s (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c) =
          e6Data_valid.xu K (Pi.single s 1) c := by
        refine Units.ext ?_
        rw [MinData.Valid.slHom_val]
        exact e6Data_valid.blockOp_upper K s c
      rw [e]; exact e6Data_valid.xu_mem K _ c
    · have e : e6Data_valid.slHom K s (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c) =
          e6Data_valid.xu K (-Pi.single s 1) c := by
        refine Units.ext ?_
        rw [MinData.Valid.slHom_val]
        exact e6Data_valid.blockOp_lower K s c
      rw [e]; exact e6Data_valid.xu_mem K _ c
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

variable (K) in
@[expose] def rankOne6 (s : N6) : SL(2, K) →* ↥(e6Data_valid.minGroup K) :=
  (e6Data_valid.slHom K s).codRestrict (e6Data_valid.minGroup K) (slHom_mem s)

theorem rankOne6_u (s : N6) (c : K) :
    rankOne6 K s (uElt c) = e6Data_valid.xm K (Pi.single s 1) c := by
  refine Subtype.ext (Units.ext ?_)
  show (e6Data_valid.slHom K s (uElt c) : Module.End K (Fin e6Data.d →₀ K)) = _
  rw [MinData.Valid.slHom_val]
  exact e6Data_valid.blockOp_upper K s c

theorem rankOne6_l (s : N6) (c : K) :
    rankOne6 K s (lElt c) = e6Data_valid.xm K (-Pi.single s 1) c := by
  refine Subtype.ext (Units.ext ?_)
  show (e6Data_valid.slHom K s (lElt c) : Module.End K (Fin e6Data.d →₀ K)) = _
  rw [MinData.Valid.slHom_val]
  exact e6Data_valid.blockOp_lower K s c

theorem rankOne6_d (s : N6) (z : Kˣ) :
    rankOne6 K s (dElt z) = e6Data_valid.hm K s z := by
  refine Subtype.ext (Units.ext ?_)
  show (e6Data_valid.slHom K s (dElt z) : Module.End K (Fin e6Data.d →₀ K)) = _
  rw [MinData.Valid.slHom_val]
  exact (e6Data_valid.blockOp_diag K s z).trans (e6Data_valid.endo_hm K s z).symm

theorem rankOne6_w (s : N6) : rankOne6 K s WSL = e6Data_valid.nm K s := by
  refine Subtype.ext (Units.ext ?_)
  show (e6Data_valid.slHom K s WSL : Module.End K (Fin e6Data.d →₀ K)) = _
  rw [MinData.Valid.slHom_val]
  exact (e6Data_valid.blockOp_weyl K s).trans (e6Data_valid.endo_nm K s).symm

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Easy
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4IStr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4ICyc
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4IRig

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kaSp4I_thm : KASp4I := by
  intro F _ _ hodd h5 a ha
  have hθα : ∀ g, alphaI ha (proj 2 F g) = proj 2 F (conjSp 2 F (aIgsp ha) g) :=
    fun g => conjAut_proj (aIgsp ha) g
  obtain ⟨hLR₀, hLn, hLperf, hLp⟩ := kaSp4I_struct hodd h5 ha
  refine ka_all_of_torus (ka_conj_inj_psp4 hodd) ((fixI a ha).map (proj 2 F)) (JI ha) ?_ ?_ hLR₀
    hLn hLperf hLp (kaSp4I_hcyc hodd h5 ha) (kaSp4I_rigid hodd ha)
    (ka_outCentral_psp4 hodd (alphaI ha))
  · exact map_fixOf_le (conjSp 2 F (aIgsp ha)) hθα
  · intro c hc ho
    exact ka_odd_mem_map_fixOf (conjSp 2 F (aIgsp ha)) (alphaI ha) hθα hc ho

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

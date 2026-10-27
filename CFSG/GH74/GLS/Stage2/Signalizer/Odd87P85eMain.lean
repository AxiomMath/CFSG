module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eNo
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eKinds
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eCfgK
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

namespace P85

theorem no_u34cfg {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (hctx : Stage2Ctx G z k S) {P : Subgroup G} {w : G} (h : U34Cfg P w) : False := by
  cases hctx.data with
  | g2 hg =>
    exact no_u34cfg_pair hctx.orderOf_z hctx.sylow_top hctx.S_le_Cen (lpairCtx_g2 hctx) h
  | m12 hm =>
    exact no_u34cfg_m12 hctx.z_mem hctx.sylow_top hctx.S_le_Cen hm h
  | psp4 hp =>
    exact no_u34cfg_pair hctx.orderOf_z hctx.sylow_top hctx.S_le_Cen (lpairCtx_psp4 hctx) h
  | l4 ε hl =>
    exact no_u34cfg_pair hctx.orderOf_z hctx.sylow_top hctx.S_le_Cen (lpairCtx_l4 ε hctx) h
  | mcl hm =>
    obtain ⟨n, hn, hsp⟩ := hm
    exact no_u34cfg_sporadic (by omega) hctx.orderOf_z hsp.cover hsp.one_class h
  | ly hm =>
    obtain ⟨n, hn, hsp⟩ := hm
    exact no_u34cfg_sporadic (by omega) hctx.orderOf_z hsp.cover hsp.one_class h

end P85

theorem prop85e_thm : Prop85e := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hhyp hU
  have hZ : IsPGroup 2 ↥(center ↥(layer (Sec H₀ H₁))) := by
    rw [hhyp.2.2.1]
    exact CFSG.pCore_isPGroup
  obtain ⟨P, w, hcfg⟩ := P85.u34cfg_of_section H₁ hsig.odd hZ hU
  exact P85.no_u34cfg hctx hcfg

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

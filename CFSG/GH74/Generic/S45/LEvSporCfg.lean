module

public import CFSG.GH74.GLS.C3.Layer1.EvenSpor
public import CFSG.GH74.Generic.S45.LEvSporAut

public section

open Subgroup CFSG CFSG.ABGLocalTools

namespace CFSG.GH74.GLS

theorem SporAutCfg.cfgData {G : Type} [Group G] [Finite G] {N H K Q : Subgroup G} {x : G}
    (cfg : SporAutCfg N H K Q x) : ∃ E : Subgroup G, Generic.S45.CfgData N H K Q E x := by
  obtain ⟨E, hEQ, hEa, hE4⟩ := Generic.S45.exists_elemAb_of_two_le_pRank cfg.rankQ
  exact ⟨E, cfg.socle.le, cfg.socle.normal, cfg.index_two, cfg.hKH, cfg.K5, cfg.sylowQ.le,
    cfg.sylowQ, hEQ, hEa, hE4, cfg.hxQ, cfg.hx2,
    fun k hk => mem_centralizer_singleton_iff.1 (cfg.comp.1 hk).1⟩

end CFSG.GH74.GLS

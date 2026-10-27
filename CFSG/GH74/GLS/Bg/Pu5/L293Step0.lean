module

public import CFSG.GH74.GLS.Bg.Pu5.ZStruct

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Cfg.z_mem_zStar {z t : G} {S : Subgroup G} (hC : Cfg G z t S) :
    z ∈ zStar (rigidProduct z) :=
  self_mem_zStar_rigidProduct hC.hzK

theorem Cfg.t_mem_rigidProduct {z t : G} {S : Subgroup G} (hC : Cfg G z t S) :
    t ∈ rigidProduct t := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hC.conj
  have h := mem_rigidProduct_conj hC.hzK c
  rwa [hc] at h

theorem Cfg.t_orderOf {z t : G} {S : Subgroup G} (hC : Cfg G z t S) : orderOf t = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hC.conj
  rw [← hc, orderOf_conj_eq', hC.hz]

theorem Cfg.z_mem_centralizer_t {z t : G} {S : Subgroup G} (hC : Cfg G z t S) :
    z ∈ centralizer ({t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hC.tC).symm

theorem step0 (hLP : L292LP) (hTP : L292TP) (h44 : II4_44) (hquat : II4_4_quat) {z t : G}
    {S : Subgroup G} (hC : Cfg G z t S) {w : G} (hw : orderOf w = 2)
    (hwz : w ∈ centralizer ({z} : Set G)) (hwt : w ∈ centralizer ({t} : Set G))
    (hK : ∀ K, IsRigidRankOneComp z K → w ∈ cSec K)
    (hL : ∀ L, IsRigidRankOneComp t L → w ∈ cSec L) : False := by
  have hzw : z ∈ centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hwz).symm
  have hz_w : z ∈ zStar (rigidProduct w) :=
    lpFull hLP h44 hquat hC.simple hC.gen4 hC.rank hw hwz hK hC.z_mem_zStar
      (exists_two_pow_eq_one_of_orderOf hC.hz) hzw
  have hzL : ∀ L, IsRigidRankOneComp t L → z ∈ cSec L := fun L hL' =>
    hTP G hC.simple hC.rank t w L hL' hw hwt (hL L hL') z hC.hz hC.z_mem_centralizer_t hzw hz_w
  have ht_z : t ∈ zStar (rigidProduct z) :=
    lpFull hLP h44 hquat hC.simple hC.gen4 hC.rank hC.hz hC.z_mem_centralizer_t hzL
      (self_mem_zStar_rigidProduct hC.t_mem_rigidProduct)
      (exists_two_pow_eq_one_of_orderOf hC.t_orderOf) hC.tC
  exact hC.tZ ht_z

end CFSG.GH74.GLS.Bg.Pu5

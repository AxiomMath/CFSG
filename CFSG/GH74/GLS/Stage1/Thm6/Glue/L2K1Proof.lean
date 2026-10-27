module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2K1Std
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2K1C3
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2TNormal
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Facts
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.K1Proof

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G]

theorem iv3K1Leaf_of_ivk (hIVK : IVKL2Facts) (x : G) (Kb : Subgroup (CentralizerBar x)) :
    IV3K1Leaf x Kb := by
  intro c _ F _ _ e N S hS hsit
  have hx2 : x * x = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [c.x_order])
  have hx1 : x ≠ 1 := fun h => by
    have := c.x_order
    rw [h, orderOf_one] at this
    omega
  have hrk : Rank2Le (Cx x) 3 := rank2Le_of_pRank_le x c.rankC.le
  have hb := hbase_of_sit hsit c.simple c.nonabelian hx2 hx1 hS rfl c.rankC c.not_solvable
  have hP4 := ip_P_four hsit hIVK.h12c
  obtain ⟨z, hz⟩ := hb.exists_HZ hP4
  intro hS2
  have hTS : S ⊓ Cx x ≠ S := by
    intro hh
    rw [hh, Subgroup.relIndex_self] at hS2
    omega
  have hout := ip_outer hsit hIVK.h12hc hIVK.h14a hx2 hx1
  have hcf := ip_cent_four hsit hIVK.h13fa hIVK.h13fb
  have h127 := after_12_7 Sec12.ig_15_3 Sec12.ig_16_2 hb hz hout hcf hP4
    (ip_Rd_factor hsit hIVK.h12a hIVK.h12d) (ip_P_conj hsit hIVK.h12g hz)
    (ip_P_trans hsit hIVK.h12c hIVK.h12d) (ip_cent_Rd hsit hIVK.h12c hIVK.h14j)
    (ip_cent_P_exp hsit hIVK.h12c hIVK.h14j) hTS
  exact k1_of_facts hb hz h127 (ip_f3 hsit hIVK.h13fc) (ip_z_V hsit hIVK.h12c hz) hout hcf
    (ip_P_closed x Kb _) (ip_Rd_dihedral hsit h127.Q_eq hIVK.h12c hIVK.h12d)
    (ip_Rd_fuse hsit h127.Q_eq hrk hx2 hx1 hIVK.h12c hIVK.h12d hIVK.h13fa)
    (ipTNormalLeaf_of_ivk hIVK x Kb c e N _ hsit z hz h127.Q_eq h127.omega1_le) hS2

theorem iv3K1LeafStd_of_ivk (hIVK : IVKL2Facts) : IV3K1LeafStd :=
  fun _ _ _ _ _ x Kb => iv3K1Leaf_of_ivk hIVK x Kb

theorem iv3K1LeafC3_of_ivk (hIVK : IVKL2Facts) : IV3K1LeafC3 :=
  fun _ _ _ _ x Kb => iv3K1Leaf_of_ivk hIVK x Kb

theorem iv3K1LeafStd_proved :
    IV3K1LeafStd :=
  iv3K1LeafStd_of_ivk (ivkL2Facts_of_proved IVK.ivk_1_2_general IVK.ivk_1_3f_c)

theorem iv3K1LeafC3_proved :
    IV3K1LeafC3 :=
  iv3K1LeafC3_of_ivk (ivkL2Facts_of_proved IVK.ivk_1_2_general IVK.ivk_1_3f_c)

end CFSG.GH74.GLS.Stage1.Thm6.Glue

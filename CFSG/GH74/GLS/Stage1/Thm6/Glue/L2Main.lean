module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Cond
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Factor
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Rank
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.K1Basic
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Conf
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.KFacts
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Outer
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9
public import CFSG.GH74.GLS.Stage1.Thm6.Setup
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

structure IVKL2Facts : Prop where
  gen : IVK.IVK_1_2_general
  h12a : IVK.IVK_1_2a_struct
  h12c : IVK.IVK_1_2c
  h12d : IVK.IVK_1_2d
  h12e : IVK.IVK_1_2e
  h12f : IVK.IVK_1_2f
  h12g : IVK.IVK_1_2g
  h12hc : IVK.IVK_1_2h_c
  h13fa : IVK.IVK_1_3f_a
  h13fb : IVK.IVK_1_3f_b
  h13fc : IVK.IVK_1_3f_c
  h14a : IVK.IVK_1_4a
  h14j : IVK.IVK_1_4j

variable {G : Type} [Group G] [Finite G] {x : G}

@[expose] def IPTNormalLeaf (x : G) (Kb : Subgroup (CentralizerBar x)) : Prop :=
  Conf12B G x Kb → ∀ [Kb.Normal] {F : Type} [Field F] [Finite F] (e : ↥Kb ≃* IVK.L2 F)
    (N : IVK.L2Notation e)
    (T : Subgroup G), SitFacts x Kb e N T → ∀ z : G, HZ T (Pg x Kb T) z →
      Qg x Kb T = Subgroup.zpowers x → omega1 T ≤ Rdg x Kb e T →
      IP_T_normal x z T (Pg x Kb T) (Rdg x Kb e T)

section Hbase

variable {Kb : Subgroup (CentralizerBar x)} [Kb.Normal] {F : Type} [Field F] [Finite F]
  {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

theorem hbase_of_sit (h : SitFacts x Kb e N T) {S : Subgroup G} (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hx : x * x = 1) (hx1 : x ≠ 1) (hS : IsSylow2In S ⊤)
    (hTS : T = S ⊓ Cx x) (hrank : pRank 2 ↥(Cx x) = 3)
    (hns : ¬ Group.IsSolvable ↥(Cx x)) :
    HBase G x S T (Pg x Kb T) (Qg x Kb T) (Rdg x Kb e T) (Qg x Kb T) where
  simple := hsimple
  nonabelian := hnonab
  x_sq := hx
  x_ne_one := hx1
  S_sylow := hS
  T_sylow := h.sylow
  T_le_S := hTS ▸ inf_le_left
  extremal := fun s hs hsx => by
    rw [hTS]
    exact ⟨hs, (mem_Cx x).2 hsx⟩
  rank_le := rank2Le_of_pRank_le x hrank.le
  rank_ge := exists_elemAb_eight x hrank
  P_normal := Pg_normal x Kb h.T_le_C
  Q_normal := Qg_normal x Kb h.T_le_C
  Rd_normal := h.Rd_normal
  PQ_disjoint := Pg_inf_Qg x Kb (IVK.conj_injective_of_L2 e) h.sylow
  PQ_comm := Pg_comm_Qg x Kb h.sylow
  x_mem_Q := h.x_mem_Q hx hx1
  R_le_Rd := SitFacts.PQ_le_Rd
  R_index_le_two := h.relIndex_PQ_Rd_le
  F_le_T := fun g hg => hg.1
  Q_le_F := le_rfl
  F_inf_Rd := inf_eq_left.2 SitFacts.Qg_le_Rd
  nonsolv := hns

end Hbase

@[expose] def IV3SylowLeaf (x : G) (Kb : Subgroup (CentralizerBar x)) : Prop :=
  Conf12B G x Kb → ∀ [Kb.Normal] {F : Type} [Field F] [Finite F] (e : ↥Kb ≃* IVK.L2 F)
    (N : IVK.L2Notation e) (S : Subgroup G), IsSylow2In S ⊤ → SitFacts x Kb e N (S ⊓ Cx x) →
      IV3_12_8c_sylow_nn x S (S ⊓ Cx x) (Pg x Kb (S ⊓ Cx x))

theorem exists_sit_L2 (hIVK : IVKL2Facts) {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
    (c : Conf12B G x Kb) (hm : IsL2Model ↥Kb) :
    ∃ (S U : Subgroup G), IsSylow2In S ⊤ ∧ IsFour U ∧ NormalIn U S ∧ U ≤ Cx x ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : ↥Kb ≃* IVK.L2 F) (N : IVK.L2Notation e),
        SitFacts x Kb e N (S ⊓ Cx x) := by
  obtain ⟨F, _, _, hF, ⟨e0⟩⟩ := hm
  have hx2 : x * x = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [c.x_order])
  have hx1 : x ≠ 1 := fun h => by
    have := c.x_order
    rw [h, orderOf_one] at this
    omega
  obtain ⟨S, hS, hxS, hTsyl, U, hU, hUn, hUC⟩ :=
    exists_setup c.simple c.nonabelian hx2 hx1 (exists_elemAb_eight x c.rankC)
  obtain ⟨e, N, hsit⟩ := sitFacts_of_general x Kb hIVK.gen hF e0 hTsyl
  exact ⟨S, U, hS, hU, hUn, hUC, F, inferInstance, inferInstance, e, N, hsit⟩

theorem kfacts_of_sit (hIVK : IVKL2Facts) {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
    (c : Conf12B G x Kb) {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F}
    {N : IVK.L2Notation e} {S U : Subgroup G} (hS : IsSylow2In S ⊤) (hU : IsFour U)
    (hUn : NormalIn U S) (hUC : U ≤ Cx x) (hsit : SitFacts x Kb e N (S ⊓ Cx x))
    (hTn : IPTNormalLeaf x Kb) :
    KFacts x S (S ⊓ Cx x) (Pg x Kb (S ⊓ Cx x)) (Qg x Kb (S ⊓ Cx x)) (Rdg x Kb e (S ⊓ Cx x))
      (Qg x Kb (S ⊓ Cx x)) U := by
  have hx2 : x * x = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [c.x_order])
  have hx1 : x ≠ 1 := fun h => by
    have := c.x_order
    rw [h, orderOf_one] at this
    omega
  have hrk : Rank2Le (Cx x) 3 := rank2Le_of_pRank_le x c.rankC.le
  exact
    { base := hbase_of_sit hsit c.simple c.nonabelian hx2 hx1 hS rfl c.rankC c.not_solvable
      hu := ⟨hU, hUn, fun u hu => ⟨hUn.1 hu, hUC hu⟩⟩
      P_four := ip_P_four hsit hIVK.h12c
      outer := ip_outer hsit hIVK.h12hc hIVK.h14a hx2 hx1
      cent_four := ip_cent_four hsit hIVK.h13fa hIVK.h13fb
      Rd_factor := ip_Rd_factor hsit hIVK.h12a hIVK.h12d
      Rd_cyclic := ip_Rd_cyclic hsit hIVK.h12e
      P_trans := ip_P_trans hsit hIVK.h12c hIVK.h12d
      cent_Rd := ip_cent_Rd hsit hIVK.h12c hIVK.h14j
      cent_P_exp := ip_cent_P_exp hsit hIVK.h12c hIVK.h14j
      f3 := ip_f3 hsit hIVK.h13fc
      P_closed := ip_P_closed x Kb _
      P_conj := fun z hz => ip_P_conj hsit hIVK.h12g hz
      z_V := fun z hz => ip_z_V hsit hIVK.h12c hz
      E8_two := fun hQ hΩ => ip_E8_two hsit hQ hΩ hrk hx2 hx1 hIVK.h12c hIVK.h12d
      Rd_dihedral := fun hQ => ip_Rd_dihedral hsit hQ hIVK.h12c hIVK.h12d
      Rd_fuse := fun hQ => ip_Rd_fuse hsit hQ hrk hx2 hx1 hIVK.h12c hIVK.h12d hIVK.h13fa
      T_normal := fun z hz hQ hΩ => hTn c e N _ hsit z hz hQ hΩ }

end CFSG.GH74.GLS.Stage1.Thm6.Glue

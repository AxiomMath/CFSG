module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AI
public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnCfg

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem y6f4a_cData_of_gData {g t : G} {P M : Subgroup G} (hd : Y6GData g t P M) :
    Y6CData (y6f4aG g) (y6f4aT g t hd.comm) (P.subgroupOf (centralizer ({g} : Set G)))
      (M.subgroupOf (centralizer ({g} : Set G))) := by
  have hPC : P ≤ centralizer ({g} : Set G) :=
    (le_sup_left.trans (ge_of_eq hd.D_eq)).trans inf_le_left
  have hMC : M ≤ centralizer ({g} : Set G) := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hd.M_cent m hm).symm
  have hCl : Subgroup.closure ({g, t} : Set G) ≤ centralizer ({g} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hd.comm.symm
  have hcl : (Subgroup.closure ({g, t} : Set G)).subgroupOf (centralizer ({g} : Set G)) =
      Subgroup.closure ({(y6f4aG g), (y6f4aT g t hd.comm)} :
        Set ↥(centralizer ({g} : Set G))) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (centralizer ({g} : Set G)))
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCl, MonoidHom.map_closure]
    congr 1
    rw [Set.image_pair]
    rfl
  have hmap : (Subgroup.closure ({(y6f4aG g), (y6f4aT g t hd.comm)} :
        Set ↥(centralizer ({g} : Set G)))).map (centralizer ({g} : Set G)).subtype =
      Subgroup.closure ({g, t} : Set G) := by
    rw [← hcl, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCl]
  have hcent : Subgroup.centralizer ({(y6f4aT g t hd.comm)} :
        Set ↥(centralizer ({g} : Set G))) =
      (Subgroup.centralizer ({t} : Set G)).subgroupOf (centralizer ({g} : Set G)) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
    rfl
  refine
    { g_central := ?_
      g_order := ?_
      t_order := ?_
      t_ne_g := ?_
      no_conj := ?_
      D_eq := ?_
      P_inf := ?_
      P_equiv := ?_
      P_four := ?_
      M_equiv := ?_
      M_inv := ?_
      g_not_mem_M := ?_ }
  · rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.2
  · rw [← Subgroup.orderOf_coe (y6f4aG g)]
    exact hd.g_order
  · rw [← Subgroup.orderOf_coe (y6f4aT g t hd.comm)]
    exact hd.t_order
  · intro h
    exact hd.t_ne_g (Subtype.ext_iff.mp h)
  · intro x h
    exact hd.no_conj (x : G) x.2 (Subtype.ext_iff.mp h)
  · rw [hcent, ← Subgroup.inf_subgroupOf_left, hd.D_eq,
      Subgroup.subgroupOf_sup hPC hCl, hcl]
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxP, hxcl⟩ := hx
    rw [Subgroup.mem_bot]
    have hxG : (x : G) ∈ P ⊓ Subgroup.closure ({g, t} : Set G) :=
      ⟨hxP, hmap ▸ Subgroup.mem_map.mpr ⟨x, hxcl, rfl⟩⟩
    rw [hd.P_inf, Subgroup.mem_bot] at hxG
    exact Subtype.ext hxG
  · obtain ⟨e⟩ := hd.P_equiv
    exact ⟨(Subgroup.subgroupOfEquivOfLe hPC).trans e⟩
  · intro p hp h4
    exact Subtype.ext (hd.P_four (p : G) hp (congrArg Subtype.val h4))
  · obtain ⟨e⟩ := hd.M_equiv
    exact ⟨(Subgroup.subgroupOfEquivOfLe hMC).trans e⟩
  · intro m hm
    exact Subtype.ext (hd.M_inv (m : G) hm)
  · intro h
    exact hd.g_not_mem_M h

theorem y6f4a_centralizer_ne_top [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {g : G}
    (hg : g ≠ 1) : centralizer ({g} : Set G) ≠ ⊤ := by
  intro htop
  have hct : Subgroup.center G ≠ ⊤ := by
    intro hc
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp hc)) a b)
  have hcb : Subgroup.center G = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_right hct
  have hgmem : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : x ∈ centralizer ({g} : Set G) := by rw [htop]; exact Subgroup.mem_top x
    exact Subgroup.mem_centralizer_singleton_iff.mp hx
  rw [hcb] at hgmem
  exact hg (Subgroup.mem_bot.mp hgmem)

theorem y6f4a_isKGroupCat_Y [Finite G] (hK : CFSG.Assembly.KProper Catalog G) {g : G}
    (hne : centralizer ({g} : Set G) ≠ ⊤) :
    CFSG.SectionRank.IsKGroupCat (↥(centralizer ({g} : Set G)) ⧸ zpowers (y6f4aG g)) := by
  exact CFSG.LocalAnalysis.EvenBN.GMSK.isKGroupCat_of_section_of_kProper hK hne
    (zpowers (y6f4aG g))

theorem y6f4a_oddCore_Y [Finite G] {g : G} (hg : orderOf g = 2)
    (hbal : CFSG.Open.standardComponentOddCore ↥(centralizer ({g} : Set G)) = ⊥) :
    CFSG.Open.standardComponentOddCore
      (↥(centralizer ({g} : Set G)) ⧸ zpowers (y6f4aG g)) = ⊥ := by
  rw [CFSG.LocalAnalysis.EvenBN.GMSK.standardComponentOddCore_eq_pPrimeCore] at hbal
  rw [CFSG.LocalAnalysis.EvenBN.GMSK.standardComponentOddCore_eq_pPrimeCore]
  refine CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn.pPrimeCore_quot_eq_bot ?_ ?_ ?_ hbal
  · have hzord : orderOf (y6f4aG g : ↥(centralizer ({g} : Set G))) = 2 := by
      rw [← Subgroup.orderOf_coe (y6f4aG g)]
      exact hg
    rw [← pow_two, ← hzord]
    exact pow_orderOf_eq_one _
  · have hg1 : g ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hg
      exact absurd hg (by norm_num)
    intro h
    exact hg1 (Subtype.ext_iff.mp h)
  · intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.2

end CFSG.OddStandard.HigherRank.YamadaG23

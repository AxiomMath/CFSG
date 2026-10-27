module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410
import CFSG.GroupTheory.AschbacherBlockMap
import CFSG.GroupTheory.SubnormalSupNormal
import CFSG.CGT.PushingUpLit.SubnormalTwoGroup
import CFSG.RankThree.S4Free.StellmacherW
public import CFSG.GroupTheory.SylowIntersectionControl.CharPair

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open scoped Pointwise

variable {Ω : Type} [Group Ω]

private theorem omegaOneCenterIn_eq_omegaOneCenterOf_l410 {K : Type} [Group K] (X : Subgroup K) :
    omegaOneCenterIn X = omegaOneCenterOf X := by
  unfold omegaOneCenterIn omegaOneCenterOf centerOf
  rw [CFSG.center_map_subtype_eq_inf_centralizer X]
  rfl

private theorem map_omegaOneCenterIn_l410 {K L : Type} [Group K] [Group L] (f : K →* L)
    (hf : Function.Injective f) (T : Subgroup K) :
    (omegaOneCenterIn T).map f = omegaOneCenterIn (T.map f) := by
  rw [omegaOneCenterIn_eq_omegaOneCenterOf_l410,
    omegaOneCenterIn_eq_omegaOneCenterOf_l410,
    CFSG.RankThree.S4Free.omegaOneCenterOf_map_of_injective' hf T]

private theorem map_subgroupOfEquiv_symm_eq_l410 {H G : Subgroup Ω} (hHG : H ≤ G)
    (B₀ : Subgroup ↥H) :
    B₀.map (Subgroup.subgroupOfEquivOfLe hHG).symm.toMonoidHom =
      (B₀.map (Subgroup.inclusion hHG)).subgroupOf (H.subgroupOf G) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, hbx⟩
    exact ⟨b, hb, congrArg Subtype.val hbx⟩
  · rintro ⟨b, hb, hbx⟩
    exact ⟨b, hb, Subtype.ext hbx⟩

private theorem isSubnormal_subgroupOf_map_inclusion_l410 {H G : Subgroup Ω} (hHG : H ≤ G)
    {B₀ : Subgroup ↥H} (hB : B₀.IsSubnormal) :
    ((B₀.map (Subgroup.inclusion hHG)).subgroupOf (H.subgroupOf G)).IsSubnormal := by
  rw [← map_subgroupOfEquiv_symm_eq_l410 hHG B₀]
  exact Subgroup.IsSubnormal.map
    (f := (Subgroup.subgroupOfEquivOfLe hHG).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hHG).symm.surjective hB

theorem hasGomiBlock_of_isSubnormal {G H : Subgroup Ω} {B₀ : Subgroup ↥H}
    (hHG : H ≤ G) (hB₀ : IsAschbacherBlockGomi B₀)
    (hsub : ((B₀.map H.subtype).subgroupOf G).IsSubnormal)
    (hQB : ⁅pCoreOf 2 G, B₀.map H.subtype⁆ ≤ gomiV G) : HasGomiBlock G := by
  let B' : Subgroup ↥G := B₀.map (Subgroup.inclusion hHG)
  have hB'eq : B' = (B₀.map H.subtype).subgroupOf G := by
    change B₀.map (Subgroup.inclusion hHG) = (B₀.map H.subtype).comap G.subtype
    rw [show B₀.map H.subtype = (B₀.map (Subgroup.inclusion hHG)).map G.subtype by
      rw [Subgroup.map_map, Subgroup.subtype_comp_inclusion]]
    rw [Subgroup.comap_map_eq_self_of_injective G.subtype_injective]
  have hBsub : B'.IsSubnormal := by
    rw [hB'eq]
    exact hsub
  have hBG : B₀.map H.subtype ≤ G := (Subgroup.map_subtype_le B₀).trans hHG
  have hcommG : ⁅pCore 2 ↥G, B'⁆ ≤ omegaOneCenterIn (pCore 2 ↥G) := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := G.subtype) G.subtype_injective]
    rw [Subgroup.map_commutator,
      map_omegaOneCenterIn_l410 G.subtype G.subtype_injective]
    rw [show (pCore 2 ↥G).map G.subtype = pCoreOf 2 G from rfl,
      show B'.map G.subtype = B₀.map H.subtype from by
        rw [hB'eq, Subgroup.map_subgroupOf_eq_of_le hBG]]
    rw [omegaOneCenterIn_eq_omegaOneCenterOf_l410]
    exact hQB
  exact ⟨B', IsAschbacherBlockGomi.map_of_injective (Subgroup.inclusion_injective hHG)
    hB₀ hBsub hcommG⟩

theorem hasGomiBlock_of_le_normalizer {G N H : Subgroup Ω} {B₀ : Subgroup ↥H}
    (hHG : H ≤ G) (hB₀ : IsAschbacherBlockGomi B₀) (hNG : N ≤ G)
    (hN : G ≤ normalizer (N : Set Ω)) (hGNH : G = N ⊔ H)
    (hNB : N ≤ normalizer ((B₀.map H.subtype : Subgroup Ω) : Set Ω))
    (hQB : ⁅pCoreOf 2 G, B₀.map H.subtype⁆ ≤ gomiV G) : HasGomiBlock G := by
  let B' : Subgroup ↥G := B₀.map (Subgroup.inclusion hHG)
  have hB'eq : B' = (B₀.map H.subtype).subgroupOf G := by
    change B₀.map (Subgroup.inclusion hHG) = (B₀.map H.subtype).comap G.subtype
    rw [show B₀.map H.subtype = (B₀.map (Subgroup.inclusion hHG)).map G.subtype by
      rw [Subgroup.map_map, Subgroup.subtype_comp_inclusion]]
    rw [Subgroup.comap_map_eq_self_of_injective G.subtype_injective]
  have hBH : B₀.map H.subtype ≤ H := Subgroup.map_subtype_le B₀
  have hBH' : B' ≤ H.subgroupOf G := by
    rw [hB'eq]
    exact Subgroup.subgroupOf_mono G hBH
  have hB'sub : (B'.subgroupOf (H.subgroupOf G)).IsSubnormal :=
    isSubnormal_subgroupOf_map_inclusion_l410 hHG hB₀.subnormal
  have hN'normal : (N.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).mpr hN
  have hNB' : N.subgroupOf G ≤ Subgroup.normalizer ((B' : Subgroup ↥G) : Set ↥G) := by
    rw [hB'eq]
    change N.comap G.subtype ≤
      Subgroup.normalizer (((B₀.map H.subtype).comap G.subtype : Subgroup ↥G) : Set ↥G)
    exact (Subgroup.comap_mono hNB).trans (Subgroup.le_normalizer_comap G.subtype)
  have hNH' : N.subgroupOf G ⊔ H.subgroupOf G = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNG hHG, ← hGNH, Subgroup.subgroupOf_self]
  have hBsubG : B'.IsSubnormal := isSubnormal_of_sup_eq_top hBH' hB'sub hN'normal hNB' hNH'
  have hsub : ((B₀.map H.subtype).subgroupOf G).IsSubnormal := by
    rw [← hB'eq]
    exact hBsubG
  exact hasGomiBlock_of_isSubnormal hHG hB₀ hsub hQB

theorem mul_eq_of_eq_sup {G N H K : Subgroup Ω} (hGNH : G = N ⊔ H)
    (hHN : H ≤ normalizer (N : Set Ω)) (hNK : N ≤ K) (hKG : K ≤ G) :
    (H : Set Ω) * (K : Set Ω) = G := by
  have hHG : H ≤ G := by rw [hGNH]; exact le_sup_right
  have hHNmul : (H : Set Ω) * (N : Set Ω) = (G : Set Ω) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H N hHN, sup_comm, ← hGNH]
  refine le_antisymm ?_ ?_
  · rintro g ⟨h, hh, x, hx, rfl⟩
    exact G.mul_mem (hHG hh) (hKG hx)
  · intro g hg
    have hg' : g ∈ (H : Set Ω) * (N : Set Ω) := by
      rw [hHNmul]; exact hg
    obtain ⟨h, hh, n, hn, rfl⟩ := hg'
    exact ⟨h, hh, n, hNK hn, rfl⟩

theorem IsAschbacherBlockGomi.commutator_map_le_gomiV {H : Subgroup Ω} {B₀ : Subgroup ↥H}
    (hB₀ : IsAschbacherBlockGomi B₀) : ⁅pCoreOf 2 H, B₀.map H.subtype⁆ ≤ gomiV H := by
  have hmap : (⁅pCore 2 ↥H, B₀⁆).map H.subtype ≤
      (omegaOneCenterIn (pCore 2 ↥H)).map H.subtype :=
    Subgroup.map_mono hB₀.comm_oTwo
  rw [Subgroup.map_commutator,
    map_omegaOneCenterIn_l410 H.subtype H.subtype_injective] at hmap
  refine hmap.trans ?_
  rw [omegaOneCenterIn_eq_omegaOneCenterOf_l410]
  exact le_rfl

theorem IsAschbacherBlockGomi.pCoreOf_le_normalizer [Finite Ω] {H : Subgroup Ω}
    {B₀ : Subgroup ↥H} (hB₀ : IsAschbacherBlockGomi B₀) :
    pCoreOf 2 H ≤ normalizer ((B₀.map H.subtype : Subgroup Ω) : Set Ω) := by
  have hle : pCore 2 ↥H ≤ Subgroup.normalizer (B₀ : Set ↥H) :=
    CFSG.CGT.PushingUpLit.SubTwo.le_normalizer_of_isSubnormal_sup
      (CFSG.CGT.PushingUpLit.SubTwo.noTwoQuotient_of_oResidualTwo hB₀.residual)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
      (Subgroup.le_normalizer_of_normal (H := pCore 2 ↥H) (K := B₀))
      (Subgroup.IsSubnormal.subgroupOf hB₀.subnormal)
  exact (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map (H := B₀) H.subtype)

end CFSG.GroupTheory

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescGrp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5AbsQuot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5AbsLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5GrpXE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma subtype_ker_sq (L : Subgroup G) :
    ∀ k ∈ (normalizer (L : Set G)).subtype.ker, k * k = 1 := by
  intro k hk
  rw [Subgroup.ker_subtype] at hk
  rw [Subgroup.mem_bot] at hk
  rw [hk, mul_one]

private lemma subtype_ker_central (L : Subgroup G) :
    (normalizer (L : Set G)).subtype.ker ≤
      Subgroup.center ↥(normalizer (L : Set G)) := by
  intro k hk
  rw [Subgroup.ker_subtype] at hk
  rw [Subgroup.mem_bot] at hk
  rw [hk]
  exact Subgroup.one_mem _

@[expose] def descCent (L : Subgroup G) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    Subgroup ↥(normalizer (L : Set G)) :=
  L.subgroupOf (normalizer (L : Set G)) ⊓
    centralizer ({(⟨s, hs⟩ : ↥(normalizer (L : Set G)))} : Set ↥(normalizer (L : Set G)))

@[expose] def descT (L : Subgroup G) {t : G} (ht : t ∈ centerIn L) :
    ↥(normalizer (L : Set G)) :=
  ⟨t, Subgroup.le_normalizer (H := L) (Subgroup.map_subtype_le (Subgroup.center ↥L) ht)⟩

theorem descCent_map_subtype (L : Subgroup G) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    (descCent L hs).map (normalizer (L : Set G)).subtype = L ⊓ centralizer ({s} : Set G) := by
  unfold descCent
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨hnL, hnc⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mp hnL
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      have h := Subgroup.mem_centralizer_iff.mp hnc (⟨s, hs⟩ : ↥(normalizer (L : Set G)))
        (Set.mem_singleton _)
      exact congrArg Subtype.val h
  · intro hg
    obtain ⟨hgL, hgc⟩ := Subgroup.mem_inf.mp hg
    refine Subgroup.mem_map.mpr ⟨⟨g, Subgroup.le_normalizer (H := L) hgL⟩, ?_, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hgL
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc s (Set.mem_singleton s))

theorem descT_mem_center (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) :
    descT L ht ∈ Subgroup.center ↥(normalizer (L : Set G)) := by
  rw [Subgroup.mem_center_iff]
  intro m
  exact Subtype.ext (t5_normalizer_commute hL ht ht2 m.2)

theorem descT_mul_self {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) :
    descT L ht * descT L ht = 1 := by
  apply Subtype.ext
  show t * t = 1
  rw [← pow_two, ← ht2, pow_orderOf_eq_one]

theorem descT_mem_descCent (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    {s : G} (hs : s ∈ normalizer (L : Set G)) : descT L ht ∈ descCent L hs := by
  unfold descCent
  rw [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr (Subgroup.map_subtype_le (Subgroup.center ↥L) ht)
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Subgroup.mem_center_iff.mp (descT_mem_center hL ht ht2) _

theorem descMk_ker_le_zpowers (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) : (descMk L t).ker ≤ Subgroup.zpowers (descT L ht) := by
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  rcases (descMk_eq_one_iff hL ht ht2 k).mp hk with h | h
  · have hk1 : k = 1 := Subtype.ext h
    rw [hk1]
    exact Subgroup.one_mem _
  · have hk1 : k = descT L ht := by
      unfold descT
      exact Subtype.ext h
    rw [hk1]
    exact Subgroup.mem_zpowers _

theorem descMk_ker_sq (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) :
    ∀ k ∈ (descMk L t).ker, k * k = 1 := by
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  rcases (descMk_eq_one_iff hL ht ht2 k).mp hk with h | h
  · have hk1 : k = 1 := Subtype.ext h
    rw [hk1, one_mul]
  · have hk1 : k = descT L ht := by
      unfold descT
      exact Subtype.ext h
    rw [hk1, descT_mul_self ht ht2]

theorem descMk_ker_central (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) : (descMk L t).ker ≤ Subgroup.center ↥(normalizer (L : Set G)) := by
  intro k hk
  exact Subgroup.zpowers_le.mpr (descT_mem_center hL ht ht2)
    (descMk_ker_le_zpowers hL ht ht2 hk)

theorem t5_twoRes_cent_eq (L : Subgroup G) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    twoRes (L ⊓ centralizer ({s} : Set G)) =
      (twoRes (descCent L hs)).map (normalizer (L : Set G)).subtype := by
  rw [map_twoRes (normalizer (L : Set G)).subtype (subtype_ker_sq L) (descCent L hs),
    descCent_map_subtype L hs]

theorem t5_desc_twoRes_cent (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    {s : G} (hs : s ∈ normalizer (L : Set G)) :
    twoRes (DescL L t ⊓ centralizer ({descElt L t s hs} : Set (DescG L t))) =
      (twoRes (descCent L hs)).map (descMk L t) := by
  unfold DescL descElt descCent
  exact map_twoRes_cent (descMk L t) (descMk_ker_central hL ht ht2) (descMk_ker_sq hL ht ht2)
    (L.subgroupOf (normalizer (L : Set G))) (⟨s, hs⟩ : ↥(normalizer (L : Set G)))

theorem t5_xout_eq_map (L : Subgroup G) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    XOut L s = (twoPrimeRes (twoRes (descCent L hs))).map (normalizer (L : Set G)).subtype := by
  unfold XOut
  rw [t5_twoRes_cent_eq L hs,
    ← map_twoPrimeRes (normalizer (L : Set G)).subtype (subtype_ker_sq L)
      (twoRes (descCent L hs))]

theorem t5_desc_xout (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    {s : G} (hs : s ∈ normalizer (L : Set G)) :
    XOut (DescL L t) (descElt L t s hs) =
      (twoPrimeRes (twoRes (descCent L hs))).map (descMk L t) := by
  unfold XOut DescL descElt descCent
  exact map_xout (descMk L t) (descMk_ker_central hL ht ht2) (descMk_ker_sq hL ht ht2)
    (L.subgroupOf (normalizer (L : Set G))) (⟨s, hs⟩ : ↥(normalizer (L : Set G)))

theorem t5_layerCent_eq_map (L : Subgroup G) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    layerCent L s =
      (CFSG.inSubgroup CFSG.layer (descCent L hs)).map (normalizer (L : Set G)).subtype := by
  have hLN : L ≤ normalizer (L : Set G) := Subgroup.le_normalizer
  have hmapL : (L.subgroupOf (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLN]
  have hmap := map_layer_cent (normalizer (L : Set G)).subtype (subtype_ker_central L)
    (subtype_ker_sq L) (L.subgroupOf (normalizer (L : Set G)))
    (⟨s, hs⟩ : ↥(normalizer (L : Set G)))
  rw [hmapL] at hmap
  unfold layerCent descCent
  exact hmap

theorem t5_desc_layerCent (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    {s : G} (hs : s ∈ normalizer (L : Set G)) :
    layerCent (DescL L t) (descElt L t s hs) =
      (CFSG.inSubgroup CFSG.layer (descCent L hs)).map (descMk L t) := by
  unfold layerCent DescL descElt descCent
  exact map_layer_cent (descMk L t) (descMk_ker_central hL ht ht2) (descMk_ker_sq hL ht ht2)
    (L.subgroupOf (normalizer (L : Set G))) (⟨s, hs⟩ : ↥(normalizer (L : Set G)))

theorem t5_desc_layerCent_bot_iff (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    layerCent (DescL L t) (descElt L t s hs) = ⊥ ↔ layerCent L s = ⊥ := by
  let En : Subgroup ↥(normalizer (L : Set G)) :=
    CFSG.inSubgroup CFSG.layer (descCent L hs)
  have hLmap : layerCent L s = En.map (normalizer (L : Set G)).subtype :=
    t5_layerCent_eq_map L hs
  have hDmap : layerCent (DescL L t) (descElt L t s hs) = En.map (descMk L t) :=
    t5_desc_layerCent hL ht ht2 hs
  rw [hDmap, hLmap]
  constructor
  · intro h
    have hle : En ≤ (descMk L t).ker := (Subgroup.map_eq_bot_iff (H := En)).mp h
    have hzp : En ≤ Subgroup.zpowers (descT L ht) :=
      hle.trans (descMk_ker_le_zpowers hL ht ht2)
    haveI : Group.IsPerfect ↥En := t5_layer_perfect (descCent L hs)
    haveI : IsMulCommutative ↥En := IsMulCommutative.of_comm fun a b => by
      have hx : (⟨(a : ↥(normalizer (L : Set G))), hzp a.2⟩ :
            ↥(Subgroup.zpowers (descT L ht))) *
          ⟨(b : ↥(normalizer (L : Set G))), hzp b.2⟩ =
          ⟨(b : ↥(normalizer (L : Set G))), hzp b.2⟩ *
          ⟨(a : ↥(normalizer (L : Set G))), hzp a.2⟩ := mul_comm' _ _
      have hx' := congrArg (Subtype.val :
        ↥(Subgroup.zpowers (descT L ht)) → ↥(normalizer (L : Set G))) hx
      exact Subtype.ext hx'
    haveI : Subsingleton ↥En := Group.IsPerfect.subsingleton_of_isMulCommutative
    have hbot : En = ⊥ := Subgroup.eq_bot_of_subsingleton En
    rw [hbot, Subgroup.map_bot]
  · intro h
    have hbot : En = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := En)
        (Subgroup.subtype_injective (normalizer (L : Set G)))).mp h
    rw [hbot, Subgroup.map_bot]

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.MapShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XBase

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem o1_of_tableX {a z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀)
    (h1 : orb2A a p ∩ orb2A a (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 0) :
    IsConjOrbitStab (Gxy p z) (orb2A a p ∩ orb2A a (p * z)) (2 ^ 8 * 3) := by
  have hf : Function.Injective (Gx p).subtype := Subgroup.subtype_injective (Gx p)
  have h1' : orb2A a p ∩ orb2A a (p * z) =
      (Gx p).subtype '' tabXSet (GxSelf p) x b₀ u₀ 0 := by
    simpa using h1
  constructor
  · rw [h1', Gxy_eq_map_of_eq hx]
    exact (isConjOrbit_map_iff hf (Gx x) (tabXSet (GxSelf p) x b₀ u₀ 0)).2
      (hT.partition.orbit 0)
  · intro c hc
    rw [h1'] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have hstab := (stabCard_map_iff hf (Gx x) (tabXSet (GxSelf p) x b₀ u₀) ![768, 384]).2
      hT.card_stab 0 ((Gx p).subtype c') ⟨c', hc', rfl⟩
    rw [← Gxy_eq_map_of_eq hx] at hstab
    rw [hstab]
    decide

theorem o1_mem_of_tableX {a z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀)
    (h1 : orb2A a p ∩ orb2A a (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 0)
    (hR : CFSG.Open.pCoreOf 2 (Gxy p z) = Gxy p z ⊓ Qz z) :
    ∀ c ∈ orb2A a p ∩ orb2A a (p * z), c ∈ Qz z := by
  have h1' : orb2A a p ∩ orb2A a (p * z) =
      (Gx p).subtype '' tabXSet (GxSelf p) x b₀ u₀ 0 := by
    simpa using h1
  intro c hc
  rw [h1'] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  have hmem : (Gx p).subtype c' ∈ (CFSG.Open.pCoreOf 2 (Gx x)).map (Gx p).subtype :=
    Subgroup.mem_map.mpr ⟨c', hT.o1_mem c' hc', rfl⟩
  rw [← pCoreOf_Gxy_eq_map hx] at hmem
  rw [hR] at hmem
  exact (Subgroup.mem_inf.mp hmem).2

theorem o1_cards_of_tableX {a z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀)
    (h1 : orb2A a p ∩ orb2A a (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 0)
    (hR : CFSG.Open.pCoreOf 2 (Gxy p z) = Gxy p z ⊓ Qz z) :
    ∀ c ∈ orb2A a p ∩ orb2A a (p * z),
      Nat.card ↥(Gxyz p z c ⊓ Qz z) = 2 ^ 7 ∧
      Nat.card ↥(Gxyz p z c ⊓ Qz z ⊓ derivedOf (Gxy p z)) = 2 ^ 6 ∧
      Nat.card ↥(Gxyz p z c ⊓ derivedOf (Gxy p z)) = 2 ^ 6 * 3 ∧
      QuotShape (Gxyz p z c ⊓ derivedOf (Gxy p z))
        (Gxyz p z c ⊓ Qz z ⊓ derivedOf (Gxy p z)) (Z 3) := by
  have hf : Function.Injective (Gx p).subtype := Subgroup.subtype_injective (Gx p)
  intro c hc
  rw [h1] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Gxyz_inf_Qz_eq_map hx hR c', Subgroup.card_map_of_injective hf, hT.o1_card_R c' hc']
  · rw [Gxyz_inf_Qz_inf_derivedOf_eq_map hx hR c', Subgroup.card_map_of_injective hf,
      hT.o1_card_R_X' c' hc']
  · rw [Gxyz_inf_derivedOf_eq_map hx c', Subgroup.card_map_of_injective hf,
      hT.o1_card_X' c' hc']
  · rw [Gxyz_inf_derivedOf_eq_map hx c', Gxyz_inf_Qz_inf_derivedOf_eq_map hx hR c']
    exact QuotShape.map hf (hT.o1_quot c' hc')

theorem three_cent_of_tableX {a z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀)
    (h1 : orb2A a p ∩ orb2A a (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 0)
    (hR : CFSG.Open.pCoreOf 2 (Gxy p z) = Gxy p z ⊓ Qz z) :
    ∀ σ ∈ Gxy p z, orderOf σ = 3 → ∃ c ∈ orb2A a p ∩ orb2A a (p * z),
      CFSG.Open.pCoreOf 2 (Gxy p z) ⊓ Gx σ =
          Subgroup.closure ((centerOf (derivedOf (Gxy p z)) : Set G) ∪ {c}) ∧
        CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z)) ⊓ Gx σ = centerOf (derivedOf (Gxy p z)) := by
  have hf : Function.Injective (Gx p).subtype := Subgroup.subtype_injective (Gx p)
  have h1' : orb2A a p ∩ orb2A a (p * z) =
      (Gx p).subtype '' tabXSet (GxSelf p) x b₀ u₀ 0 := by
    simpa using h1
  intro σ hσ hord
  rw [Gxy_eq_map_of_eq hx] at hσ
  obtain ⟨σ', hσ', rfl⟩ := Subgroup.mem_map.mp hσ
  have hord' : orderOf σ' = 3 := by
    rw [← orderOf_injective (Gx p).subtype hf σ']
    exact hord
  obtain ⟨c', hc', heq1, heq2⟩ := hT.three_centralizer σ' hσ' hord'
  refine ⟨(Gx p).subtype c', ?_, ?_, ?_⟩
  · rw [h1']
    exact ⟨c', hc', rfl⟩
  · rw [pCoreOf_Gxy_eq_map hx, map_inf_Gx_of_injective hf (CFSG.Open.pCoreOf 2 (Gx x)) σ',
      heq1, MonoidHom.map_closure, Set.image_union, Set.image_singleton,
      ← Subgroup.coe_map, ← centerOf_derivedOf_Gxy_eq_map hx]
  · rw [pCoreOf_derivedOf_Gxy_eq_map hx,
      map_inf_Gx_of_injective hf (CFSG.Open.pCoreOf 2 (derivedOf (Gx x))) σ',
      hT.pCore_derived.1, heq2, centerOf_derivedOf_Gxy_eq_map hx]

theorem o2_of_tableX {a z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀)
    (h2 : orb2A a p ∩ orb2B a z (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 1) :
    IsConjOrbitStab (Gxy p z) (orb2A a p ∩ orb2B a z (p * z)) (2 ^ 7 * 3) := by
  have hf : Function.Injective (Gx p).subtype := Subgroup.subtype_injective (Gx p)
  have h2' : orb2A a p ∩ orb2B a z (p * z) =
      (Gx p).subtype '' tabXSet (GxSelf p) x b₀ u₀ 1 := by
    simpa using h2
  constructor
  · rw [h2', Gxy_eq_map_of_eq hx]
    exact (isConjOrbit_map_iff hf (Gx x) (tabXSet (GxSelf p) x b₀ u₀ 1)).2
      (hT.partition.orbit 1)
  · intro c hc
    rw [h2'] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have hstab := (stabCard_map_iff hf (Gx x) (tabXSet (GxSelf p) x b₀ u₀) ![768, 384]).2
      hT.card_stab 1 ((Gx p).subtype c') ⟨c', hc', rfl⟩
    rw [← Gxy_eq_map_of_eq hx] at hstab
    rw [hstab]
    decide

theorem o2_cards_of_tableX {a z p : G} {x b₀ u₀ : ↥(Gx p)} (hx : (x : G) = z)
    (hT : TableXData (GxSelf p) x b₀ u₀)
    (h2 : orb2A a p ∩ orb2B a z (p * z) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 1)
    (hR : CFSG.Open.pCoreOf 2 (Gxy p z) = Gxy p z ⊓ Qz z) :
    ∀ d ∈ orb2A a p ∩ orb2B a z (p * z),
      IsElemTwo 5 (Gxyz p z d ⊓ Qz z) ∧
      IsElemTwo 4 (Gxyz p z d ⊓ Qz z ⊓ derivedOf (Gxy p z)) ∧
      Nat.card ↥(Gxyz p z d ⊓ derivedOf (Gxy p z)) = 2 ^ 5 * 3 ∧
      QuotShape (Gxyz p z d ⊓ derivedOf (Gxy p z))
        (Gxyz p z d ⊓ Qz z ⊓ derivedOf (Gxy p z)) (Sym 3) := by
  have hf : Function.Injective (Gx p).subtype := Subgroup.subtype_injective (Gx p)
  intro d hd
  rw [h2] at hd
  obtain ⟨d', hd', rfl⟩ := hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Gxyz_inf_Qz_eq_map hx hR d']
    exact isElemTwo_map_of_injective hf (hT.o2_R d' hd')
  · rw [Gxyz_inf_Qz_inf_derivedOf_eq_map hx hR d']
    exact isElemTwo_map_of_injective hf (hT.o2_R_X' d' hd')
  · rw [Gxyz_inf_derivedOf_eq_map hx d', Subgroup.card_map_of_injective hf,
      hT.o2_card_X' d' hd']
  · rw [Gxyz_inf_derivedOf_eq_map hx d', Gxyz_inf_Qz_inf_derivedOf_eq_map hx hR d']
    exact QuotShape.map hf (hT.o2_quot d' hd')

end CFSG.EvenSporadicStandard.HNRecog.Section3

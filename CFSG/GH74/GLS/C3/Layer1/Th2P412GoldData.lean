module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldC
public import CFSG.GH74.GLS.C3.Layer1.Th2P412Gen

public section

namespace CFSG.GH74.GLS.Th2.P412

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Goldschmidt CFSG.GH74.Uniqueness

theorem tiData0_of_data
    {G : Type} [Group G] [Finite G] {C : Subgroup G} {v x : G} {Zs : Set G} {S E : Subgroup G}
    (hvC : v ∈ C) (hxC : x ∈ C) (hSC : S ≤ C)
    (hv_sq : v * v = 1) (hv_ne : v ≠ 1) (hv_comm : ∀ c ∈ C, c * v = v * c)
    (hZ_sq : ∀ z ∈ Zs, z * z = 1) (hZ_ne : ∀ z ∈ Zs, z ≠ 1) (hv_nmem : v ∉ Zs)
    (hZ_conj : ∀ z ∈ Zs, ∀ g ∈ C, g * z * g⁻¹ ∈ Zs) (hZ_mul_v : ∀ z ∈ Zs, z * v ∈ Zs)
    (hsylow : IsSylowOf 2 S C) (hE_le : E ≤ S) (hE_card : Nat.card E = 8)
    (hE_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE_sq : ∀ a ∈ E, a * a = 1) (hv_mem : v ∈ E)
    (hS_norm : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hZ_inter : ∀ y ∈ S, (y ∈ Zs ↔ (y ∈ E ∧ y ≠ 1 ∧ y ≠ v)))
    (hx_Z : x ∈ Zs) (hx_E : x ∈ E) (hZ_single : ∀ z ∈ Zs, ∃ c ∈ C, c * x * c⁻¹ = z) :
    TIData0 (⟨v, hvC⟩ : ↥C) {c : ↥C | (c : G) ∈ Zs} (S.subgroupOf C) (E.subgroupOf C)
      (⟨x, hxC⟩ : ↥C) := by
  have hEC : E ≤ C := hE_le.trans hSC
  have hSmap : (S.subgroupOf C).map C.subtype = S := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hSC]
  refine
    { v_sq := Subtype.ext hv_sq
      v_ne := fun h => hv_ne (congrArg Subtype.val h)
      v_comm := fun c => Subtype.ext (hv_comm c c.2)
      Z_sq := fun z hz => Subtype.ext (hZ_sq z hz)
      Z_ne := fun z hz h => hZ_ne z hz (congrArg Subtype.val h)
      v_nmem := hv_nmem
      Z_conj := fun z hz g => hZ_conj z hz g g.2
      Z_mul_v := fun z hz => hZ_mul_v z hz
      sylow := ?_
      E_le := fun e he => hE_le he
      E_card := ?_
      E_comm := fun a ha b hb => Subtype.ext (hE_comm _ ha _ hb)
      E_sq := fun a ha => Subtype.ext (hE_sq _ ha)
      v_mem := hv_mem
      S_norm := fun s hs e he => hS_norm _ hs _ he
      Z_inter := ?_
      x_Z := hx_Z
      x_E := hx_E
      Z_single := ?_ }
  · have hmapTop : (⊤ : Subgroup ↥C).map C.subtype = C := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [← isSylowOf_map_subtype_iff C, hSmap, hmapTop]
    exact hsylow
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv).trans hE_card
  · intro y hy
    have h1 := hZ_inter (y : G) hy
    refine h1.trans ?_
    constructor
    · rintro ⟨h2, h3, h4⟩
      exact ⟨h2, fun h => h3 (congrArg Subtype.val h), fun h => h4 (congrArg Subtype.val h)⟩
    · rintro ⟨h2, h3, h4⟩
      exact ⟨h2, fun h => h3 (Subtype.ext h), fun h => h4 (Subtype.ext h)⟩
  · intro z hz
    obtain ⟨c, hc, hcz⟩ := hZ_single z hz
    exact ⟨⟨c, hc⟩, Subtype.ext hcz⟩

theorem gold_cent_of_data
    (hGold : GoldStmt) (hN11a : S_N11a) (hN11b : S_N11b)
    {G : Type} [Group G] [Finite G] {C : Subgroup G} {v x : G} {Zs : Set G} {S E : Subgroup G}
    (hvC : v ∈ C) (hxC : x ∈ C) (hSC : S ≤ C)
    (hv_sq : v * v = 1) (hv_ne : v ≠ 1) (hv_comm : ∀ c ∈ C, c * v = v * c)
    (hZ_sq : ∀ z ∈ Zs, z * z = 1) (hZ_ne : ∀ z ∈ Zs, z ≠ 1) (hv_nmem : v ∉ Zs)
    (hZ_conj : ∀ z ∈ Zs, ∀ g ∈ C, g * z * g⁻¹ ∈ Zs) (hZ_mul_v : ∀ z ∈ Zs, z * v ∈ Zs)
    (hsylow : IsSylowOf 2 S C) (hE_le : E ≤ S) (hE_card : Nat.card E = 8)
    (hE_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE_sq : ∀ a ∈ E, a * a = 1) (hv_mem : v ∈ E)
    (hS_norm : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hZ_inter : ∀ y ∈ S, (y ∈ Zs ↔ (y ∈ E ∧ y ≠ 1 ∧ y ≠ v)))
    (hx_Z : x ∈ Zs) (hx_E : x ∈ E) (hZ_single : ∀ z ∈ Zs, ∃ c ∈ C, c * x * c⁻¹ = z)
    (hS128 : Nat.card S ≤ 128) (hex : ∃ s ∈ S, s * s = 1 ∧ s ∉ E) :
    ∀ g ∈ C, ∀ e ∈ E, ∃ e' ∈ E, ∃ o ∈ pPrimeCoreOf 2 C, g * e * g⁻¹ = e' * o := by
  intro g hg e he
  have hEC : E ≤ C := hE_le.trans hSC
  have hTI := tiData0_of_data hvC hxC hSC hv_sq hv_ne hv_comm hZ_sq hZ_ne hv_nmem hZ_conj hZ_mul_v
    hsylow hE_le hE_card hE_comm hE_sq hv_mem hS_norm hZ_inter hx_Z hx_E hZ_single
  have hS' : Nat.card ↥(S.subgroupOf C) ≤ 128 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv).trans_le hS128
  have hex' : ∃ s ∈ S.subgroupOf C, s * s = 1 ∧ s ∉ E.subgroupOf C := by
    obtain ⟨s, hsS, hs2, hsE⟩ := hex
    exact ⟨⟨s, hSC hsS⟩, hsS, Subtype.ext hs2, hsE⟩
  obtain ⟨e', he', o, ho, hheo⟩ := gold_normal_EO hGold hN11a hN11b hTI hS' hex' ⟨g, hg⟩
    ⟨e, hEC he⟩ he
  exact ⟨(e' : G), he', (o : G), ⟨o, ho, rfl⟩, congrArg Subtype.val hheo⟩

theorem isSolvable_of_E8_data_gold (hZD : S_ZD)
    (hGold : GoldStmt) (hN11a : S_N11a) (hN11b : S_N11b)
    {G : Type} [Group G] [Finite G] {C : Subgroup G} {v x : G} {Zs : Set G} {S E : Subgroup G}
    (hvC : v ∈ C) (hxC : x ∈ C) (hSC : S ≤ C)
    (hv_sq : v * v = 1) (hv_ne : v ≠ 1) (hv_comm : ∀ c ∈ C, c * v = v * c)
    (hZ_sq : ∀ z ∈ Zs, z * z = 1) (hZ_ne : ∀ z ∈ Zs, z ≠ 1) (hv_nmem : v ∉ Zs)
    (hZ_conj : ∀ z ∈ Zs, ∀ g ∈ C, g * z * g⁻¹ ∈ Zs) (hZ_mul_v : ∀ z ∈ Zs, z * v ∈ Zs)
    (hsylow : IsSylowOf 2 S C) (hE_le : E ≤ S) (hE_card : Nat.card E = 8)
    (hE_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE_sq : ∀ a ∈ E, a * a = 1) (hv_mem : v ∈ E)
    (hS_norm : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hZ_inter : ∀ y ∈ S, (y ∈ Zs ↔ (y ∈ E ∧ y ≠ 1 ∧ y ≠ v)))
    (hx_Z : x ∈ Zs) (hx_E : x ∈ E) (hZ_single : ∀ z ∈ Zs, ∃ c ∈ C, c * x * c⁻¹ = z)
    (hS128 : Nat.card S ≤ 128) (hex : ∃ s ∈ S, s * s = 1 ∧ s ∉ E)
    (hZS : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 → s = v)
    (hCS : Nat.card ↥(S ⊓ centralizer (E : Set G)) ≤ 16) : Group.IsSolvable ↥C :=
  isSolvable_of_E8_data hZD hvC hxC hSC hv_sq hv_ne hv_comm hZ_sq hZ_ne hv_nmem hZ_conj hZ_mul_v
    hsylow hE_le hE_card hE_comm hE_sq hv_mem hS_norm hZ_inter hx_Z hx_E hZ_single
    (fun g hg _ e he => gold_cent_of_data hGold hN11a hN11b hvC hxC hSC hv_sq hv_ne hv_comm hZ_sq
      hZ_ne hv_nmem hZ_conj hZ_mul_v hsylow hE_le hE_card hE_comm hE_sq hv_mem hS_norm hZ_inter
      hx_Z hx_E hZ_single hS128 hex g hg e he)
    hS128 hex hZS hCS

end CFSG.GH74.GLS.Th2.P412

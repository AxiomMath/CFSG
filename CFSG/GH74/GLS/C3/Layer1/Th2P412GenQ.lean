module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412QT
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Th2.P412

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.Uniqueness

theorem tiDataQ_of_data
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
    (hcent : ∀ g ∈ C, g * x = x * g → ∀ e ∈ E,
      ∃ e' ∈ E, ∃ o ∈ pPrimeCoreOf 2 C, g * e * g⁻¹ = e' * o) :
    TIDataQ (⟨v, hvC⟩ : ↥C) {c : ↥C | (c : G) ∈ Zs} (S.subgroupOf C) (E.subgroupOf C)
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
      Z_single := ?_
      cent := ?_ }
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
  · intro g hg e he
    obtain ⟨e', he', o, ho, hheo⟩ := hcent g g.2 (congrArg Subtype.val hg) e he
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.1 ho
    exact ⟨⟨e', hEC he'⟩, he', o', ho', Subtype.ext hheo⟩

end CFSG.GH74.GLS.Th2.P412

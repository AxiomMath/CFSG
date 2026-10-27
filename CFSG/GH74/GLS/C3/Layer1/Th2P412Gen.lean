module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GenQ

public section

namespace CFSG.GH74.GLS.Th2.P412

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.Uniqueness

theorem isSolvable_of_E8_data (hZD : S_ZD)
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
      ∃ e' ∈ E, ∃ o ∈ pPrimeCoreOf 2 C, g * e * g⁻¹ = e' * o)
    (hS128 : Nat.card S ≤ 128) (hex : ∃ s ∈ S, s * s = 1 ∧ s ∉ E)
    (hZS : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 → s = v)
    (hCS : Nat.card ↥(S ⊓ centralizer (E : Set G)) ≤ 16) : Group.IsSolvable ↥C := by
  have hEC : E ≤ C := hE_le.trans hSC
  have hTI := tiDataQ_of_data hvC hxC hSC hv_sq hv_ne hv_comm hZ_sq hZ_ne hv_nmem hZ_conj hZ_mul_v
    hsylow hE_le hE_card hE_comm hE_sq hv_mem hS_norm hZ_inter hx_Z hx_E hZ_single hcent
  refine isSolvable_of_tiDataQ hZD hTI ?_ ?_ ?_ ?_
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv).trans_le hS128
  · obtain ⟨s, hsS, hs2, hsE⟩ := hex
    exact ⟨⟨s, hSC hsS⟩, hsS, Subtype.ext hs2, hsE⟩
  · intro s hs hcomm hs2 hs1
    refine Subtype.ext (hZS s hs ?_ (congrArg Subtype.val hs2) (fun h => hs1 (Subtype.ext h)))
    intro t ht
    exact congrArg Subtype.val (hcomm ⟨t, hSC ht⟩ ht)
  · have hle : (S.subgroupOf C ⊓ centralizer ((E.subgroupOf C : Subgroup ↥C) : Set ↥C)).map
        C.subtype ≤ S ⊓ centralizer (E : Set G) := by
      rintro _ ⟨s, ⟨hsS, hsc⟩, rfl⟩
      have hsc' : s ∈ centralizer ((E.subgroupOf C : Subgroup ↥C) : Set ↥C) := hsc
      refine ⟨hsS, ?_⟩
      show (s : G) ∈ centralizer (E : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have := Subgroup.mem_centralizer_iff.1 hsc' ⟨e, hEC he⟩ he
      exact congrArg Subtype.val this
    calc Nat.card ↥(S.subgroupOf C ⊓ centralizer ((E.subgroupOf C : Subgroup ↥C) : Set ↥C))
        = Nat.card ↥((S.subgroupOf C ⊓ centralizer ((E.subgroupOf C : Subgroup ↥C) : Set ↥C)).map
            C.subtype) := (Subgroup.card_map_of_injective C.subtype_injective).symm
      _ ≤ Nat.card ↥(S ⊓ centralizer (E : Set G)) := Subgroup.card_le_of_le hle
      _ ≤ 16 := hCS

end CFSG.GH74.GLS.Th2.P412

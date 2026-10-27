module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6Split
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6Act

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit

open Subgroup

variable {G : Type*} [Group G] (D Y : Subgroup G) [(Y.subgroupOf D).Normal]

@[expose] def liftFix (S : Subgroup (normDY D Y)) : Subgroup G :=
  ((fixSub (actQuot D Y) S).comap (QuotientGroup.mk' (Y.subgroupOf D))).map D.subtype

@[expose] def liftFixG (S : Subgroup G) : Subgroup G :=
  liftFix D Y (S.subgroupOf (normDY D Y))

theorem mem_liftFix_iff (S : Subgroup (normDY D Y)) {x : G} :
    x ∈ liftFix D Y S ↔ ∃ hx : x ∈ D, ∀ g ∈ S, (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ Y := by
  unfold liftFix
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, mem_fixSub] at hy
    exact ⟨y.2, fun g hg => (actQuot_mk_eq_iff D Y g y).1 (hy g hg)⟩
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, mem_fixSub]
    exact fun g hg => (actQuot_mk_eq_iff D Y g ⟨x, hx⟩).2 (h g hg)

theorem mem_liftFixG_iff {S : Subgroup G} (hS : S ≤ normDY D Y) {x : G} :
    x ∈ liftFixG D Y S ↔ x ∈ D ∧ ∀ g ∈ S, g * x * g⁻¹ * x⁻¹ ∈ Y := by
  unfold liftFixG
  rw [mem_liftFix_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun g hg => h ⟨g, hS hg⟩ (Subgroup.mem_subgroupOf.mpr hg)⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun g hg => h g (Subgroup.mem_subgroupOf.mp hg)⟩

theorem Y_le_liftFix (hYD : Y ≤ D) (S : Subgroup (normDY D Y)) : Y ≤ liftFix D Y S := by
  intro y hy
  refine (mem_liftFix_iff D Y S).2 ⟨hYD hy, fun g _ => ?_⟩
  have hgY : (g : G) * y * (g : G)⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp ((mem_normDY D Y).mp g.2).2 y).mp hy
  exact Y.mul_mem hgY (Y.inv_mem hy)

theorem card_liftFix (hYD : Y ≤ D) (S : Subgroup (normDY D Y)) :
    Nat.card (liftFix D Y S) = Nat.card Y * Nat.card (fixSub (actQuot D Y) S) := by
  have hK : Nat.card (Y.subgroupOf D) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYD).toEquiv
  have hpre : Nat.card ↥((fixSub (actQuot D Y) S).comap (QuotientGroup.mk' (Y.subgroupOf D)))
      = Nat.card (Y.subgroupOf D) * Nat.card (fixSub (actQuot D Y) S) := by
    have e : ↥((fixSub (actQuot D Y) S).comap (QuotientGroup.mk' (Y.subgroupOf D)))
        ≃ ↥(QuotientGroup.mk ⁻¹' ((fixSub (actQuot D Y) S : Subgroup (D ⧸ Y.subgroupOf D)) :
          Set (D ⧸ Y.subgroupOf D))) :=
      Equiv.subtypeEquivRight fun x => Iff.rfl
    have h1 := QuotientGroup.card_preimage_mk (Y.subgroupOf D)
      ((fixSub (actQuot D Y) S : Subgroup (D ⧸ Y.subgroupOf D)) : Set (D ⧸ Y.subgroupOf D))
    rw [Nat.card_congr e]
    exact h1
  unfold liftFix
  rw [Subgroup.card_map_of_injective D.subtype_injective, hpre, hK]

theorem liftFix_inf (S T : Subgroup (normDY D Y)) :
    liftFix D Y S ⊓ liftFix D Y T = liftFix D Y (S ⊔ T) := by
  unfold liftFix
  rw [fixSub_sup, Subgroup.comap_inf, Subgroup.map_inf _ _ _ D.subtype_injective]

theorem liftFix_sup_of_fixSub_sup (S T : Subgroup (normDY D Y))
    (h : fixSub (actQuot D Y) S ⊔ fixSub (actQuot D Y) T = ⊤) :
    liftFix D Y S ⊔ liftFix D Y T = D := by
  unfold liftFix
  rw [← Subgroup.map_sup,
    Subgroup.comap_sup_eq _ _ _ (QuotientGroup.mk'_surjective (Y.subgroupOf D)), h,
    Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem liftFix_map_conj (S : Subgroup (normDY D Y)) (g : normDY D Y) :
    liftFix D Y (S.map (MulAut.conj g).toMonoidHom) =
      (liftFix D Y S).map (MulAut.conj (g : G)).toMonoidHom := by
  have hgY : (g : G) ∈ normalizer (Y : Set G) := ((mem_normDY D Y).mp g.2).2
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨hxD, h⟩ := (mem_liftFix_iff D Y _).1 hx
    refine ⟨(g : G)⁻¹ * x * (g : G), ?_, ?_⟩
    · refine (mem_liftFix_iff D Y S).2 ⟨conj_inv_mem_D D Y g.2 hxD, fun s hs => ?_⟩
      have hm : (g : G) * (s : G) * (g : G)⁻¹ * x * ((g : G) * (s : G) * (g : G)⁻¹)⁻¹ * x⁻¹ ∈ Y :=
        h ((MulAut.conj g).toMonoidHom s) (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hs)
      have hm' : (g : G)⁻¹ * ((g : G) * (s : G) * (g : G)⁻¹ * x *
          ((g : G) * (s : G) * (g : G)⁻¹)⁻¹ * x⁻¹) * (g : G) ∈ Y :=
        (Subgroup.mem_normalizer_iff''.mp hgY _).mp hm
      have e : (g : G)⁻¹ * ((g : G) * (s : G) * (g : G)⁻¹ * x *
          ((g : G) * (s : G) * (g : G)⁻¹)⁻¹ * x⁻¹) * (g : G)
          = (s : G) * ((g : G)⁻¹ * x * (g : G)) * (s : G)⁻¹ *
            ((g : G)⁻¹ * x * (g : G))⁻¹ := by
        group
      rw [e] at hm'
      exact hm'
    · show (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyD, h⟩ := (mem_liftFix_iff D Y S).1 hy
    refine (mem_liftFix_iff D Y _).2 ⟨conj_mem_D D Y g.2 hyD, fun t ht => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    have hm' : (g : G) * ((s : G) * y * (s : G)⁻¹ * y⁻¹) * (g : G)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hgY _).mp (h s hs)
    have e : (g : G) * ((s : G) * y * (s : G)⁻¹ * y⁻¹) * (g : G)⁻¹
        = (g : G) * (s : G) * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) *
          ((g : G) * (s : G) * (g : G)⁻¹)⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹ := by
      group
    rw [e] at hm'
    exact hm'

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Rung

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G}

theorem OuterS16Hyp.card_fusionOddCore_D (h : OuterS16Hyp G L z t T E Q x B β) :
    Nat.card ↥(fusionOddCore ↥(L ⊓ centralizer ({β} : Set G))) = 3 := by
  have hβL : β ∈ L := h.outerB.B_le h.outerB.beta_mem
  set D : Subgroup G := L ⊓ centralizer ({β} : Set G) with hDdef
  have hβD : β ∈ D := ⟨hβL, mem_centralizer_singleton_iff.2 rfl⟩
  have hβ3 := h.outerB.beta_order
  have hzp : Nat.card ↥(zpowers β) = 3 := by rw [Nat.card_zpowers, hβ3]
  have hle : Nat.card ↥(fusionOddCore ↥D) ≤ 3 := by
    have h1 : Nat.card ↥(fusionOddCoreOf D) ≤ Nat.card ↥(zpowers β) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion h.outerB.D_odd) (Subgroup.inclusion_injective _)
    rw [fusionOddCoreOf, Subgroup.card_map_of_injective D.subtype_injective, hzp] at h1
    exact h1
  have hge : 3 ≤ Nat.card ↥(fusionOddCore ↥D) := by
    set b : ↥D := ⟨β, hβD⟩ with hb
    have hb3 : orderOf b = 3 := by rw [← Subgroup.orderOf_coe]; exact hβ3
    have hcentral : ∀ y : ↥D, y * b = b * y := fun y =>
      Subtype.ext (mem_centralizer_singleton_iff.1 y.2.2)
    haveI : (zpowers b).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
      have : g * b ^ k * g⁻¹ = b ^ k := by
        have hc : Commute g b := hcentral g
        rw [(Commute.zpow_right hc k).eq]
        group
      rw [this]
      exact mem_zpowers_iff.2 ⟨k, rfl⟩
    have hodd : Odd (Nat.card ↥(zpowers b)) := by
      rw [Nat.card_zpowers, hb3]; exact ⟨1, rfl⟩
    have := Subgroup.card_le_of_le (le_fusionOddCore hodd)
    rwa [Nat.card_zpowers, hb3] at this
  omega

theorem OuterS16Hyp.card_D (h : OuterS16Hyp G L z t T E Q x B β) :
    Nat.card ↥(L ⊓ centralizer ({β} : Set G)) = 1080 := by
  obtain ⟨e⟩ := h.outerB.D_quot
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)))
  rw [Nat.card_congr e.toEquiv, h.card_fusionOddCore_D] at h1
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [h360] at h1
  omega

theorem OuterS16Hyp.inf_odd_le (h : OuterS16Hyp G L z t T E Q x B β) {y : G}
    (hyD : y ∈ L ⊓ centralizer ({β} : Set G))
    (hyO : y ∈ (fusionOddCore ↥(centralizer ({β} : Set G))).map
      (centralizer ({β} : Set G)).subtype) : y ∈ zpowers β := by
  set K : Subgroup G := centralizer ({β} : Set G) with hK
  set DK : Subgroup ↥K := (L ⊓ K).subgroupOf K with hDK
  let e : DK ≃* ↥(L ⊓ K) := Subgroup.subgroupOfEquivOfLe (inf_le_right : L ⊓ K ≤ K)
  have hmap : (fusionOddCore DK).map e.toMonoidHom = fusionOddCore ↥(L ⊓ K) :=
    map_fusionOddCore_mulEquiv e
  obtain ⟨o, ho, rfl⟩ := hyO
  have hoDK : o ∈ DK := Subgroup.mem_subgroupOf.2 hyD
  have h1 : (⟨o, hoDK⟩ : ↥DK) ∈ fusionOddCore ↥DK := mem_oddCore_of_mem_O DK ho
  have h2 : e ⟨o, hoDK⟩ ∈ fusionOddCore ↥(L ⊓ K) := hmap ▸ ⟨_, h1, rfl⟩
  exact h.outerB.D_odd ⟨e ⟨o, hoDK⟩, h2, rfl⟩

end CFSG.EvenSporadicStandard.Fin76b

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Cfg

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Prod

variable {S : Type} [Group S] [Finite S]

theorem card_sup_mul_card_inf (H K : Subgroup S) (hHK : H ≤ Subgroup.normalizer (K : Set S)) :
    Nat.card (H ⊔ K : Subgroup S) * Nat.card (H ⊓ K : Subgroup S) = Nat.card H * Nat.card K := by
  set G : Subgroup S := H ⊔ K with hG
  have hKn : (K.subgroupOf G).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
  have hHG : H ≤ G := le_sup_left
  have hKG : K ≤ G := le_sup_right
  have htop : H.subgroupOf G ⊔ K.subgroupOf G = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right H K hHK
    have hg : (g : S) ∈ (↑(H ⊔ K) : Set S) := g.2
    rw [hcoe] at hg
    obtain ⟨h, hh, k, hk, hhk⟩ := hg
    have hg' : g = ⟨h, hHG hh⟩ * ⟨k, hKG hk⟩ := Subtype.ext hhk.symm
    rw [hg']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (show (⟨h, hHG hh⟩ : G) ∈ H.subgroupOf G from hh))
      (Subgroup.mem_sup_right (show (⟨k, hKG hk⟩ : G) ∈ K.subgroupOf G from hk))
  have h1 := Subgroup.relIndex_sup_right (H := H.subgroupOf G) (K := K.subgroupOf G)
  rw [htop, Subgroup.relIndex_top_right] at h1
  have hKcard : Nat.card (K.subgroupOf G) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG).toEquiv
  have hHcard : Nat.card (H.subgroupOf G) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHG).toEquiv
  have hcap : Nat.card (K.subgroupOf G ⊓ H.subgroupOf G : Subgroup G) = Nat.card (H ⊓ K : Subgroup S) := by
    have : K.subgroupOf G ⊓ H.subgroupOf G = (K ⊓ H).subgroupOf G := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [this, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hHG)).toEquiv
  have h2 := Subgroup.index_mul_card (K.subgroupOf G)
  have h3 := Subgroup.relIndex_mul_card (H := K.subgroupOf G) (K := H.subgroupOf G)
  rw [hKcard] at h2
  rw [hcap, hHcard] at h3
  rw [← h1] at h3
  rw [← h2, ← h3]
  ring

end Prod

end CFSG.EvenSporadicStandard.Fin76b

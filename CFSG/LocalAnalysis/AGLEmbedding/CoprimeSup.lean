module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbedding

theorem le_of_le_sup_of_coprime_card {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    {X Y N : Subgroup G} [Y.Normal] (hX : IsPGroup p X) (hN : (Nat.card N).Coprime p)
    (h : X ≤ Y ⊔ N) : X ≤ Y := by
  set φ := QuotientGroup.mk' Y
  have hY : Y.map φ = ⊥ := (Subgroup.map_eq_bot_iff Y).mpr (by rw [QuotientGroup.ker_mk'])
  have h1 : X.map φ ≤ N.map φ := by
    calc X.map φ ≤ (Y ⊔ N).map φ := Subgroup.map_mono h
      _ = N.map φ := by rw [Subgroup.map_sup, hY, bot_sup_eq]
  have h2 : Nat.card (X.map φ) = 1 := by
    rcases (hX.map φ).card_eq_or_dvd with h3 | h3
    · exact h3
    · exact absurd ((h3.trans (Subgroup.card_dvd_of_le h1)).trans (N.card_map_dvd φ))
        ((Nat.Prime.coprime_iff_not_dvd hp.out).1 hN.symm)
  rw [← QuotientGroup.ker_mk' Y, ← Subgroup.map_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq _ h2

theorem le_of_le_sup_of_coprime_card_of_le {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {K X Y N : Subgroup G} (hXK : X ≤ K) (hYK : Y ≤ K) (hNK : N ≤ K)
    (hYn : (Y.subgroupOf K).Normal) (hX : IsPGroup p X) (hN : (Nat.card N).Coprime p)
    (h : X ≤ Y ⊔ N) : X ≤ Y := by
  have hX' : IsPGroup p (X.subgroupOf K) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hN' : (Nat.card (N.subgroupOf K)).Coprime p := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
  have h' : X.subgroupOf K ≤ Y.subgroupOf K ⊔ N.subgroupOf K := by
    rw [← Subgroup.subgroupOf_sup hYK hNK]
    exact Subgroup.comap_mono h
  have := hYn
  have h'' := le_of_le_sup_of_coprime_card hX' hN' h'
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (h'' (Subgroup.mem_subgroupOf.mpr hx :
    (⟨x, hXK hx⟩ : K) ∈ X.subgroupOf K))

end CFSG.AGLEmbedding

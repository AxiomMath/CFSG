module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

namespace CFSG.CGT.T75P

variable {G : Type} [Group G]

theorem exists_complement_of_coprime_index [Finite G] {H T K₀ : Subgroup G} (hTH : T ≤ H)
    (hK₀H : K₀ ≤ H) (hnorm : (T.subgroupOf H).Normal)
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTK : T ⊓ K₀ = ⊥)
    (hcop : Nat.Coprime ((T ⊔ K₀).relIndex H) (Nat.card T)) :
    ∃ K : Subgroup G, K ≤ H ∧ T ⊓ K = ⊥ ∧ T ⊔ K = H := by
  classical
  let N : Subgroup ↥H := T.subgroupOf H
  let K' : Subgroup ↥H := K₀.subgroupOf H
  let P : Subgroup ↥H := (T ⊔ K₀).subgroupOf H
  have : N.Normal := hnorm
  have : IsMulCommutative N := ⟨⟨fun a b => by
    have ha : (a : ↥H).1 ∈ T := Subgroup.mem_subgroupOf.1 a.2
    have hb : (b : ↥H).1 ∈ T := Subgroup.mem_subgroupOf.1 b.2
    exact Subtype.ext (Subtype.ext (hTab _ ha _ hb))⟩⟩
  have hsup : N ⊔ K' = P := (Subgroup.subgroupOf_sup hTH hK₀H).symm
  have hNK : N ⊓ K' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    have h1 : (x : G) ∈ T := Subgroup.mem_subgroupOf.1 hx1
    have h2 : (x : G) ∈ K₀ := Subgroup.mem_subgroupOf.1 hx2
    have h3 : (x : G) ∈ T ⊓ K₀ := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [hTK, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.2 (Subtype.ext h3)
  have hcardN : Nat.card N = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hcop' : Nat.Coprime P.index (Nat.card N) := by
    rw [hcardN]
    exact hcop
  obtain ⟨D, -, hD1, hD2⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N P K' hcop' hNK hsup
  have hNmap : N.map H.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hTH
  refine ⟨D.map H.subtype, Subgroup.map_subtype_le D, ?_, ?_⟩
  · rw [← hNmap, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective, hD1, Subgroup.map_bot]
  · rw [← hNmap, ← Subgroup.map_sup, hD2, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.CGT.T75P

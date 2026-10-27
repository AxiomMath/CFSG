module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveModel

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

namespace FiveData

variable {G : Type} [Group G] [Finite G] (d : FiveData G)

include d

theorem disjoint_x₁_D : Disjoint (zpowers d.x₁) d.D := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsimple := d.D_simple
  have hx1D : d.x₁ ∉ d.D := by
    intro hx
    let N : Subgroup d.D := (zpowers d.x₁).subgroupOf d.D
    have hN : N.Normal := ⟨fun n hn g => by
      have hn' : (n : G) ∈ zpowers d.x₁ := hn
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hn'
      have hc : Commute (g : G) d.x₁ := mem_centralizer_singleton_iff.1 (d.D_le g.2)
      show ((g * n * g⁻¹ : d.D) : G) ∈ zpowers d.x₁
      have : ((g * n * g⁻¹ : d.D) : G) = n := by
        change (g : G) * n * (g : G)⁻¹ = n
        rw [← hk, (hc.zpow_right k).eq, mul_inv_cancel_right]
      rw [this, ← hk]
      exact zpow_mem (mem_zpowers _) k⟩
    have : N.Normal := hN
    rcases hsimple.eq_bot_or_eq_top_of_normal N with h | h
    · have hmem : (⟨d.x₁, hx⟩ : d.D) ∈ N := mem_zpowers _
      rw [h, Subgroup.mem_bot] at hmem
      have h0 : d.x₁ = 1 := by simpa using congrArg Subtype.val hmem
      have h1 : orderOf d.x₁ = 1 := by rw [h0, orderOf_one]
      rw [d.x₁_order] at h1
      omega
    · have hle : Nat.card N ≤ Nat.card (zpowers d.x₁) :=
        Nat.card_le_card_of_injective (fun n => ⟨(n : G), n.2⟩) (by
          intro a b hab
          have h := congrArg (fun z : zpowers d.x₁ => (z : G)) hab
          exact Subtype.ext (Subtype.ext h))
      rw [Nat.card_zpowers, d.x₁_order] at hle
      have h60 : Nat.card N = 60 := by rw [h, Subgroup.card_top]; exact d.card_D
      omega
  rw [Subgroup.disjoint_def]
  intro g hg1 hg2
  by_contra hg
  have hdvd : orderOf g ∣ 5 := by
    have := Subgroup.orderOf_dvd_natCard (zpowers d.x₁) hg1
    rwa [Nat.card_zpowers, d.x₁_order] at this
  have hord : orderOf g = 5 := by
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg
    · exact h
  have hz : zpowers g = zpowers d.x₁ := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact zpowers_le.2 hg1
    · rw [Nat.card_zpowers, Nat.card_zpowers, hord, d.x₁_order]
  apply hx1D
  have : d.x₁ ∈ zpowers g := hz ▸ mem_zpowers d.x₁
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 this
  rw [← hk]
  exact zpow_mem hg2 k

theorem centralizer_x₁_eq : centralizer ({d.x₁} : Set G) = zpowers d.x₁ ⊔ d.D := by
  have hdisj := d.disjoint_x₁_D
  have hle : zpowers d.x₁ ⊔ d.D ≤ centralizer ({d.x₁} : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) d.D_le
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  have hinj : Function.Injective (fun p : zpowers d.x₁ × d.D =>
      (⟨(p.1 : G) * p.2, mul_mem_sup p.1.2 p.2.2⟩ : ↥(zpowers d.x₁ ⊔ d.D))) := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    have h0 : (u : G) * v = u' * v' := congrArg Subtype.val h
    have h1 : (u' : G)⁻¹ * u = v' * (v : G)⁻¹ := by
      calc (u' : G)⁻¹ * u = (u' : G)⁻¹ * (u * v) * (v : G)⁻¹ := by group
        _ = (u' : G)⁻¹ * (u' * v') * (v : G)⁻¹ := by rw [h0]
        _ = v' * (v : G)⁻¹ := by group
    have h2 : (u' : G)⁻¹ * u ∈ zpowers d.x₁ := mul_mem (inv_mem u'.2) u.2
    have h3 : (u' : G)⁻¹ * u ∈ d.D := by rw [h1]; exact mul_mem v'.2 (inv_mem v.2)
    have h4 : (u' : G)⁻¹ * u = 1 := Subgroup.disjoint_def.1 hdisj h2 h3
    have hu : (u : G) = u' := (inv_mul_eq_one.1 h4).symm
    have hv : (v : G) = v' := by
      rw [hu] at h0
      exact mul_left_cancel h0
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hv)
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_zpowers, d.x₁_order, d.card_D] at this
  rw [d.card_C₁]
  omega

@[expose] def S₁ : Subgroup G := zpowers d.x₁ ⊔ zpowers d.y

omit [Finite G] in
theorem S₁_le_centralizer : d.S₁ ≤ centralizer ({d.x₁} : Set G) :=
  sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 d.y_comm))

omit [Finite G] in
theorem S₁_le_Q : d.S₁ ≤ (d.Q : Subgroup G) :=
  sup_le (zpowers_le.2 d.x₁_mem) (zpowers_le.2 d.y_mem)

theorem card_S₁ : Nat.card d.S₁ = 25 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : IsPGroup 5 d.S₁ := d.Q.isPGroup'.to_le d.S₁_le_Q
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  have hdvd : Nat.card d.S₁ ∣ 300 :=
    d.card_C₁ ▸ Subgroup.card_dvd_of_le d.S₁_le_centralizer
  have hk2 : k ≤ 2 := by
    by_contra h
    have h3 : 5 ^ 3 ∣ 5 ^ k := pow_dvd_pow 5 (by omega)
    rw [← hk] at h3
    have := h3.trans hdvd
    norm_num at this
  have hk2' : 2 ≤ k := by
    by_contra h
    have hcard5 : Nat.card d.S₁ ≤ 5 := by
      rw [hk]
      calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 5 := by norm_num
    have heq : zpowers d.x₁ = d.S₁ :=
      Subgroup.eq_of_le_of_card_ge (le_sup_left : zpowers d.x₁ ≤ d.S₁)
        (by rw [Nat.card_zpowers, d.x₁_order]; exact hcard5)
    apply d.y_not_mem
    rw [heq]
    exact (le_sup_right : zpowers d.y ≤ d.S₁) (mem_zpowers d.y)
  rw [hk, le_antisymm hk2 hk2']
  norm_num

omit [Finite G] in
theorem mem_zpowers_y_of_mem_S₁ {s : G} (hs : s ∈ d.S₁) (hs1 : s ≠ 1)
    (hc : Nat.card (centralizer ({s} : Set G)) = 1000) : s ∈ zpowers d.y :=
  d.y_unique s (d.S₁_le_Q hs) hs1
    (mem_centralizer_singleton_iff.1 (d.S₁_le_centralizer hs)) hc

end FiveData

end CFSG.EvenSporadicStandard.RuStd.S2

module

public import CFSG.GH74.Generic.S45.GLevel2
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem false_of_normal_index_two (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    {N : Subgroup G} (hN : N.Normal) (hi : N.index = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, Subgroup.index_bot] at hi
    have hcyc : IsCyclic G := isCyclic_of_prime_card hi
    obtain ⟨a, b, hab⟩ := hn
    exact hab (@mul_comm G (IsCyclic.commGroup (α := G)).toCommMagma a b)
  · rw [h, Subgroup.index_top] at hi
    omega

variable {x : G} {S₀ R₀ : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem Conf2.fusion_iff (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hx : orderOf x = 2) (hc : Conf2 S₀ R₀ T)
    (h315 : ∀ A' : Subgroup (MulAut ↥T), Nat.card ↥A' ≠ 315) :
    ∀ t ∈ T, (∃ g : G, g * x * g⁻¹ = t) ↔ t ∉ Rg x R₀ T := by
  obtain ⟨hfus1, hfus2, -, hidx⟩ := fusion_step hs hn hx hc h315
  have hxT : x ∈ T := hc.lift.x_mem hx
  have hab : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht => hc.lift.comm hc.S_comm hs ht
  intro t ht
  constructor
  · rintro ⟨g, rfl⟩ hR
    obtain ⟨n, hnN, hnx⟩ := exists_mem_normalizer_conj_eq hc.lift.sylow hxT hab ht
    have h1 := hfus1 n hnN
    rw [hnx] at h1
    have h2 : x⁻¹ ∈ Rg x R₀ T := by
      have h3 : x⁻¹ = (x⁻¹ * (g * x * g⁻¹)) * (g * x * g⁻¹)⁻¹ := by group
      rw [h3]
      exact mul_mem h1 (inv_mem hR)
    apply hc.x_not_Rg
    have := inv_mem h2
    rwa [inv_inv] at this
  · intro htR
    obtain ⟨n, -, hn'⟩ := hfus2 (x⁻¹ * t) (hidx t ht htR)
    refine ⟨n, ?_⟩
    rw [hn']
    group

theorem Conf2.not_isSylowOf_top (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hx : orderOf x = 2) (hc : Conf2 S₀ R₀ T)
    (h315 : ∀ A' : Subgroup (MulAut ↥T), Nat.card ↥A' ≠ 315) : ¬ IsSylowOf 2 T ⊤ := by
  intro hT
  have hfus := hc.fusion_iff hs hn hx h315
  have hxT : x ∈ T := hc.lift.x_mem hx
  have hTS := isSylowOf_iff.1 hT
  have hTidx : ¬ 2 ∣ T.index := by
    have := hTS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hUidx : (Rg x R₀ T).relIndex T = 2 := by
    have h1 := Subgroup.card_mul_index ((Rg x R₀ T).subgroupOf T)
    have h2 : Nat.card ↥((Rg x R₀ T).subgroupOf T) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Rg_le).toEquiv]
      exact hc.card_Rg
    have hcardT : Nat.card ↥T = 16 := hc.lift.card_eq.trans hc.S_card
    rw [h2, hcardT] at h1
    show ((Rg x R₀ T).subgroupOf T).index = 2
    omega
  have hmin : ∀ y ∈ T, y ∉ Rg x R₀ T → orderOf x ≤ orderOf y := by
    intro y hy hyR
    have hy1 : y ≠ 1 := fun h => hyR (h ▸ one_mem _)
    have hyy : y ^ 2 = 1 := by rw [pow_two]; exact hc.lift.sq_eq_one hc.S_sq hy
    have : orderOf y = 2 := orderOf_eq_prime hyy hy1
    rw [hx, this]
  have hconj : ∀ g : G, g⁻¹ * x * g ∉ Rg x R₀ T := by
    intro g hg
    have hgT : g⁻¹ * x * g ∈ T := Rg_le hg
    have hy : (∃ g' : G, g' * x * g'⁻¹ = g⁻¹ * x * g) :=
      ⟨g⁻¹, by rw [inv_inv]⟩
    exact ((hfus _ hgT).1 hy) hg
  obtain ⟨N, hN, hidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hTS.2.1 hTidx
    Rg_le hUidx hxT hc.x_not_Rg hmin hconj
  exact false_of_normal_index_two hs hn hN hidx

end CFSG.GH74.Generic.S45

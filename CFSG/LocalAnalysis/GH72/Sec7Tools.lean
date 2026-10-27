module

public import CFSG.LocalAnalysis.GH72.Sec4Basic

public section

namespace CFSG.GH72

open Subgroup

namespace Sec7

variable {G : Type*} [Group G]

theorem O_le (H : Subgroup G) : O H ≤ H := map_subtype_le _

theorem normalizer_le_normalizer_O [Finite G] (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (O H : Set G) := by
  intro s hs
  let φ : MulAut H := H.normalizerMonoidHom ⟨s, hs⟩
  have hle : (CFSG.oddCore H).map φ.toMonoidHom ≤ CFSG.oddCore H :=
    CFSG.ABGLocalTools.le_oddCore_of_normal ((CFSG.oddCore_normal H).map _ φ.surjective)
      (by
        rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
        exact CFSG.ABGLocalTools.odd_card_oddCore)
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have hφy : φ y ∈ CFSG.oddCore H := hle ⟨y, hy, rfl⟩
  exact ⟨φ y, hφy, rfl⟩

theorem le_O_of_normal [Finite G] {N H : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hodd : Odd (Nat.card N)) : N ≤ O H := by
  have h : N.subgroupOf H ≤ CFSG.oddCore H :=
    CFSG.ABGLocalTools.le_oddCore_of_normal hN
      (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv])
  intro x hx
  exact ⟨⟨x, hNH hx⟩, h hx, rfl⟩

theorem O_le_O_of_normal [Finite G] {C K : Subgroup G} (hCK : C ≤ K)
    (hC : (C.subgroupOf K).Normal) : O C ≤ O K := by
  have hKC : K ≤ normalizer (C : Set G) := (normal_subgroupOf_iff_le_normalizer hCK).mp hC
  refine le_O_of_normal ((O_le C).trans hCK)
    ((normal_subgroupOf_iff_le_normalizer ((O_le C).trans hCK)).mpr
      (hKC.trans (normalizer_le_normalizer_O C))) (card_O_odd C)

section SimplePerfect

variable {L : Type*} [Group L] [IsSimpleGroup L]

theorem exists_mul_ne_of_perfect (hL : commutator L = ⊤) : ∃ a b : L, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hbot : commutator L = ⊥ := by
    rw [_root_.commutator_def, eq_bot_iff, commutator_le]
    intro a _ b _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  obtain ⟨x, y, hxy⟩ := IsSimpleGroup.toNontrivial (G := L) |>.exists_pair_ne
  have : (⊤ : Subgroup L) = ⊥ := hL.symm.trans hbot
  exact hxy ((Subgroup.eq_bot_iff_forall _).mp this _ (mem_top x) ▸
    ((Subgroup.eq_bot_iff_forall _).mp this _ (mem_top y)).symm)

theorem eq_bot_of_normal_of_comm (hL : commutator L = ⊤) {N : Subgroup L} (hN : N.Normal)
    (hc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := exists_mul_ne_of_perfect hL
    exact absurd (hc a (h ▸ mem_top a) b (h ▸ mem_top b)) hab

theorem eq_bot_of_normal_of_odd [Finite L] (hL : commutator L = ⊤) {N : Subgroup L}
    (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hoddL : Odd (Nat.card L) := by
      rw [h, card_top] at hodd
      exact hodd
    have : Group.IsSolvable L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddL
    have hne : (⊤ : Subgroup L) ≠ ⊥ := top_ne_bot
    have := (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne
    exact this (by rw [← _root_.commutator_def, hL])

end SimplePerfect

theorem commutator_mul_central {u₁ u₂ z₁ z₂ : G} (h₁₂ : Commute z₁ u₂) (h₂₁ : Commute z₂ u₁)
    (h : Commute z₁ z₂) :
    u₁ * z₁ * (u₂ * z₂) * (u₁ * z₁)⁻¹ * (u₂ * z₂)⁻¹ = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ := by
  have e1 : u₁ * z₁ * (u₂ * z₂) * (u₁ * z₁)⁻¹ * (u₂ * z₂)⁻¹ =
      u₁ * (z₁ * u₂) * z₂ * z₁⁻¹ * u₁⁻¹ * z₂⁻¹ * u₂⁻¹ := by group
  rw [e1, h₁₂.eq]
  have e2 : u₁ * (u₂ * z₁) * z₂ * z₁⁻¹ * u₁⁻¹ * z₂⁻¹ * u₂⁻¹ =
      u₁ * u₂ * (z₁ * z₂ * z₁⁻¹) * u₁⁻¹ * z₂⁻¹ * u₂⁻¹ := by group
  rw [e2, h.eq, mul_inv_cancel_right]
  have e3 : u₁ * u₂ * z₂ * u₁⁻¹ * z₂⁻¹ * u₂⁻¹ = u₁ * u₂ * (z₂ * u₁⁻¹) * z₂⁻¹ * u₂⁻¹ := by group
  rw [e3, (h₂₁.inv_right).eq]
  group

theorem commutator_le_of_forall_mul {H U : Subgroup G} (hUH : U ≤ H)
    (hdec : ∀ h ∈ H, ∃ u ∈ U, ∃ z ∈ H, (∀ k ∈ H, Commute z k) ∧ h = u * z) :
    ⁅H, H⁆ ≤ ⁅U, U⁆ := by
  rw [commutator_le]
  intro h₁ hh₁ h₂ hh₂
  obtain ⟨u₁, hu₁, z₁, hz₁, hc₁, rfl⟩ := hdec h₁ hh₁
  obtain ⟨u₂, hu₂, z₂, hz₂, hc₂, rfl⟩ := hdec h₂ hh₂
  have key := commutator_mem_commutator hu₁ hu₂
  rw [commutatorElement_def] at key ⊢
  rwa [commutator_mul_central (hc₁ _ (hUH hu₂)) (hc₂ _ (hUH hu₁)) (hc₁ _ hz₂)]

theorem surjective_of_ker_le {P L₁ L₂ : Type*} [Group P] [Finite P] [Group L₁] [Group L₂]
    [Finite L₁] (φ : P →* L₁) (ψ : P →* L₂) (hψ : Function.Surjective ψ)
    (hker : φ.ker ≤ ψ.ker) (hcard : Nat.card L₁ ≤ Nat.card L₂) : Function.Surjective φ := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective (f := φ.rangeRestrict)
    φ.rangeRestrict_surjective
  have h2 := Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψ
  rw [MonoidHom.ker_rangeRestrict] at h1
  have hk : Nat.card φ.ker ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hker
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hle : Nat.card L₂ ≤ Nat.card φ.range := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card φ.ker * Nat.card L₂ ≤ Nat.card ψ.ker * Nat.card L₂ :=
          Nat.mul_le_mul_right _ hk
      _ = Nat.card φ.ker * Nat.card φ.range := by rw [h2, h1]
  have htop : φ.range = ⊤ := Subgroup.eq_top_of_le_card _ (hcard.trans hle)
  exact MonoidHom.range_eq_top.mp htop

theorem le_of_normal_of_not_le {M₁ U : Subgroup G} {L : Type*} [Group L] [IsSimpleGroup L]
    (g : M₁ →* L) (hg : Function.Surjective g) (hker : g.ker = (O M₁).subgroupOf M₁)
    (hcen : O M₁ ≤ centralizer (M₁ : Set G)) (hperf : ⁅M₁, M₁⁆ = M₁) (hUM : U ≤ M₁)
    (hU : (U.subgroupOf M₁).Normal) (hUO : ¬ U ≤ O M₁) : M₁ ≤ U := by
  have htop : (U.subgroupOf M₁).map g = ⊤ := by
    have : ((U.subgroupOf M₁).map g).Normal := hU.map g hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((U.subgroupOf M₁).map g) with h | h
    · refine absurd (fun u hu => ?_) hUO
      have h1 : g ⟨u, hUM hu⟩ = 1 := by
        rw [← mem_bot, ← h]
        exact mem_map_of_mem g (show (⟨u, hUM hu⟩ : M₁) ∈ U.subgroupOf M₁ from hu)
      have h2 : (⟨u, hUM hu⟩ : M₁) ∈ g.ker := h1
      rw [hker] at h2
      exact h2
    · exact h
  have hdec : ∀ m ∈ M₁, ∃ u ∈ U, ∃ z ∈ M₁, (∀ k ∈ M₁, Commute z k) ∧ m = u * z := by
    intro m hm
    obtain ⟨x, hx, hxm⟩ := (htop ▸ mem_top (g ⟨m, hm⟩) : g ⟨m, hm⟩ ∈ (U.subgroupOf M₁).map g)
    have hz : (x : G)⁻¹ * m ∈ O M₁ := by
      have h1 : x⁻¹ * ⟨m, hm⟩ ∈ g.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxm, inv_mul_cancel]
      rw [hker] at h1
      exact h1
    refine ⟨x, hx, (x : G)⁻¹ * m, mul_mem (inv_mem x.2) hm, fun k hk => ?_, by group⟩
    exact (mem_centralizer_iff.mp (hcen hz) k hk).symm
  calc M₁ = ⁅M₁, M₁⁆ := hperf.symm
    _ ≤ ⁅U, U⁆ := commutator_le_of_forall_mul hUM hdec
    _ ≤ U := commutator_le_self U

end Sec7

end CFSG.GH72

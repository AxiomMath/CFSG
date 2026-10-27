module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Uniq

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mem_sup_of_pow_two_pow_eq_one {L₀ W : Subgroup G} (hWodd : Odd (Nat.card W))
    (hLW : L₀ ⊓ W = ⊥) (hWC : W ≤ centralizer (L₀ : Set G)) {x : G} (hx : x ∈ L₀ ⊔ W) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : x ∈ L₀ := by
  have hWN : W ≤ normalizer (L₀ : Set G) := fun w hw => mem_normalizer_iff.mpr fun h => by
    have hc := mem_centralizer_iff.mp (hWC hw)
    constructor
    · intro hh
      rw [← hc h hh, mul_inv_cancel_right]
      exact hh
    · intro hh
      have h1 := hc _ hh
      have h2 : h = w * h * w⁻¹ := by
        calc h = w⁻¹ * ((w * h * w⁻¹) * w) := by group
          _ = w⁻¹ * (w * (w * h * w⁻¹)) := by rw [h1]
          _ = w * h * w⁻¹ := by group
      rw [h2]
      exact hh
  obtain ⟨l, hl, w, hw, rfl⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer hWN hx
  have hlw : Commute l w := mem_centralizer_iff.mp (hWC hw) l hl
  rw [hlw.mul_pow, mul_eq_one_iff_eq_inv] at hxk
  have hw1 : w ^ 2 ^ k = 1 := by
    have h2 : w ^ 2 ^ k = (l ^ 2 ^ k)⁻¹ := (inv_eq_iff_eq_inv.mpr hxk).symm
    have hwL : w ^ 2 ^ k ∈ L₀ := by
      rw [h2]
      exact L₀.inv_mem (L₀.pow_mem hl _)
    have hmem : w ^ 2 ^ k ∈ L₀ ⊓ W := mem_inf.mpr ⟨hwL, W.pow_mem hw _⟩
    rwa [hLW, mem_bot] at hmem
  have hodd : Odd (orderOf w) := hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hw)
  have hdvd : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hw1
  have hcop : Nat.Coprime (orderOf w) (2 ^ k) :=
    Nat.Coprime.pow_right k hodd.coprime_two_right
  have h1 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [orderOf_eq_one_iff.mp h1, mul_one]
  exact hl

theorem isSylowOf_top_of_normalizer_le {L₀ W S₀ : Subgroup G} (hWodd : Odd (Nat.card W))
    (hLW : L₀ ⊓ W = ⊥) (hWC : W ≤ centralizer (L₀ : Set G)) (hS₀ : IsSylowOf 2 S₀ L₀)
    (hNS : normalizer (S₀ : Set G) ≤ L₀ ⊔ W) : IsSylowOf 2 S₀ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  obtain ⟨S, hS₀S, z, hzS, hzN, hzS₀⟩ := exists_mem_normalizer_of_not_isSylowOf hS₀.isPGroup hnot
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨z, hzS⟩
  have hzk : z ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hzL₀ : z ∈ L₀ := mem_of_mem_sup_of_pow_two_pow_eq_one hWodd hLW hWC (hNS hzN) hzk
  have heq := hS₀.eq_of_le (le_inf hS₀S hS₀.le) inf_le_right (S.isPGroup'.to_le inf_le_left)
  exact hzS₀ (heq ▸ ⟨hzS, hzL₀⟩)

theorem oddCoreIn_centralizer_eq {L₀ W S₀ : Subgroup G} (hWodd : Odd (Nat.card W))
    (hWC : W ≤ centralizer (L₀ : Set G)) (hS₀L₀ : S₀ ≤ L₀)
    (hCW : centralizer (S₀ : Set G) ≤ normalizer (W : Set G))
    (hY : ∀ Y : Subgroup G, Odd (Nat.card Y) → S₀ ≤ normalizer (Y : Set G) → Y ≤ W) :
    AS76b.oddCoreIn (centralizer (S₀ : Set G)) = W := by
  set C := centralizer (S₀ : Set G) with hC
  have hS₀C : S₀ ≤ normalizer (C : Set G) := fun s hs => mem_normalizer_iff.mpr fun c => by
    rw [hC, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro h u hu
      have h1 := h (s⁻¹ * u * s) (by
        have := (mem_normalizer_iff.mp (le_normalizer (inv_mem hs)) u)
        exact S₀.mul_mem (S₀.mul_mem (inv_mem hs) hu) hs)
      calc u * (s * c * s⁻¹) = s * ((s⁻¹ * u * s) * c) * s⁻¹ := by group
        _ = s * (c * (s⁻¹ * u * s)) * s⁻¹ := by rw [h1]
        _ = s * c * s⁻¹ * u := by group
    · intro h u hu
      have h1 := h (s * u * s⁻¹) (S₀.mul_mem (S₀.mul_mem hs hu) (inv_mem hs))
      calc u * c = s⁻¹ * ((s * u * s⁻¹) * (s * c * s⁻¹)) * s := by group
        _ = s⁻¹ * ((s * c * s⁻¹) * (s * u * s⁻¹)) * s := by rw [h1]
        _ = c * u := by group
  refine le_antisymm (hY _ (AS76b.odd_card_oddCoreIn C)
    (hS₀C.trans (AS76b.normalizer_le_normalizer_oddCoreIn C))) ?_
  have hWC' : W ≤ C := hWC.trans (centralizer_le hS₀L₀)
  have hn : (W.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hWC').mpr hCW
  have hodd' : Odd (Nat.card (W.subgroupOf C)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hWC').toEquiv]
  have h := AS76b.le_assemblyOddCore hn hodd'
  intro x hx
  exact ⟨⟨x, hWC' hx⟩, h hx, rfl⟩

theorem normalizer_le_sup {L₀ W S₀ : Subgroup G} (hWodd : Odd (Nat.card W))
    (hWC : W ≤ centralizer (L₀ : Set G)) (hS₀L₀ : S₀ ≤ L₀)
    (hCW : centralizer (S₀ : Set G) ≤ normalizer (W : Set G))
    (hY : ∀ Y : Subgroup G, Odd (Nat.card Y) → S₀ ≤ normalizer (Y : Set G) → Y ≤ W)
    (hNW : normalizer (W : Set G) ≤ L₀ ⊔ W) : normalizer (S₀ : Set G) ≤ L₀ ⊔ W := by
  have hNC : normalizer (S₀ : Set G) ≤ normalizer (centralizer (S₀ : Set G) : Set G) :=
    fun n hn => mem_normalizer_iff.mpr fun c => by
      rw [mem_centralizer_iff, mem_centralizer_iff]
      constructor
      · intro h u hu
        have h1 := h (n⁻¹ * u * n) (by
          have := (mem_normalizer_iff.mp (inv_mem hn) u).mp hu
          simpa using this)
        calc u * (n * c * n⁻¹) = n * ((n⁻¹ * u * n) * c) * n⁻¹ := by group
          _ = n * (c * (n⁻¹ * u * n)) * n⁻¹ := by rw [h1]
          _ = n * c * n⁻¹ * u := by group
      · intro h u hu
        have h1 := h (n * u * n⁻¹) ((mem_normalizer_iff.mp hn u).mp hu)
        calc u * c = n⁻¹ * ((n * u * n⁻¹) * (n * c * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * c * n⁻¹) * (n * u * n⁻¹)) * n := by rw [h1]
          _ = c * u := by group
  have h := hNC.trans (AS76b.normalizer_le_normalizer_oddCoreIn _)
  rw [oddCoreIn_centralizer_eq hWodd hWC hS₀L₀ hCW hY] at h
  exact h.trans hNW

namespace SzMinCounter

theorem isSylowOf_top_of_isSylowOf
    {L T : Subgroup G} (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) {L₀ : Subgroup G}
    (hLW : L₀ ⊓ AS76b.oddCoreIn (centralizer (L : Set G)) = ⊥)
    (hWC : AS76b.oddCoreIn (centralizer (L : Set G)) ≤ centralizer (L₀ : Set G))
    (hNW : normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) ≤
      L₀ ⊔ AS76b.oddCoreIn (centralizer (L : Set G)))
    (hCt : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G))
    {S₀ : Subgroup G} (hS₀ : IsSylowOf 2 S₀ L₀) (hTS₀ : T ≤ S₀) : IsSylowOf 2 S₀ ⊤ := by
  set W := AS76b.oddCoreIn (centralizer (L : Set G)) with hWdef
  have hWodd : Odd (Nat.card W) := AS76b.odd_card_oddCoreIn _
  obtain ⟨t, ht, ht1⟩ : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : T ⊓ centralizer (L : Set G) = ⊥ := (eq_bot_iff_forall _).mpr hcon
    rw [hbot, card_bot] at h4
    norm_num at h4
  have hCW : centralizer (S₀ : Set G) ≤ normalizer (W : Set G) := fun c hc =>
    hCt t ht ht1 (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hc t (hTS₀ ht.1)).symm)
  have hVS : gmsV L T ≤ S₀ := (sup_le (inf_le_left.trans inf_le_left) inf_le_left).trans hTS₀
  have hY : ∀ Y : Subgroup G, Odd (Nat.card Y) → S₀ ≤ normalizer (Y : Set G) → Y ≤ W :=
    fun Y hYodd hS₀Y => hM.le_oddCoreIn_of_le_normalizer_gmsV h3 hF hZ h4 hYodd (hVS.trans hS₀Y)
  exact isSylowOf_top_of_normalizer_le hWodd hLW hWC hS₀
    (normalizer_le_sup hWodd hWC hS₀.le hCW hY hNW)

end SzMinCounter

end CFSG.ComponentClassification.GMS78

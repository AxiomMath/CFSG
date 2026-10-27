module

public import CFSG.ClassicalInvolution.Q3.Q3SSylow
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution

theorem isSubnormal_sup_of_normal {G : Type*} [Group G] {H K N : Subgroup G}
    (h : IsSubnormal H K) (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal) :
    IsSubnormal (H ⊔ N) K := by
  induction h with
  | refl =>
    rw [sup_eq_left.mpr hNK]
    exact IsSubnormal.refl _
  | @step H M K hHM hHN hMK ih =>
    have hMK' : M ≤ K := isSubnormal_le hMK
    have hconjN : ∀ m ∈ K, ∀ n ∈ N, m * n * m⁻¹ ∈ N := fun m hm n hn =>
      (Subgroup.normal_subgroupOf_iff hNK).1 hN n m hn hm
    have hconjH : ∀ m ∈ M, ∀ x ∈ H, m * x * m⁻¹ ∈ H := fun m hm x hx =>
      (Subgroup.normal_subgroupOf_iff hHM).1 hHN x m hx hm
    have hnorm : ∀ m ∈ M, ∀ y ∈ H ⊔ N, m * y * m⁻¹ ∈ H ⊔ N := by
      intro m hm y hy
      have hy' : y ∈ Subgroup.closure ((H : Set G) ∪ (N : Set G)) := by
        rwa [← Subgroup.sup_eq_closure]
      clear hy
      induction hy' using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · exact Subgroup.mem_sup_left (hconjH m hm x hx)
        · exact Subgroup.mem_sup_right (hconjN m (hMK' hm) x hx)
      | one => simp
      | mul x y _ _ hx hy =>
        have : m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
        rw [this]
        exact (H ⊔ N).mul_mem hx hy
      | inv x _ hx =>
        have : m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
        rw [this]
        exact (H ⊔ N).inv_mem hx
    have hMT : M ≤ Subgroup.normalizer (((H ⊔ N : Subgroup G)) : Set G) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hnorm m hm y hy, fun hy => ?_⟩
      have := hnorm m⁻¹ (M.inv_mem hm) _ hy
      simpa [mul_assoc] using this
    have hNT : N ≤ Subgroup.normalizer (((H ⊔ N : Subgroup G)) : Set G) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hnS : n ∈ H ⊔ N := Subgroup.mem_sup_right hn
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      · exact (H ⊔ N).mul_mem ((H ⊔ N).mul_mem hnS hy) ((H ⊔ N).inv_mem hnS)
      · have := (H ⊔ N).mul_mem ((H ⊔ N).mul_mem ((H ⊔ N).inv_mem hnS) hy) hnS
        simpa [mul_assoc] using this
    have hT : M ⊔ N ≤ Subgroup.normalizer (((H ⊔ N : Subgroup G)) : Set G) := sup_le hMT hNT
    refine IsSubnormal.step (sup_le_sup_right hHM N) ?_ (ih hNK hN)
    rw [Subgroup.normal_subgroupOf_iff (sup_le_sup_right hHM N)]
    intro y x hy hx
    exact (Subgroup.mem_normalizer_iff.1 (hT hx) y).1 hy

section Normal

variable {G : Type} [Group G] [Finite G] {z : G} {L N : Subgroup G} [N.Normal]

theorem IsClassicalMember3.nine_dvd_card_sup (hL : IsClassicalMember3 L z)
    (hNodd : Odd (Nat.card N)) (hN3 : 3 ∣ Nat.card N) : 9 ∣ Nat.card (L ⊔ N : Subgroup G) := by
  have hmap : (N.subgroupOf L).map L.subtype = N ⊓ L := Subgroup.subgroupOf_map_subtype N L
  have hcard_a : Nat.card (N.subgroupOf L) ∣ Nat.card N := by
    have h1 : Nat.card ((N.subgroupOf L).map L.subtype) = Nat.card (N.subgroupOf L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [← h1, hmap]
    exact Subgroup.card_dvd_of_le inf_le_left
  have haodd : Odd (Nat.card (N.subgroupOf L)) := hNodd.of_dvd_nat hcard_a
  have hle : N.subgroupOf L ≤ classicalInvolutionOddCore L :=
    le_sSup ⟨Subgroup.normal_subgroupOf, haodd⟩
  obtain ⟨q, hq⟩ : Nat.card (N.subgroupOf L) ∣ Nat.card (classicalInvolutionOddCore L) :=
    Subgroup.card_dvd_of_le hle
  have hLi := Subgroup.card_mul_index (N.subgroupOf L)
  have hapos : 0 < Nat.card (N.subgroupOf L) := Nat.card_pos
  have h24 : (N.subgroupOf L).index = 24 * q := by
    have h1 : Nat.card (N.subgroupOf L) * (N.subgroupOf L).index =
        Nat.card (N.subgroupOf L) * (24 * q) := by
      rw [hLi, hL.card_eq, hq]
      ring
    exact Nat.eq_of_mul_eq_mul_left hapos h1
  have hrel : N.relIndex (L ⊔ N) = N.relIndex L := Subgroup.relIndex_sup_right L N
  have hLN := Subgroup.card_mul_index (N.subgroupOf (L ⊔ N))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ L ⊔ N)).toEquiv] at hLN
  have : Nat.card (L ⊔ N : Subgroup G) = Nat.card N * (24 * q) := by
    rw [← hLN]
    change Nat.card N * N.relIndex (L ⊔ N) = _
    rw [hrel]
    change Nat.card N * (N.subgroupOf L).index = _
    rw [h24]
  rw [this]
  obtain ⟨c, hc⟩ := hN3
  rw [hc]
  exact ⟨c * (8 * q), by ring⟩

variable (hz : ∀ g : G, g * z = z * g)

include hz in
theorem IsClassicalMember3.mem_sup_of_pow_three_eq_one (hL : IsClassicalMember3 L z)
    (hNodd : Odd (Nat.card N)) (hN3 : 3 ∣ Nat.card N) (h27 : ¬ 27 ∣ Nat.card G) {x : G}
    (hx : x ^ 3 = 1) : x ∈ L ⊔ N := by
  have hC : Subgroup.centralizer ({z} : Set G) = ⊤ :=
    eq_top_iff.2 fun g _ => Subgroup.mem_centralizer_singleton_iff.2 (hz g)
  have hsub : IsSubnormal L ⊤ := by
    have := hL.subnormal
    rwa [hC] at this
  have hsub' : IsSubnormal (L ⊔ N) ⊤ :=
    isSubnormal_sup_of_normal hsub le_top Subgroup.normal_subgroupOf
  have h9 := hL.nine_dvd_card_sup hNodd hN3
  have hidx : ¬ 3 ∣ (L ⊔ N).relIndex ⊤ := by
    intro hd
    apply h27
    have h1 := Subgroup.card_mul_index (L ⊔ N)
    rw [← h1]
    obtain ⟨a, ha⟩ := h9
    have hd' : 3 ∣ (L ⊔ N).index := by
      have : (L ⊔ N).relIndex ⊤ = (L ⊔ N).index := Subgroup.relIndex_top_right (L ⊔ N)
      rwa [this] at hd
    obtain ⟨b, hb⟩ := hd'
    rw [ha, hb]
    exact ⟨a * b, by ring⟩
  exact isSubnormal_mem_of_pow_eq_one hsub' Nat.prime_three hidx (Subgroup.mem_top x)
    (k := 1) (by simpa using hx)

include hz in
theorem IsClassicalMember3.eq_of_mem_sup (hL : IsClassicalMember3 L z)
    (hNodd : Odd (Nat.card N)) {t : G} (ht : t ∈ L ⊔ N) (ht2 : orderOf t = 2) : t = z := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hodd : ∀ n : G, n ∈ N → Odd (orderOf n) := fun n hn => by
    have := hNodd.of_dvd_nat (orderOf_dvd_natCard (⟨n, hn⟩ : N))
    rwa [Subgroup.orderOf_mk] at this
  have hNbot : N.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  have hmap : (L ⊔ N).map π = L.map π := by
    rw [Subgroup.map_sup, hNbot, sup_bot_eq]
  obtain ⟨l, hlL, hl⟩ := Subgroup.mem_map.1 (hmap ▸ Subgroup.mem_map_of_mem π ht)
  have hsq : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have hπt : π t ≠ 1 := fun h1 => by
    have := hodd t ((QuotientGroup.eq_one_iff t).1 h1)
    rw [ht2] at this
    exact absurd this (by decide)
  have hπl2 : π l * π l = 1 := by
    rw [hl, ← map_mul, hsq, map_one]
  have hπlne : π l ≠ 1 := by rw [hl]; exact hπt
  have hord_πl : orderOf (π l) = 2 := orderOf_eq_prime (by rwa [pow_two]) hπlne
  have h2dvd : 2 ∣ orderOf l := hord_πl ▸ orderOf_map_dvd π l
  have hl2N : l ^ 2 ∈ N := by
    have : π (l ^ 2) = 1 := by rw [map_pow, pow_two, hπl2]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hodd2 : Odd (orderOf (l ^ 2)) := hodd _ hl2N
  have hl0 : orderOf l ≠ 0 := (orderOf_pos l).ne'
  have hord2 : orderOf (l ^ 2) = orderOf l / 2 := orderOf_pow_of_dvd (by norm_num) h2dvd
  rw [hord2] at hodd2
  set m := orderOf l / 2 with hm
  have hmo : orderOf l = 2 * m := by omega
  have hm0 : m ≠ 0 := by omega
  have hmdvd : m ∣ orderOf l := ⟨2, by omega⟩
  have hlm : orderOf (l ^ m) = 2 := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hmo]
    exact Nat.mul_div_cancel 2 (Nat.pos_of_ne_zero hm0)
  have hlz : l ^ m = z := hL.eq_of_orderOf_eq_two (L.pow_mem hlL m) hlm
  have hπz : π z = π t := by
    rw [← hlz, map_pow, ← hl]
    obtain ⟨k, hk⟩ := hodd2
    rw [hk, pow_succ, pow_mul, pow_two, hπl2, one_pow, one_mul]
  have hzt : z⁻¹ * t ∈ N := QuotientGroup.eq.1 hπz
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hL.orderOf_eq_two, pow_two] at this
  have hcomm : Commute z⁻¹ t := by
    have : Commute z t := (hz t).symm
    exact this.inv_left
  have hpow : (z⁻¹ * t) ^ 2 = 1 := by
    rw [hcomm.mul_pow, pow_two, pow_two, hsq, mul_one, ← mul_inv_rev, hz2, inv_one]
  have hdvd : orderOf (z⁻¹ * t) ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
  have hodd3 := hodd _ hzt
  have h1 : orderOf (z⁻¹ * t) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd3
      exact absurd hodd3 (by decide)
  have h3 : z⁻¹ * t = 1 := orderOf_eq_one_iff.mp h1
  exact (inv_mul_eq_one.mp h3).symm

include hz in
theorem NoWeakClassical3At.of_witness_normal (hNodd : Odd (Nat.card N)) (hN3 : 3 ∣ Nat.card N)
    (h27 : ¬ 27 ∣ Nat.card G) {g₁ g₂ : G} (hg₁ : g₁ ^ 3 = 1) (hg₂ : g₂ ^ 3 = 1)
    (ht : (g₁ * g₂) ^ 2 = 1) (ht1 : g₁ * g₂ ≠ 1) (htz : g₁ * g₂ ≠ z) : NoWeakClassical3At z := by
  intro L hL
  have h1 := hL.mem_sup_of_pow_three_eq_one hz hNodd hN3 h27 hg₁
  have h2 := hL.mem_sup_of_pow_three_eq_one hz hNodd hN3 h27 hg₂
  exact htz (hL.eq_of_mem_sup hz hNodd ((L ⊔ N).mul_mem h1 h2) (orderOf_eq_prime ht ht1))

end Normal

end CFSG.ClassicalInvolution.Q3

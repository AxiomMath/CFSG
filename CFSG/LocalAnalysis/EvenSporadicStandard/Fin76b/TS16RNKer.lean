module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RCtx
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RNW

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem s16_comm_gen_eq_one_or_t {G : Type} [Group G] {s z t y : G} (hz2 : z * z = 1)
    (hzs : z * s * z⁻¹ = s⁻¹) (hs8 : s ^ 8 = 1) (hord : orderOf s = 8) (hs4 : s ^ 4 = t)
    (hy : ∃ i j : ℕ, y = s ^ i * z ^ j) (hyA : y * (s * s) = (s * s) * y)
    (hyB : y * (s * z) = (s * z) * y) : y = 1 ∨ y = t := by
  have ht2 : t * t = 1 := by
    rw [← hs4, ← pow_add]
    exact hs8
  obtain ⟨i, j, rfl⟩ := hy
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
  ·
    rw [z_pow_two_mul hz2 r, mul_one] at hyB ⊢
    have h1 : s ^ i * (s * z) = s ^ (i + 1) * z := by
      rw [pow_succ, mul_assoc]
    have h2 : s * z * s ^ i = s ^ (7 * i + 1) * z := by
      rw [mul_assoc, z_mul_pow_s hz2 hzs hs8 i, ← mul_assoc, ← pow_succ']
    rw [h1, h2] at hyB
    have h3 : s ^ (i + 1) * s ^ (6 * i) = s ^ (i + 1) * 1 := by
      rw [mul_one, ← pow_add, show i + 1 + 6 * i = 7 * i + 1 by ring]
      exact (mul_right_cancel hyB).symm
    have h4 : s ^ (6 * i) = 1 := mul_left_cancel h3
    have h8 : 8 ∣ 6 * i := by
      have := orderOf_dvd_of_pow_eq_one h4
      rwa [hord] at this
    obtain ⟨q, rfl⟩ : 4 ∣ i := by omega
    rw [pow_mul, hs4]
    obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' q
    · left
      rw [pow_mul, pow_two, ht2, one_pow]
    · right
      rw [pow_succ, pow_mul, pow_two, ht2, one_pow, one_mul]
  ·
    exfalso
    rw [z_pow_two_mul_add_one hz2 r] at hyA
    have h1 : s ^ i * z * (s * s) = s ^ (i + 14) * z := by
      rw [← pow_two, mul_assoc, z_mul_pow_s hz2 hzs hs8 2, ← mul_assoc, ← pow_add]
    have h2 : s * s * (s ^ i * z) = s ^ (2 + i) * z := by
      rw [← pow_two, ← mul_assoc, ← pow_add]
    have h3 : s ^ (i + 14) = s ^ (2 + i) := mul_right_cancel ((h1.symm.trans hyA).trans h2)
    have h4 : s ^ (2 + i) * s ^ 12 = s ^ (2 + i) * 1 := by
      rw [mul_one, ← pow_add, show 2 + i + 12 = i + 14 by ring]
      exact h3
    have h5 : s ^ 12 = 1 := mul_left_cancel h4
    have h8 : 8 ∣ 12 := by
      have := orderOf_dvd_of_pow_eq_one h5
      rwa [hord] at this
    omega

theorem cent_W_split {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
    {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
    (c : OuterS16Ctx G L z t T E Q x B β S) (e : ↥S ≃* DihedralGroup 8) {s : G}
    (hs : s ∈ S) (hzS : z ∈ S) (hs8 : s ^ 8 = 1) (hs4 : s ^ 4 = t) (hz2 : z * z = 1)
    (hzs : z * s * z⁻¹ = s⁻¹) (hord : orderOf s = 8)
    (hgen : ∀ y ∈ S, ∃ i j : ℕ, y = s ^ i * z ^ j) :
    ∃ N : Subgroup G,
      (∀ n ∈ N, Odd (orderOf n)) ∧
      (∀ n ∈ Subgroup.centralizer ((Subgroup.closure ({s * s, s * z} : Set G) ⊔ E : Subgroup G) : Set G),
        Odd (orderOf n) → n ∈ N) ∧
      N ≤ Subgroup.centralizer ((Subgroup.closure ({s * s, s * z} : Set G) ⊔ E : Subgroup G) : Set G) ∧
      Subgroup.centralizer ((Subgroup.closure ({s * s, s * z} : Set G) ⊔ E : Subgroup G) : Set G) =
        N ⊔ Subgroup.zpowers t := by
  obtain ⟨N₀, hN₀nor, hN₀odd, hN₀int, hN₀cov⟩ := c.facts.2.1 3 (by norm_num) ⟨e⟩
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : Subgroup G, N₁ = N₀.map (centralizer (E : Set G)).subtype :=
    ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W = Subgroup.closure ({s * s, s * z} : Set G) ⊔ E :=
    ⟨_, rfl⟩
  rw [← hW]
  have hN₁mem : ∀ g : G, g ∈ N₁ ↔ ∃ y ∈ N₀, (y : G) = g := by
    intro g
    rw [hN₁]
    exact Subgroup.mem_map
  have hsS : s * s ∈ S := mul_mem hs hs
  have hszS : s * z ∈ S := mul_mem hs hzS
  have hgenW1 : s * s ∈ W := by
    rw [hW]
    exact mem_sup_left (subset_closure (Set.mem_insert _ _))
  have hgenW2 : s * z ∈ W := by
    rw [hW]
    exact mem_sup_left (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hEW : E ≤ W := by
    rw [hW]
    exact le_sup_right
  have htC : t ∈ centralizer (E : Set G) :=
    mem_centralizer_iff.2 fun v hv => c.hyp.outerE.t_comm_E hv
  have htW : t ∈ centralizer (W : Set G) := by
    have hK : W ≤ centralizer ({t} : Set G) := by
      rw [hW]
      refine sup_le ((Subgroup.closure_le _).2 ?_) ?_
      · rintro u (rfl | rfl)
        · exact mem_centralizer_singleton_iff.2 (c.t_comm_S _ hsS)
        · exact mem_centralizer_singleton_iff.2 (c.t_comm_S _ hszS)
      · intro v hv
        exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC v hv)
    rw [mem_centralizer_iff]
    intro w hw
    exact mem_centralizer_singleton_iff.1 (hK hw)
  have htWmem : t ∈ W := by
    have h4 : t = (s * s) * (s * s) := by
      rw [← hs4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h4]
    exact mul_mem hgenW1 hgenW1
  have hdec : ∀ g ∈ centralizer (E : Set G), ∃ n ∈ N₁, ∃ s₀ ∈ S, n * s₀ = g := by
    intro g hg
    have hmem : (⟨g, hg⟩ : ↥(centralizer (E : Set G))) ∈
        (Set.univ : Set ↥(centralizer (E : Set G))) := Set.mem_univ _
    rw [← hN₀cov, Set.mem_mul] at hmem
    obtain ⟨n, hn, s', hs', hns⟩ := hmem
    refine ⟨(n : G), (hN₁mem _).2 ⟨n, hn, rfl⟩, (s' : G), Subgroup.mem_subgroupOf.1 hs', ?_⟩
    simpa using congrArg Subtype.val hns
  have hN₁odd : ∀ n ∈ N₁, Odd (orderOf n) := by
    intro n hn
    obtain ⟨y, hy, rfl⟩ := (hN₁mem n).1 hn
    rw [Subgroup.orderOf_coe]
    exact (hN₀odd y).1 hy
  have hN₁int : ∀ n ∈ N₁, n ∈ S → n = 1 := by
    intro n hn hnS
    obtain ⟨y, hy, rfl⟩ := (hN₁mem n).1 hn
    have hyS : y ∈ S.subgroupOf (centralizer (E : Set G)) := Subgroup.mem_subgroupOf.2 hnS
    have hy1 : y ∈ N₀ ⊓ S.subgroupOf (centralizer (E : Set G)) := Subgroup.mem_inf.2 ⟨hy, hyS⟩
    rw [hN₀int, Subgroup.mem_bot] at hy1
    simp [hy1]
  have hN₁conj : ∀ h ∈ centralizer (E : Set G), ∀ n ∈ N₁, h * n * h⁻¹ ∈ N₁ := by
    intro h hh n hn
    obtain ⟨y, hy, rfl⟩ := (hN₁mem n).1 hn
    refine (hN₁mem _).2 ⟨(⟨h, hh⟩ : ↥(centralizer (E : Set G))) * y *
      (⟨h, hh⟩ : ↥(centralizer (E : Set G)))⁻¹, hN₀nor.conj_mem y hy _, ?_⟩
    simp
  have hkey : ∀ u ∈ S, u ∈ W → ∀ n ∈ N₁, ∀ s₀ ∈ S, n * s₀ ∈ centralizer (W : Set G) →
      s₀ * u = u * s₀ := by
    intro u huS huW n hn s₀ hs₀ hc
    have huH : u ∈ centralizer (E : Set G) := c.SC huS
    have hcu : u * (n * s₀) = n * s₀ * u := mem_centralizer_iff.1 hc u huW
    have hs' : s₀ * u = n⁻¹ * (u * n) * s₀ := by
      calc s₀ * u = n⁻¹ * (n * s₀ * u) := by group
        _ = n⁻¹ * (u * (n * s₀)) := by rw [hcu]
        _ = n⁻¹ * (u * n) * s₀ := by group
    have hcomm : s₀ * u * s₀⁻¹ * u⁻¹ = n⁻¹ * (u * n * u⁻¹) := by
      calc s₀ * u * s₀⁻¹ * u⁻¹ = n⁻¹ * (u * n) * s₀ * s₀⁻¹ * u⁻¹ := by rw [hs']
        _ = n⁻¹ * (u * n * u⁻¹) := by group
    have hmemN : s₀ * u * s₀⁻¹ * u⁻¹ ∈ N₁ := by
      rw [hcomm]
      exact mul_mem (inv_mem hn) (hN₁conj u huH n hn)
    have hmemS : s₀ * u * s₀⁻¹ * u⁻¹ ∈ S :=
      mul_mem (mul_mem (mul_mem hs₀ huS) (inv_mem hs₀)) (inv_mem huS)
    have h1 : s₀ * u * s₀⁻¹ * u⁻¹ = 1 := hN₁int _ hmemN hmemS
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hS1t : ∀ n ∈ N₁, ∀ s₀ ∈ S, n * s₀ ∈ centralizer (W : Set G) → s₀ = 1 ∨ s₀ = t := by
    intro n hn s₀ hs₀ hc
    exact s16_comm_gen_eq_one_or_t hz2 hzs hs8 hord hs4 (hgen s₀ hs₀)
      (hkey (s * s) hsS hgenW1 n hn s₀ hs₀ hc) (hkey (s * z) hszS hgenW2 n hn s₀ hs₀ hc)
  have ht2 : t * t = 1 := by
    rw [← hs4, ← pow_add]
    exact hs8
  have ht_ne : t ≠ 1 := by
    intro h
    have h4 : s ^ 4 = 1 := hs4.trans h
    have h8 := orderOf_dvd_of_pow_eq_one h4
    rw [hord] at h8
    omega
  have ht_ord : orderOf t = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht_ne
  have ht_pow_odd : ∀ k : ℕ, Odd k → t ^ k = t := by
    rintro k ⟨m, rfl⟩
    rw [pow_succ, pow_mul, pow_two, ht2, one_pow, one_mul]
  have hodd_c : ∀ g ∈ centralizer (W : Set G), Odd (orderOf g) → g ∈ N₁ := by
    intro g hg hodd
    have hgE : g ∈ centralizer (E : Set G) :=
      mem_centralizer_iff.2 fun v hv => mem_centralizer_iff.1 hg v (hEW hv)
    obtain ⟨n, hn, s₀, hs₀, hns⟩ := hdec g hgE
    have hgn : n * s₀ ∈ centralizer (W : Set G) := by
      rw [hns]
      exact hg
    rcases hS1t n hn s₀ hs₀ hgn with h | h
    · have hng : n = g := by
        rw [← hns, h, mul_one]
      rw [← hng]
      exact hn
    · exfalso
      have hnt : g = n * t := by
        rw [← hns, h]
      have hnW : n ∈ centralizer (W : Set G) := by
        have hn_eq : n = g * t⁻¹ := by
          rw [hnt]
          group
        rw [hn_eq]
        exact mul_mem hg (inv_mem htW)
      have hcomm : Commute n t := (mem_centralizer_iff.1 hnW t htWmem).symm
      have h2 : (n * t) ^ orderOf g = n ^ orderOf g * t ^ orderOf g := hcomm.mul_pow _
      rw [ht_pow_odd _ hodd, ← hnt, pow_orderOf_eq_one] at h2
      have h3 : t = (n ^ orderOf g)⁻¹ := eq_inv_of_mul_eq_one_right h2.symm
      have h4 : t ∈ N₁ := by
        rw [h3]
        exact inv_mem (pow_mem hn _)
      have h5 := hN₁odd t h4
      rw [ht_ord] at h5
      obtain ⟨m, hm⟩ := h5
      omega
  refine ⟨N₁ ⊓ centralizer (W : Set G), ?_, ?_, inf_le_right, ?_⟩
  · intro n hn
    exact hN₁odd n (Subgroup.mem_inf.1 hn).1
  · intro g hg hodd
    exact Subgroup.mem_inf.2 ⟨hodd_c g hg hodd, hg⟩
  · apply le_antisymm
    · intro g hg
      have hgE : g ∈ centralizer (E : Set G) :=
        mem_centralizer_iff.2 fun v hv => mem_centralizer_iff.1 hg v (hEW hv)
      obtain ⟨n, hn, s₀, hs₀, hns⟩ := hdec g hgE
      have hgn : n * s₀ ∈ centralizer (W : Set G) := by
        rw [hns]
        exact hg
      rcases hS1t n hn s₀ hs₀ hgn with h | h
      · have hng : n = g := by
          rw [← hns, h, mul_one]
        have hnC : n ∈ centralizer (W : Set G) := by
          rw [hng]
          exact hg
        rw [← hng]
        exact mem_sup_left (Subgroup.mem_inf.2 ⟨hn, hnC⟩)
      · have hnC : n ∈ centralizer (W : Set G) := by
          have hn_eq : n = g * t⁻¹ := by
            rw [← hns, h]
            group
          rw [hn_eq]
          exact mul_mem hg (inv_mem htW)
        have hgnt : g = n * t := by
          rw [← hns, h]
        rw [hgnt]
        exact mul_mem (mem_sup_left (Subgroup.mem_inf.2 ⟨hn, hnC⟩))
          (mem_sup_right (mem_zpowers t))
    · exact sup_le inf_le_right (zpowers_le.2 htW)

end CFSG.EvenSporadicStandard.Fin76b

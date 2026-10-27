module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

open Subgroup

variable {G : Type*} [Group G]

theorem mem_closure_pair_cases {r s g : G} (hsr : s * r * s⁻¹ ∈ zpowers r)
    (hs2 : s ^ 2 ∈ zpowers r) (hg : g ∈ closure ({r, s} : Set G)) :
    g ∈ zpowers r ∨ ∃ ρ ∈ zpowers r, g = ρ * s := by
  have hconj : ∀ ρ ∈ zpowers r, s * ρ * s⁻¹ ∈ zpowers r := by
    intro ρ hρ
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hρ
    rw [← conj_zpow]
    exact zpow_mem hsr n
  refine Subgroup.closure_induction
    (p := fun g _ => g ∈ zpowers r ∨ ∃ ρ ∈ zpowers r, g = ρ * s) ?_ ?_ ?_ ?_ hg
  · rintro g (rfl | rfl)
    · exact Or.inl (mem_zpowers g)
    · exact Or.inr ⟨1, one_mem _, (one_mul g).symm⟩
  · exact Or.inl (one_mem _)
  · rintro a b - - (ha | ⟨ρ, hρ, rfl⟩) (hb | ⟨σ, hσ, rfl⟩)
    · exact Or.inl (mul_mem ha hb)
    · exact Or.inr ⟨a * σ, mul_mem ha hσ, by rw [mul_assoc]⟩
    · refine Or.inr ⟨ρ * (s * b * s⁻¹), mul_mem hρ (hconj b hb), ?_⟩
      group
    · refine Or.inl ?_
      have : ρ * s * (σ * s) = ρ * (s * σ * s⁻¹) * s ^ 2 := by group
      rw [this]
      exact mul_mem (mul_mem hρ (hconj σ hσ)) hs2
  · rintro a - (ha | ⟨ρ, hρ, rfl⟩)
    · exact Or.inl (inv_mem ha)
    · refine Or.inr ⟨s * ((s ^ 2)⁻¹ * ρ⁻¹) * s⁻¹, hconj _ (mul_mem (inv_mem hs2) (inv_mem hρ)), ?_⟩
      group

theorem exists_pow_lt_of_mem_zpowers {y g : G} {n : ℕ} (hn : 0 < n) (hy : y ^ n = 1)
    (hg : g ∈ zpowers y) : ∃ i : ℕ, i < n ∧ g = y ^ i := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have h1 : 0 ≤ k % (n : ℤ) := Int.emod_nonneg k hn'.ne'
  have h2 : k % (n : ℤ) < n := Int.emod_lt_of_pos k hn'
  refine ⟨(k % (n : ℤ)).toNat, by omega, ?_⟩
  have h4 : y ^ (n : ℤ) = 1 := by exact_mod_cast hy
  calc y ^ k = y ^ ((n : ℤ) * (k / n) + k % n) := by rw [Int.mul_ediv_add_emod]
    _ = (y ^ (n : ℤ)) ^ (k / n) * y ^ (k % (n : ℤ)) := by rw [zpow_add, zpow_mul]
    _ = y ^ (k % (n : ℤ)) := by rw [h4, one_zpow, one_mul]
    _ = y ^ (k % (n : ℤ)).toNat := by rw [← zpow_natCast, Int.toNat_of_nonneg h1]

theorem pow_eq_pow_iff_of_orderOf_four {y : G} (hy : orderOf y = 4) {i j : ℕ} :
    y ^ i = y ^ j ↔ i % 4 = j % 4 := by
  rw [pow_eq_pow_iff_modEq, hy]; rfl

theorem inv_eq_pow_three {y : G} (hy : y ^ 4 = 1) : y⁻¹ = y ^ 3 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', hy]

theorem commute_of_mem_closure {S : Set G} {c : G} (h : ∀ s ∈ S, c * s = s * c) {g : G}
    (hg : g ∈ closure S) : c * g = g * c := by
  have : closure S ≤ centralizer {c} := by
    rw [closure_le]
    intro s hs
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (h s hs).symm
  exact ((mem_centralizer_singleton_iff).mp (this hg)).symm

theorem comm_of_mem_closure_pair {y v a b : G} (hyv : y * v = v * y)
    (ha : a ∈ closure ({y, v} : Set G)) (hb : b ∈ closure ({y, v} : Set G)) :
    a * b = b * a := by
  have hpw : ({y, v} : Set G).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first | exact Commute.refl _ | exact hyv | exact hyv.symm
  have := Subgroup.isMulCommutative_closure hpw
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : closure ({y, v} : Set G)) ⟨b, hb⟩)

theorem pow_eq_one_or_self {z : G} (hz : z ^ 2 = 1) (n : ℕ) : z ^ n = 1 ∨ z ^ n = z := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; rw [← two_mul, pow_mul, hz, one_pow]
  · right; rw [pow_succ, pow_mul, hz, one_pow, one_mul]

theorem mul_mem_iff_of_relIndex_two {H K : Subgroup G} (h : H.relIndex K = 2) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) : a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := by
  have := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf K) h (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa [Subgroup.mem_subgroupOf] using this

theorem sq_mem_of_relIndex_two {H K : Subgroup G} (h : H.relIndex K = 2) {a : G} (ha : a ∈ K) :
    a ^ 2 ∈ H := by
  have := Subgroup.sq_mem_of_index_two (H := H.subgroupOf K) h ⟨a, ha⟩
  simpa [Subgroup.mem_subgroupOf] using this

structure T0 (y w : G) : Prop where
  ord : orderOf y = 4
  sq : w ^ 2 = y ^ 2
  not_mem : w ∉ zpowers y

namespace T0

variable {y w : G} (h : T0 y w)

include h

theorem y_pow_four : y ^ 4 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one y

theorem y_sq_ne_one : y ^ 2 ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h.ord]; norm_num)

theorem w_pow_four : w ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h.sq, ← pow_mul]; exact h.y_pow_four

theorem orderOf_w : orderOf w = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf w = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one, h.sq]; exact h.y_sq_ne_one)
      (by rw [show 2 ^ (1 + 1) = 4 from rfl]; exact h.w_pow_four)
  simpa using h2

theorem mul_eq_iff {i j i' j' : ℕ} :
    y ^ i * w ^ j = y ^ i' * w ^ j' ↔ j % 2 = j' % 2 ∧ (i + j) % 4 = (i' + j') % 4 := by
  have hw : ∀ j : ℕ, w ^ j = y ^ (2 * (j / 2)) * w ^ (j % 2) := by
    intro j
    conv_lhs => rw [← Nat.div_add_mod j 2, pow_add, pow_mul, h.sq, ← pow_mul]
  have nf : ∀ i j : ℕ, y ^ i * w ^ j = y ^ (i + 2 * (j / 2)) * w ^ (j % 2) := by
    intro i j
    rw [hw j, ← mul_assoc, ← pow_add]
  rw [nf i j, nf i' j']
  have hj := Nat.mod_two_eq_zero_or_one j
  have hj' := Nat.mod_two_eq_zero_or_one j'
  have hA : ∀ A A' : ℕ, y ^ A = y ^ A' ↔ A % 4 = A' % 4 := fun A A' =>
    pow_eq_pow_iff_of_orderOf_four h.ord
  constructor
  · intro heq
    rcases hj with hj | hj <;> rcases hj' with hj' | hj' <;> rw [hj, hj'] at heq
    · simp only [pow_zero, mul_one] at heq
      rw [hA] at heq
      omega
    · exfalso
      apply h.not_mem
      simp only [pow_zero, mul_one, pow_one] at heq
      have : w = (y ^ (i' + 2 * (j' / 2)))⁻¹ * y ^ (i + 2 * (j / 2)) := by
        rw [heq]; group
      rw [this]
      exact mul_mem (inv_mem (pow_mem (mem_zpowers y) _)) (pow_mem (mem_zpowers y) _)
    · exfalso
      apply h.not_mem
      simp only [pow_zero, mul_one, pow_one] at heq
      have : w = (y ^ (i + 2 * (j / 2)))⁻¹ * y ^ (i' + 2 * (j' / 2)) := by
        rw [← heq]; group
      rw [this]
      exact mul_mem (inv_mem (pow_mem (mem_zpowers y) _)) (pow_mem (mem_zpowers y) _)
    · simp only [pow_one] at heq
      have := mul_right_cancel heq
      rw [hA] at this
      omega
  · rintro ⟨hjj, hmod⟩
    have hy : y ^ (i + 2 * (j / 2)) = y ^ (i' + 2 * (j' / 2)) := (hA _ _).mpr (by omega)
    rw [← hjj, hy]

theorem mem_closure_iff (hwy : w * y * w⁻¹ ∈ zpowers y) {g : G} :
    g ∈ closure ({y, w} : Set G) ↔ ∃ i j : ℕ, i < 4 ∧ j < 2 ∧ g = y ^ i * w ^ j := by
  constructor
  · intro hg
    have hs2 : w ^ 2 ∈ zpowers y := by
      rw [h.sq]; exact pow_mem (mem_zpowers y) 2
    rcases mem_closure_pair_cases hwy hs2 hg with hg | ⟨ρ, hρ, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) h.y_pow_four hg
      exact ⟨i, 0, hi, by norm_num, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) h.y_pow_four hρ
      exact ⟨i, 1, hi, by norm_num, by simp⟩
  · rintro ⟨i, j, -, -, rfl⟩
    exact mul_mem (pow_mem (subset_closure (by simp)) i) (pow_mem (subset_closure (by simp)) j)

theorem card_closure (hwy : w * y * w⁻¹ ∈ zpowers y) :
    Nat.card (closure ({y, w} : Set G)) = 8 := by
  let f : Fin 4 × Fin 2 → closure ({y, w} : Set G) := fun p =>
    ⟨y ^ p.1.val * w ^ p.2.val, (h.mem_closure_iff hwy).mpr ⟨_, _, p.1.2, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ hij
      have := congrArg Subtype.val hij
      obtain ⟨h1, h2⟩ := h.mul_eq_iff.mp this
      dsimp only at h1 h2
      have e1 : j = j' := by omega
      have e2 : i = i' := by omega
      subst e1 e2
      rfl
    · rintro ⟨g, hg⟩
      obtain ⟨i, j, hi, hj, rfl⟩ := (h.mem_closure_iff hwy).mp hg
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

end T0

structure Config (M : Subgroup G) (y w m : G) : Prop where
  t0 : T0 y w
  wy : w * y * w⁻¹ ∈ zpowers y
  y_mem : y ∈ M
  w_mem : w ∈ M
  m_mem : m ∈ M
  m_not : m ∉ closure ({y, w} : Set G)
  m_sq : m ^ 2 ∈ closure ({y, w} : Set G)
  span : ∀ g ∈ M, g ∈ closure ({y, w} : Set G) ∨ g * m⁻¹ ∈ closure ({y, w} : Set G)

namespace Config

variable {M : Subgroup G} {y w m : G} (c : Config M y w m)

include c

theorem le : closure ({y, w} : Set G) ≤ M := by
  rw [closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact c.y_mem
  · exact c.w_mem

theorem eq_closure : M = closure ({y, w, m} : Set G) := by
  have hT : closure ({y, w} : Set G) ≤ closure ({y, w, m} : Set G) :=
    closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  have hm : m ∈ closure ({y, w, m} : Set G) := subset_closure (by simp)
  apply le_antisymm
  · intro g hg
    rcases c.span g hg with h1 | h1
    · exact hT h1
    · have := mul_mem (hT h1) hm
      simpa using this
  · rw [closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact c.y_mem
    · exact c.w_mem
    · exact c.m_mem

theorem relIndex : (closure ({y, w} : Set G)).relIndex M = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨m, c.m_mem⟩, ?_⟩
  rintro ⟨b, hb⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hbT : b ∈ closure ({y, w} : Set G)
  · refine Or.inr ⟨hbT, fun hbm => c.m_not ?_⟩
    have := mul_mem (inv_mem hbT) hbm
    simpa using this
  · refine Or.inl ⟨?_, hbT⟩
    have h1 := (c.span b hb).resolve_left hbT
    have := mul_mem h1 c.m_sq
    have e : b * m⁻¹ * m ^ 2 = b * m := by group
    rwa [e] at this

theorem card : Nat.card M = 16 := by
  have := Subgroup.relIndex_mul_card (closure ({y, w} : Set G)) M
  rw [c.relIndex, inf_of_le_left c.le, c.t0.card_closure c.wy] at this
  omega

end Config

theorem parity {t y w m : G} (hy : orderOf y = 4) (hty : t * y * t⁻¹ = y⁻¹)
    (htw : t * w = w * t) {ε : ℕ} (hε : ε % 2 = 1) (hmt : m * t * m⁻¹ = y ^ ε * t) {α β : ℕ}
    (hm2 : m ^ 2 = y ^ α * w ^ β) :
    (m * y * m⁻¹ = y → α % 2 = 1) ∧ (m * y * m⁻¹ = y⁻¹ → α % 2 = 0) := by
  have h1 : SemiconjBy t y y⁻¹ := mul_inv_eq_iff_eq_mul.mp hty
  have h2 : SemiconjBy m t (y ^ ε * t) := mul_inv_eq_iff_eq_mul.mp hmt
  have hcomm : t * w ^ β = w ^ β * t := (Commute.pow_right (show Commute t w from htw) β).eq
  have hE1 : (y ^ α * w ^ β) * t = (y ^ (2 * α) * t) * (y ^ α * w ^ β) := by
    have e : t * y ^ α = y⁻¹ ^ α * t := (h1.pow_right α).eq
    calc (y ^ α * w ^ β) * t = y ^ α * (t * w ^ β) := by rw [mul_assoc, hcomm]
      _ = (y ^ (2 * α) * y⁻¹ ^ α) * t * w ^ β := by
        have : y ^ (2 * α) * y⁻¹ ^ α = y ^ α := by group
        rw [this]; group
      _ = y ^ (2 * α) * (y⁻¹ ^ α * t) * w ^ β := by group
      _ = (y ^ (2 * α) * (t * y ^ α)) * w ^ β := by rw [e]
      _ = (y ^ (2 * α) * t) * (y ^ α * w ^ β) := by group
  have key : ∀ y' : G, m * y * m⁻¹ = y' → y' ^ ε * y ^ ε = y ^ (2 * α) := by
    intro y' hy'
    have h3 : SemiconjBy m y y' := mul_inv_eq_iff_eq_mul.mp hy'
    have h4 : SemiconjBy m (y ^ ε * t) (y' ^ ε * (y ^ ε * t)) := (h3.pow_right ε).mul_right h2
    have h5 : SemiconjBy (m * m) t (y' ^ ε * (y ^ ε * t)) := h4.mul_left h2
    have h6 : (y ^ α * w ^ β) * t = (y' ^ ε * (y ^ ε * t)) * (y ^ α * w ^ β) := by
      rw [← hm2, pow_two]
      exact h5.eq
    rw [hE1] at h6
    have h7 := mul_right_cancel h6
    have h8 : (y ^ (2 * α)) * t = (y' ^ ε * y ^ ε) * t := by rw [h7, mul_assoc]
    exact (mul_right_cancel h8).symm
  constructor
  · intro hδ
    have := key y hδ
    rw [← pow_add, pow_eq_pow_iff_of_orderOf_four hy] at this
    omega
  · intro hδ
    have := key y⁻¹ hδ
    rw [inv_pow, inv_mul_cancel, eq_comm, ← pow_zero y, pow_eq_pow_iff_of_orderOf_four hy] at this
    omega

end CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

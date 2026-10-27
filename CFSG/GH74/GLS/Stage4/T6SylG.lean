module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

theorem t6_cent_of_cent_invols {G : Type} [Group G] {T : Subgroup G} {x : G}
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hT2 : ∀ t ∈ T, ∃ k : ℕ, t ^ (2 ^ k) = 1)
    (hxT : ∀ t ∈ T, x * t * x⁻¹ ∈ T) (hx : Odd (orderOf x))
    (hinv : ∀ t ∈ T, t * t = 1 → x * t * x⁻¹ = t) : ∀ t ∈ T, x * t * x⁻¹ = t := by
  suffices h : ∀ k : ℕ, ∀ t ∈ T, t ^ (2 ^ k) = 1 → x * t * x⁻¹ = t from fun t ht => by
    obtain ⟨k, hk⟩ := hT2 t ht
    exact h k t ht hk
  intro k
  induction k with
  | zero =>
    intro t _ h1
    rw [pow_zero, pow_one] at h1
    subst h1
    group
  | succ k ih =>
    intro t ht htk
    have hsq : (t * t) ^ (2 ^ k) = 1 := by
      rw [← pow_two, ← pow_mul, ← pow_succ']
      exact htk
    have h2 : x * (t * t) * x⁻¹ = t * t := ih (t * t) (T.mul_mem ht ht) hsq
    have hαt : x * t * x⁻¹ ∈ T := hxT t ht
    have hcomm : t⁻¹ * (x * t * x⁻¹) = (x * t * x⁻¹) * t⁻¹ := hab _ (T.inv_mem ht) _ hαt
    have e1 : (x * t * x⁻¹) * (x * t * x⁻¹) = t * t := by
      rw [← h2]
      group
    obtain ⟨s, hs⟩ : ∃ s : G, s = x * t * x⁻¹ * t⁻¹ := ⟨_, rfl⟩
    have hsT : s ∈ T := hs ▸ T.mul_mem hαt (T.inv_mem ht)
    have hss : s * s = 1 := by
      rw [hs]
      calc (x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹)
          = (x * t * x⁻¹) * (t⁻¹ * (x * t * x⁻¹)) * t⁻¹ := by group
        _ = (x * t * x⁻¹) * ((x * t * x⁻¹) * t⁻¹) * t⁻¹ := by rw [hcomm]
        _ = ((x * t * x⁻¹) * (x * t * x⁻¹)) * t⁻¹ * t⁻¹ := by group
        _ = 1 := by rw [e1]; group
    have hαs : x * s * x⁻¹ = s := hinv s hsT hss
    have hpow : ∀ j : ℕ, x ^ j * t * (x ^ j)⁻¹ = s ^ j * t := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        have e3 : x ^ (j + 1) * t * (x ^ (j + 1))⁻¹ = x * (x ^ j * t * (x ^ j)⁻¹) * x⁻¹ := by
          rw [pow_succ']
          group
        have e4 : x * (s ^ j * t) * x⁻¹ = (x * s * x⁻¹) ^ j * (x * t * x⁻¹) := by
          rw [conj_pow]
          group
        have e5 : s * t = x * t * x⁻¹ := by
          rw [hs]
          group
        rw [e3, ihj, e4, hαs, ← e5, pow_succ]
        exact (mul_assoc _ _ _).symm
    obtain ⟨m, hm⟩ := hx
    have h3 := hpow (orderOf x)
    rw [pow_orderOf_eq_one] at h3
    have h4 : s ^ orderOf x = 1 := by
      have : s ^ orderOf x * t = 1 * t := by
        rw [← h3]
        group
      exact mul_right_cancel this
    have h5 : s = 1 := by
      have : s ^ orderOf x = s := by
        rw [hm, pow_succ, pow_mul, pow_two, hss, one_pow, one_mul]
      rw [← this]
      exact h4
    rw [hs] at h5
    exact mul_inv_eq_one.1 h5

theorem t6_mem_of_pelt_normalizes_sylow {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (_hTM : T ≤ M) (hTp : IsPGroup 2 ↥T) (hT : ¬ 2 ∣ T.relIndex M) {n : G} (hnM : n ∈ M)
    (hnT : ∀ t ∈ T, n * t * n⁻¹ ∈ T) (hn2 : ∃ k : ℕ, n ^ (2 ^ k) = 1) : n ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hn2
  have hP : IsPGroup 2 ↥(T.subgroupOf M) := hTp.comap_subtype
  let S : Sylow 2 ↥M := hP.toSylow hT
  let m : ↥M := ⟨n, hnM⟩
  have hmk : m ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
  have hQ : IsPGroup 2 ↥(Subgroup.zpowers m) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, Subtype.ext ?_⟩
    have : ((g : ↥M)) ^ (2 ^ k) = 1 := by
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hmk, one_zpow]
    simpa using this
  have hnorm : m ∈ Subgroup.normalizer (S : Set ↥M) :=
    Subgroup.mem_normalizer_fintype fun s hs => hnT s hs
  have hmem : m ∈ Subgroup.zpowers m ⊓ Subgroup.normalizer (S : Set ↥M) :=
    ⟨Subgroup.mem_zpowers m, hnorm⟩
  rw [hQ.inf_normalizer_sylow S] at hmem
  exact hmem.2

theorem t6_two_part_decomp_of_isOfFinOrder {G : Type} [Group G] {g : G} (hg : IsOfFinOrder g) :
    ∃ a b : G, g = a * b ∧ a * b = b * a ∧ (∃ k : ℕ, a ^ (2 ^ k) = 1) ∧ Odd (orderOf b) ∧
      a ∈ Subgroup.zpowers g ∧ b ∈ Subgroup.zpowers g := by
  obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd hg.orderOf_pos.ne'
  have hcop : Nat.Coprime (2 ^ k) r := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hr)
  obtain ⟨x, y, hbez⟩ : ∃ x y : ℤ, ((2 ^ k : ℕ) : ℤ) * x + (r : ℤ) * y = 1 := by
    refine ⟨Nat.gcdA (2 ^ k) r, Nat.gcdB (2 ^ k) r, ?_⟩
    have h := Nat.gcd_eq_gcd_ab (2 ^ k) r
    rw [hcop.gcd_eq_one] at h
    push_cast at h ⊢
    linarith
  have hord : ((2 ^ k : ℕ) : ℤ) * (r : ℤ) = (orderOf g : ℤ) := by
    rw [hkr]
    push_cast
    ring
  refine ⟨g ^ ((r : ℤ) * y), g ^ (((2 ^ k : ℕ) : ℤ) * x), ?_, ?_, ⟨k, ?_⟩, ?_, ?_, ?_⟩
  · rw [← zpow_add, add_comm, hbez, zpow_one]
  · exact ((Commute.refl g).zpow_zpow _ _).eq
  · have h : (r : ℤ) * y * ((2 ^ k : ℕ) : ℤ) = (orderOf g : ℤ) * y := by
      rw [← hord]
      ring
    rw [← zpow_natCast, ← zpow_mul, h, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have h : ((2 ^ k : ℕ) : ℤ) * x * (r : ℤ) = (orderOf g : ℤ) * x := by
      rw [← hord]
      ring
    have h1 : (g ^ (((2 ^ k : ℕ) : ℤ) * x)) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul, h, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact Odd.of_dvd_nat hr (orderOf_dvd_of_pow_eq_one h1)
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _

theorem t6_two_part_decomp {G : Type} [Group G] [Finite G] (g : G) :
    ∃ a b : G, g = a * b ∧ a * b = b * a ∧ (∃ k : ℕ, a ^ (2 ^ k) = 1) ∧ Odd (orderOf b) ∧
      a ∈ Subgroup.zpowers g ∧ b ∈ Subgroup.zpowers g :=
  t6_two_part_decomp_of_isOfFinOrder (isOfFinOrder_of_finite g)

theorem t6_two_complement {G : Type} [Group G] [Finite G] (M T : Subgroup G) (hTM : T ≤ M)
    (hTp : IsPGroup 2 ↥T) (hT : ¬ 2 ∣ T.relIndex M)
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hN : ∀ n ∈ M, (∀ t ∈ T, n * t * n⁻¹ ∈ T) → Odd (orderOf n) → ∀ t ∈ T, n * t = t * n) :
    ∃ K : Subgroup G, K ≤ M ∧ (∀ g ∈ M, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ ¬ 2 ∣ Nat.card ↥K ∧
      Nat.card ↥M = Nat.card ↥K * Nat.card ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(T.subgroupOf M) := hTp.comap_subtype
  let S : Sylow 2 ↥M := hP.toSylow hT
  have hSmem : ∀ y : ↥M, y ∈ (S : Subgroup ↥M) ↔ (y : G) ∈ T := fun y => Subgroup.mem_subgroupOf
  have hcent : Subgroup.normalizer (S : Set ↥M) ≤ Subgroup.centralizer (S : Set ↥M) := by
    intro n' hn'
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsT : (s : G) ∈ T := (hSmem s).1 hs
    have hnM : (n' : G) ∈ M := n'.2
    have hnT : ∀ t ∈ T, (n' : G) * t * (n' : G)⁻¹ ∈ T := by
      intro t ht
      have h1 := ((Subgroup.mem_normalizer_iff.1 hn') ⟨t, hTM ht⟩).1 ((hSmem ⟨t, hTM ht⟩).2 ht)
      exact (hSmem _).1 h1
    obtain ⟨a, b, hnab, -, ha2, hb, ha, hbz⟩ :=
      t6_two_part_decomp_of_isOfFinOrder (isOfFinOrder_of_finite (n' : G))
    have hnN : (n' : G) ∈ Subgroup.normalizer (T : Set G) := Subgroup.mem_normalizer_fintype hnT
    have hzN : Subgroup.zpowers (n' : G) ≤ Subgroup.normalizer (T : Set G) :=
      Subgroup.zpowers_le.2 hnN
    have hzM : Subgroup.zpowers (n' : G) ≤ M := Subgroup.zpowers_le.2 hnM
    have haN : ∀ t ∈ T, a * t * a⁻¹ ∈ T := fun t ht =>
      ((Subgroup.mem_normalizer_iff.1 (hzN ha)) t).1 ht
    have hbN : ∀ t ∈ T, b * t * b⁻¹ ∈ T := fun t ht =>
      ((Subgroup.mem_normalizer_iff.1 (hzN hbz)) t).1 ht
    have haT : a ∈ T := t6_mem_of_pelt_normalizes_sylow hTM hTp hT (hzM ha) haN ha2
    have hbc : ∀ t ∈ T, b * t = t * b := hN b (hzM hbz) hbN hb
    apply Subtype.ext
    show (s : G) * (n' : G) = (n' : G) * (s : G)
    rw [hnab]
    calc (s : G) * (a * b) = ((s : G) * a) * b := by group
      _ = (a * (s : G)) * b := by rw [hab _ hsT _ haT]
      _ = a * ((s : G) * b) := by group
      _ = a * (b * (s : G)) := by rw [← hbc _ hsT]
      _ = (a * b) * (s : G) := by group
  obtain ⟨K', hK'n, hK'odd, hK'idx, -⟩ := CFSG.GroupTheory.burnside_normal_complement S hcent
  have hST : Nat.card ↥(S : Subgroup ↥M) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv
  refine ⟨K'.map M.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨k, hk, rfl⟩
    exact ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, hK'n.conj_mem k hk _, rfl⟩
  · rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hK'odd
  · rw [Subgroup.card_map_of_injective M.subtype_injective, ← hST, ← hK'idx]
    exact (Subgroup.card_mul_index K').symm

end CFSG.GH74.GLS.Stage4.Rest.T6

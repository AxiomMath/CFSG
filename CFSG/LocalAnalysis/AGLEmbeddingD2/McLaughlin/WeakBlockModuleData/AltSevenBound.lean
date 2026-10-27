module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem orderOf_ne_thirtyFive_perm_seven (g : Equiv.Perm (Fin 7)) : orderOf g ≠ 35 := by
  intro h
  rw [← Equiv.Perm.lcm_cycleType] at h
  have hsum : g.cycleType.sum ≤ 7 := by
    rw [Equiv.Perm.sum_cycleType]
    simpa using Finset.card_le_univ g.support
  have hmem : ∀ n ∈ g.cycleType, n = 5 ∨ n = 7 := by
    intro n hn
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    have hdvd : n ∣ 35 := h ▸ Multiset.dvd_lcm hn
    have hle : n ≤ 7 := le_trans (Multiset.le_sum_of_mem hn) hsum
    interval_cases n <;> omega
  by_cases h0 : g.cycleType = 0
  · rw [h0] at h
    simp at h
  · obtain ⟨n, hn⟩ := Multiset.exists_mem_of_ne_zero h0
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hn
    have ht0 : t = 0 := by
      by_contra ht0
      obtain ⟨m, hm⟩ := Multiset.exists_mem_of_ne_zero ht0
      have hmt : m ∈ g.cycleType := by rw [ht]; exact Multiset.mem_cons_of_mem hm
      have hm' : m ≤ t.sum := Multiset.le_sum_of_mem hm
      have hnm := hmem n hn
      have hmm := hmem m hmt
      rw [ht, Multiset.sum_cons] at hsum
      omega
    rw [ht, ht0] at h
    simp at h
    have := hmem n hn
    omega

theorem commute_of_orderOf_five_seven {G : Type*} [Group G] {c x : G} (hc : orderOf c = 7)
    (hx : orderOf x = 5) (hn : x * c * x⁻¹ ∈ Subgroup.zpowers c) : Commute x c := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hpow : ∀ n : ℕ, x ^ n * c * (x ^ n)⁻¹ = c ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * c * (x ^ (n + 1))⁻¹
          = x * (x ^ n * c * (x ^ n)⁻¹) * x⁻¹ := by group
        _ = x * c ^ (k ^ n) * x⁻¹ := by rw [ih]
        _ = (x * c * x⁻¹) ^ (k ^ n) := by rw [conj_zpow]
        _ = c ^ (k ^ (n + 1)) := by rw [← hk, ← zpow_mul, pow_succ, mul_comm]
  have h5 := hpow 5
  rw [show x ^ 5 = 1 from hx ▸ pow_orderOf_eq_one x] at h5
  simp only [inv_one, mul_one, one_mul] at h5
  have h7 : (7 : ℤ) ∣ k ^ 5 - 1 := by
    have : c ^ (k ^ 5 - 1) = 1 := by rw [zpow_sub, ← h5, zpow_one, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr this
    rwa [hc] at this
  have hk1 : (k : ZMod 7) ^ 5 = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k ^ 5 - 1) 7).mpr (by exact_mod_cast h7)
    push_cast at this
    exact sub_eq_zero.mp this
  have hk2 : (k : ZMod 7) = 1 := by
    have key : ∀ a : ZMod 7, a ^ 5 = 1 → a = 1 := by decide
    exact key _ hk1
  have h7' : (7 : ℤ) ∣ k - 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 7).mp (by push_cast; rw [hk2]; simp)
    exact_mod_cast this
  have : c ^ k = c := by
    have h1 : c ^ (k - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hc]
      exact h7'
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h1
    exact h1
  rw [this] at hk
  unfold Commute SemiconjBy
  have : x * c * x⁻¹ = c := hk.symm
  calc x * c = x * c * x⁻¹ * x := by group
    _ = c * x := by rw [this]

theorem card_dvd_alt_seven (H : Subgroup (alternatingGroup (Fin 7))) : Nat.card H ∣ 2520 := by
  have := Subgroup.card_subgroup_dvd_card H
  rwa [Nat.card_eq_fintype_card (α := alternatingGroup (Fin 7)), card_alternatingGroup] at this

theorem not_thirtyFive_dvd_card_alt_seven (H : Subgroup (alternatingGroup (Fin 7)))
    (h3 : ¬ 3 ∣ Nat.card H) : ¬ 35 ∣ Nat.card H := by
  intro h35
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hdvd := card_dvd_alt_seven H
  have hkey : ∀ d ∈ Nat.divisors 2520, ¬ 3 ∣ d → 35 ∣ d → d ∣ 280 ∧ ¬ 49 ∣ d := by
    decide +kernel
  obtain ⟨h280, h49⟩ := hkey _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) h3 h35
  obtain ⟨P⟩ : Nonempty (Sylow 7 H) := Sylow.nonempty
  have hP : Nat.card P = 7 := by
    rw [Sylow.card_eq_multiplicity]
    have hn0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card H).factorization 7 :=
      (Nat.Prime.factorization_pos_of_dvd (by decide) hn0 (dvd_trans (by norm_num) h35))
    have h2 : (Nat.card H).factorization 7 < 2 := by
      by_contra hlt
      push Not at hlt
      exact h49 (dvd_trans (pow_dvd_pow 7 hlt) (Nat.ordProj_dvd _ _))
    have : (Nat.card H).factorization 7 = 1 := by omega
    rw [this]; norm_num
  set N := Subgroup.normalizer (P : Set H) with hN
  have hidx : Nat.card (Sylow 7 H) = N.index := P.card_eq_index_normalizer
  have hmod := card_sylow_modEq_one 7 H
  have hmul : Nat.card N * N.index = Nat.card H := Subgroup.card_mul_index N
  have hidvd : N.index ∣ 280 := (Dvd.intro_left _ hmul).trans h280
  have h5N : 5 ∣ Nat.card N := by
    by_contra h5
    have h5H : 5 ∣ Nat.card H := dvd_trans (by norm_num) h35
    rw [← hmul] at h5H
    have h5i : 5 ∣ N.index := by
      rcases (Nat.Prime.dvd_mul (by decide)).mp h5H with h | h
      · exact absurd h h5
      · exact h
    have hk : ∀ d ∈ Nat.divisors 280, 5 ∣ d → d % 7 ≠ 1 := by decide
    rw [hidx] at hmod
    exact hk _ (Nat.mem_divisors.mpr ⟨hidvd, by norm_num⟩) h5i hmod
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 h5N
  have : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  have hgo : orderOf g = 7 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hP]
  set x : H := (x' : H) with hxdef
  set c : H := (g : H) with hcdef
  have hxo : orderOf x = 5 := by rw [hxdef, Subgroup.orderOf_coe, hx']
  have hco : orderOf c = 7 := by rw [hcdef, Subgroup.orderOf_coe, hgo]
  have hxn : x ∈ N := x'.2
  have hcP : c ∈ (P : Subgroup H) := g.2
  have hconj : x * c * x⁻¹ ∈ Subgroup.zpowers c := by
    have hmem : x * c * x⁻¹ ∈ (P : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hxn c).mp hcP
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨_, hmem⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcomm : Commute x c := commute_of_orderOf_five_seven hco hxo hconj
  have h35o : orderOf (x * c) = 35 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hxo, hco]; decide), hxo, hco]
  let φ : H →* Equiv.Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp H.subtype
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  exact orderOf_ne_thirtyFive_perm_seven (φ (x * c)) (by rw [orderOf_injective φ hφ, h35o])

theorem card_le_of_not_three_dvd_alt_seven (H : Subgroup (alternatingGroup (Fin 7)))
    (h : ¬ 3 ∣ Nat.card H) : Nat.card H ≤ 140 := by
  have hdvd := card_dvd_alt_seven H
  have key : ∀ d ∈ Nat.divisors 2520, ¬ 3 ∣ d → ¬ 35 ∣ d → d ≤ 140 := by decide +kernel
  exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) h (not_thirtyFive_dvd_card_alt_seven H h)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

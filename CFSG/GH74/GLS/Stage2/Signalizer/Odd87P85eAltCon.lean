module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eAlt

public section

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

theorem perm_pow_five_eq_one {n : ℕ} (hn : n ≤ 11) (c : Equiv.Perm (Fin n)) (a : ℕ)
    (hc : c ^ (5 ^ a) = 1) : c ^ 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Equiv.Perm.pow_prime_eq_one_iff]
  intro m hm
  have hdvd : m ∣ 5 ^ a :=
    (Equiv.Perm.dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one hc)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
  have h2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
  have hle : m ≤ n := by
    calc m ≤ c.cycleType.sum := Multiset.le_sum_of_mem hm
      _ ≤ Fintype.card (Fin n) := Equiv.Perm.sum_cycleType_le c
      _ = n := Fintype.card_fin n
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · simp at hk
      omega
    · rfl
    · exfalso
      have : 5 ^ (k + 2) ≥ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rw [hk, hk1]
  norm_num

theorem alt_contra {X : Type} [Group X] [Finite X] {n : ℕ} (hn : n ≤ 11)
    (π : X →* Equiv.Perm (Fin n))
    (hker : ∀ Q : Subgroup X, IsPGroup 2 Q → Nat.card ↥(Q ⊓ π.ker) ≤ 2)
    {Q : Subgroup X} (hQ2 : IsPGroup 2 Q) {w : X} {a : ℕ} (hw : w ^ (5 ^ a) = 1)
    (hwQ : w ∈ Subgroup.normalizer (Q : Set X)) (hQ : ⁅Q, Subgroup.zpowers w⁆ = Q) :
    Nat.card Q ≤ 32 := by
  have hc5 : π w ^ 5 = 1 := perm_pow_five_eq_one hn (π w) a (by rw [← map_pow, hw, map_one])
  have hQ'2 : IsPGroup 2 (Q.map π) := hQ2.map π
  have hnorm : π w ∈ Subgroup.normalizer ((Q.map π : Subgroup (Equiv.Perm (Fin n))) : Set _) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨w * x * w⁻¹, (Subgroup.mem_set_normalizer_iff.1 hwQ x).1 hx, ?_⟩
      simp
    · rintro ⟨x, hx, hxy⟩
      refine ⟨w⁻¹ * x * w, (Subgroup.mem_set_normalizer_iff''.1 hwQ x).1 hx, ?_⟩
      rw [map_mul, map_mul, map_inv, hxy]
      group
  have hcomm : ⁅Q.map π, Subgroup.zpowers (π w)⁆ = Q.map π := by
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, hQ]
  have hcardQ' : Nat.card (Q.map π) ≤ 16 := by
    have hord : orderOf (π w) ∣ 5 := orderOf_dvd_of_pow_eq_one hc5
    rcases (Nat.dvd_prime Nat.prime_five).1 hord with h1 | h5
    · have h1' : π w = 1 := orderOf_eq_one_iff.1 h1
      have hbot : Q.map π = ⊥ := by
        rw [← hcomm, h1', Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
      rw [hbot, Subgroup.card_bot]
      norm_num
    · exact alt5_perm_bound hn (π w) h5 (Q.map π) hQ'2 hnorm hcomm
  have hcard : Nat.card (π.ker.subgroupOf Q) * Nat.card (Q.map π) = Nat.card Q := by
    have := Subgroup.card_ker_mul_card_range (π.domRestrict Q)
    rwa [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at this
  have hkerQ : Nat.card (π.ker.subgroupOf Q) = Nat.card ↥(Q ⊓ π.ker) := by
    rw [← Subgroup.card_subtype Q (π.ker.subgroupOf Q), Subgroup.subgroupOf_map_subtype,
      inf_comm]
  calc Nat.card Q = Nat.card (π.ker.subgroupOf Q) * Nat.card (Q.map π) := hcard.symm
    _ ≤ 2 * 16 := by
      rw [hkerQ]
      exact Nat.mul_le_mul (hker Q hQ2) hcardQ'
    _ = 32 := by norm_num

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

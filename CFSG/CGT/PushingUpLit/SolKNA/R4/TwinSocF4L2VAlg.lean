module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.IntegralDomain

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

theorem isPGroup_zpowers_of_pow' {G : Type*} [Group G] {v : G} {k : ℕ} (h : v ^ 2 ^ k = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers v) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem exists_conj_mem_zpowers {G : Type*} [Group G] [Finite G] {U N : Subgroup G} {u : G}
    {k : ℕ} (hNodd : Odd (Nat.card N)) (hNU : N ≤ U) (huU : u ∈ U) (huk : u ^ 2 ^ k = 1)
    (hU : ∀ g ∈ U, ∃ n ∈ N, ∃ j : ℤ, g = n * u ^ j) {τ : G} (hτ : τ ∈ U) {a : ℕ}
    (hτa : τ ^ 2 ^ a = 1) : ∃ h ∈ U, ∃ j : ℤ, τ = h * u ^ j * h⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u' : ↥U := ⟨u, huU⟩ with hu'
  have hcoe : ∀ m : ℤ, ((u' ^ m : ↥U) : G) = u ^ m := fun m => by
    simp [hu']
  have hu'k : u' ^ 2 ^ k = 1 := Subtype.ext (by simpa [hu'] using huk)
  have hP : IsPGroup 2 ↥(Subgroup.zpowers u') := isPGroup_zpowers_of_pow' hu'k
  let P : Sylow 2 ↥U :=
    { toSubgroup := Subgroup.zpowers u'
      isPGroup' := hP
      is_maximal' := by
        intro Q hQ hle
        refine le_antisymm (fun q hq => ?_) hle
        obtain ⟨n, hn, j, hj⟩ := hU (q : G) q.2
        have hnU : n ∈ U := hNU hn
        have hnq : (⟨n, hnU⟩ : ↥U) = q * u' ^ (-j) := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, hcoe, hj]
          group
        have hnQ : (⟨n, hnU⟩ : ↥U) ∈ Q := by
          rw [hnq]
          exact Q.mul_mem hq (Q.zpow_mem (hle (Subgroup.mem_zpowers u')) _)
        obtain ⟨e, he⟩ := hQ ⟨_, hnQ⟩
        have h1 : orderOf n ∣ 2 ^ e := by
          apply orderOf_dvd_of_pow_eq_one
          have := congrArg (fun x : ↥Q => ((x : ↥U) : G)) he
          simpa using this
        have h2 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
        have hcop : Nat.Coprime (2 ^ e) (Nat.card N) :=
          Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hNodd)
        have h3 : orderOf n = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
        have hn1 : n = 1 := orderOf_eq_one_iff.mp h3
        have : q = u' ^ j := by
          apply Subtype.ext
          rw [hcoe, hj, hn1, one_mul]
        rw [this]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u') _ }
  have hτ' : (⟨τ, hτ⟩ : ↥U) ^ 2 ^ a = 1 := Subtype.ext (by simpa using hτa)
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (isPGroup_zpowers_of_pow' hτ')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥U P Q
  have hτQ : (⟨τ, hτ⟩ : ↥U) ∈ (Q : Subgroup ↥U) := hQ (Subgroup.mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hτQ
  obtain ⟨s, hs, hsg⟩ := hτQ
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  refine ⟨(g : G), g.2, j, ?_⟩
  have := congrArg (fun x : ↥U => (x : G)) hsg
  simpa [MulAut.smul_def, MulAut.conj_apply, hcoe] using this.symm

theorem two_pow_dvd_sum_pow {m : ℕ} (hm : Odd m) (k : ℕ) :
    2 ^ k ∣ ∑ i ∈ Finset.range (2 ^ k), m ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : ∑ i ∈ Finset.range (2 ^ (k + 1)), m ^ i =
        (1 + m ^ 2 ^ k) * ∑ i ∈ Finset.range (2 ^ k), m ^ i := by
      rw [pow_succ, mul_two, Finset.sum_range_add, add_mul, one_mul]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
    rw [h1, pow_succ']
    have h2 : 2 ∣ 1 + m ^ 2 ^ k := by
      have : Odd (m ^ 2 ^ k) := hm.pow
      obtain ⟨t, ht⟩ := this
      exact ⟨t + 1, by omega⟩
    exact mul_dvd_mul h2 ih

theorem exists_pow_eq_of_hom {K : Type*} [Field K] [Finite K] (f : Kˣ →* Kˣ) :
    ∃ m : ℕ, ∀ c : Kˣ, f c = c ^ m := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hmem : ∀ x : Kˣ, x ∈ Submonoid.powers g := fun x =>
    (mem_powers_iff_mem_zpowers).mpr (hg x)
  obtain ⟨m, hm⟩ := hmem (f g)
  refine ⟨m, fun c => ?_⟩
  obtain ⟨j, rfl⟩ := hmem c
  rw [map_pow, ← hm, ← pow_mul, ← pow_mul, mul_comm]

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

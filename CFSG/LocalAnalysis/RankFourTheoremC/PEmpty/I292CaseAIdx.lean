module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

open Subgroup

theorem not_dvd_index_comap_of_commutator {p : ℕ} (hp : p.Prime) {Y G : Type*} [Group Y]
    [Finite Y] [Group G] (θ : Y →* G) (D : Subgroup G) [D.Normal]
    (hab : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ D)
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤) :
    ¬ p ∣ (D.comap θ).index := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup Y := D.comap θ with hN
  haveI : N.Normal := Subgroup.normal_comap θ
  have hcomm : ∀ a b : Y ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 := hab (θ z⁻¹) (θ y⁻¹)
    rw [hN, Subgroup.mem_comap]
    simpa [map_mul, map_inv, mul_assoc] using h1
  rw [Subgroup.index_eq_card]
  intro hpdvd
  set n := Nat.card (Y ⧸ N) with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  set m := ordCompl[p] n with hm
  have hmcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hn0
  have hnm : p ^ n.factorization p * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  let ψ : (Y ⧸ N) →* (Y ⧸ N) :=
    { toFun := fun a => a ^ m
      map_one' := one_pow m
      map_mul' := fun a b => (Commute.mul_pow (hcomm a b) m) }
  let ρ : Y →* (Y ⧸ N) := ψ.comp (QuotientGroup.mk' N)
  haveI : ρ.ker.Normal := MonoidHom.normal_ker ρ
  have hρp : IsPGroup p ρ.range := by
    intro g
    obtain ⟨y, hy⟩ := g.2
    refine ⟨n.factorization p, ?_⟩
    apply Subtype.ext
    change (g : Y ⧸ N) ^ p ^ n.factorization p = 1
    rw [← hy]
    change ((QuotientGroup.mk y : Y ⧸ N) ^ m) ^ p ^ n.factorization p = 1
    rw [← pow_mul, mul_comm, hnm]
    exact pow_card_eq_one'
  have hq : IsPGroup p (Y ⧸ ρ.ker) := hρp.of_equiv (QuotientGroup.quotientKerEquivRange ρ).symm
  have hker : ρ.ker = ⊤ := hperf ρ.ker hq
  have hall : ∀ a : Y ⧸ N, a ^ m = 1 := by
    intro a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    have : y ∈ ρ.ker := by rw [hker]; exact Subgroup.mem_top y
    exact this
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have h1 : orderOf a ∣ m := orderOf_dvd_of_pow_eq_one (hall a)
  rw [ha] at h1
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hmcop h1

theorem exists_sylow_comap {p : ℕ} [Fact p.Prime] {Y G : Type*} [Group Y] [Group G]
    (θ : Y →* G) (D R : Subgroup G) (hRD : R ≤ D) (hDS : D ≤ θ.range)
    (hker : IsPGroup p θ.ker) (hR : IsPGroup p R) (hRidx : ¬ p ∣ R.relIndex D)
    (hDidx : ¬ p ∣ (D.comap θ).index) :
    ∃ Q : Sylow p Y, (Q : Subgroup Y) = R.comap θ := by
  have hQ : IsPGroup p (R.comap θ) := hR.comap_of_ker_isPGroup θ hker
  have hidx : (R.comap θ).index = R.relIndex D * D.relIndex θ.range := by
    rw [Subgroup.index_comap, Subgroup.relIndex_mul_relIndex R D θ.range hRD hDS]
  have hidx' : D.relIndex θ.range = (D.comap θ).index := (Subgroup.index_comap D θ).symm
  have hnd : ¬ p ∣ (R.comap θ).index := by
    rw [hidx, hidx']
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h1 | h1
    · exact hRidx h1
    · exact hDidx h1
  exact ⟨hQ.toSylow hnd, by simp⟩

theorem commute_of_ker_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y G : Type*} [Group Y]
    [Group G] (θ : Y →* G) (hker : IsPGroup p θ.ker) {T : Subgroup Y} (hT : IsPGroup 2 T)
    (hTC : ∀ t ∈ T, ∀ c ∈ θ.ker, t * c = c * t) {Q : Subgroup Y}
    (hQ : ∀ t ∈ T, ∀ q ∈ Q, θ t * θ q = θ q * θ t) : ∀ t ∈ T, ∀ q ∈ Q, t * q = q * t := by
  intro t ht q hq
  set c : Y := t * q * t⁻¹ * q⁻¹ with hc
  have hcker : c ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hc]
    have h := hQ t ht q hq
    simp only [map_mul, map_inv]
    rw [h]
    group
  have htc : t * c = c * t := hTC t ht c hcker
  have h1 : t * q = c * q * t := by rw [hc]; group
  have hkey : ∀ k : ℕ, t ^ k * q = c ^ k * q * t ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc t ^ (k + 1) * q = t * (t ^ k * q) := by rw [pow_succ', mul_assoc]
        _ = t * (c ^ k * q * t ^ k) := by rw [ih]
        _ = (t * c ^ k) * q * t ^ k := by simp only [mul_assoc]
        _ = (c ^ k * t) * q * t ^ k := by
          rw [(Commute.pow_right (show Commute t c from htc) k).eq]
        _ = c ^ k * (t * q) * t ^ k := by simp only [mul_assoc]
        _ = c ^ k * (c * q * t) * t ^ k := by rw [h1]
        _ = c ^ (k + 1) * q * t ^ (k + 1) := by rw [pow_succ, pow_succ']; simp only [mul_assoc]
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have hj' : t ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have h2 := hkey (2 ^ j)
  rw [hj', one_mul, mul_one] at h2
  have hc2 : c ^ (2 ^ j) = 1 := by
    have : c ^ (2 ^ j) * q = 1 * q := by rw [← h2, one_mul]
    exact mul_right_cancel this
  obtain ⟨m, hm⟩ := hker ⟨c, hcker⟩
  have hcm : c ^ (p ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ j) (p ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hc1 : c = 1 := by
    have h3 : orderOf c ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hc2
    have h4 : orderOf c ∣ p ^ m := orderOf_dvd_of_pow_eq_one hcm
    have h5 := Nat.dvd_gcd h3 h4
    rw [hcop.gcd_eq_one] at h5
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h5)
  have h6 : t * q * t⁻¹ * q⁻¹ = 1 := hc1
  calc t * q = t * q * t⁻¹ * q⁻¹ * (q * t) := by group
    _ = q * t := by rw [h6, one_mul]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

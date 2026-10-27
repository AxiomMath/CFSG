module

public import CFSG.CGT.PushingUpLit.BlocksCommuteQuasi1

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_eq_of_prime_top {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) : ∃ x ∈ X, orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card ↥X := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥X), hcard]
    exact dvd_mul_right _ _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hdvd
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem prime_top_ne_two {X : Subgroup G} (hX : IsShortGroup ↥X) {p : ℕ}
    (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) : p ≠ 2 := by
  rintro rfl
  have hpow : ∀ g ∈ X, ∃ k : ℕ, g ^ 2 ^ k ∈ oTwoIn X := by
    intro g hg
    refine ⟨1, ?_⟩
    have h1 : (⟨g, hg⟩ : ↥X) ^ 2 ∈ pCore 2 ↥X := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      rw [QuotientGroup.mk_pow]
      have := pow_card_eq_one' (G := ↥X ⧸ pCore 2 ↥X)
        (x := ((⟨g, hg⟩ : ↥X) : ↥X ⧸ pCore 2 ↥X))
      rwa [hcard] at this
    exact ⟨_, h1, by simp⟩
  have hle := noTwoQuot_of_short hX (oTwoIn X)
    (fun g hg n hn => conj_mem_oTwoIn (Subgroup.le_normalizer hg) hn) hpow
  have htop : pCore 2 ↥X = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun g => ?_
    obtain ⟨h, hh, hg⟩ := hle g.2
    have : h = g := Subtype.ext hg
    rwa [← this]
  have h1 : Nat.card (↥X ⧸ (⊤ : Subgroup ↥X)) = 1 := Subgroup.index_top
  rw [htop] at hcard
  omega

theorem decomp_of_prime_top {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) (hp2 : p ≠ 2) {x : G} (hx : x ∈ X)
    (hxo : orderOf x = p) : ∀ g ∈ X, ∃ r ∈ oTwoIn X, ∃ k : ℕ, g = r * x ^ k := by
  have : Fact (Nat.card (↥X ⧸ pCore 2 ↥X)).Prime := ⟨hcard ▸ hp⟩
  intro g hg
  let x' : ↥X := ⟨x, hx⟩
  have hx1 : (x' : ↥X ⧸ pCore 2 ↥X) ≠ 1 := by
    intro h
    have h1 : x' ∈ pCore 2 ↥X := (QuotientGroup.eq_one_iff _).1 h
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := ↥X)) ⟨x', h1⟩
    have h2 : x ^ 2 ^ k = 1 := by
      have := congrArg (fun a : ↥(pCore 2 ↥X) => ((a : ↥X) : G)) hk
      simpa [x'] using this
    have h3 : p ∣ 2 ^ k := hxo ▸ orderOf_dvd_of_pow_eq_one h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
  have hzp : Subgroup.zpowers (x' : ↥X ⧸ pCore 2 ↥X) = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      (Subgroup.zpowers (x' : ↥X ⧸ pCore 2 ↥X)) with h | h
    · exact absurd (Subgroup.zpowers_eq_bot.1 h) hx1
    · exact h
  have hmem : ((⟨g, hg⟩ : ↥X) : ↥X ⧸ pCore 2 ↥X) ∈
      Subgroup.zpowers (x' : ↥X ⧸ pCore 2 ↥X) := by
    rw [hzp]
    trivial
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  have hq : (x' ^ n)⁻¹ * ⟨g, hg⟩ ∈ pCore 2 ↥X :=
    QuotientGroup.eq.1 (by rw [QuotientGroup.mk_pow]; exact hn)
  have hr : (⟨g, hg⟩ : ↥X) * (x' ^ n)⁻¹ ∈ pCore 2 ↥X := by
    have := (pCore_normal (p := 2) (G := ↥X)).conj_mem _ hq (x' ^ n)
    simpa [mul_assoc] using this
  refine ⟨((⟨g, hg⟩ * (x' ^ n)⁻¹ : ↥X) : G), ⟨_, hr, rfl⟩, n, ?_⟩
  simp [x']

theorem oTwoIn_le_blockU_of_prime {X : Subgroup G} (hX : IsShortGroup ↥X) {p : ℕ}
    (hp : p.Prime) (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) {x : G} (hx : x ∈ X)
    (hxo : orderOf x = p) : oTwoIn X ≤ blockU X := by
  have hp2 := prime_top_ne_two hX hcard
  have hdec := decomp_of_prime_top hp hcard hp2 hx hxo
  let U' : Subgroup ↥X := (blockU X).subgroupOf X
  have hU'n : U'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (blockU_le X)).2 (le_normalizer_blockU X)
  let π : ↥X →* ↥X ⧸ U' := QuotientGroup.mk' U'
  let x' : ↥X := ⟨x, hx⟩
  have hcentral : ∀ (r y : ↥X), (r : G) ∈ oTwoIn X → π y * π r = π r * π y := by
    intro r y hr
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.2 ?_
    show ((y * r)⁻¹ * (r * y) : ↥X) ∈ U'
    rw [Subgroup.mem_subgroupOf]
    have h1 := commutator_mem_blockU_of_mem (inv_mem y.2) (inv_mem hr)
    have h2 := inv_mem h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hxc : ∀ g : ↥X, π g * π x' = π x' * π g := by
    intro g
    obtain ⟨r, hr, k, hk⟩ := hdec g g.2
    have hg : g = ⟨r, oTwoIn_le X hr⟩ * x' ^ k := Subtype.ext (by simpa [x'] using hk)
    rw [hg, map_mul, map_pow]
    have c1 := hcentral ⟨r, oTwoIn_le X hr⟩ x' hr
    have c2 : Commute (π x') (π x' ^ k) := (Commute.refl _).pow_right k
    calc π ⟨r, oTwoIn_le X hr⟩ * π x' ^ k * π x'
        = π ⟨r, oTwoIn_le X hr⟩ * (π x' ^ k * π x') := by rw [mul_assoc]
      _ = π ⟨r, oTwoIn_le X hr⟩ * (π x' * π x' ^ k) := by rw [c2.eq]
      _ = (π ⟨r, oTwoIn_le X hr⟩ * π x') * π x' ^ k := by rw [mul_assoc]
      _ = (π x' * π ⟨r, oTwoIn_le X hr⟩) * π x' ^ k := by rw [← c1]
      _ = π x' * (π ⟨r, oTwoIn_le X hr⟩ * π x' ^ k) := by rw [mul_assoc]
  let N : Subgroup G := (Subgroup.zpowers (π x')).comap π |>.map X.subtype
  have hNn : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    obtain ⟨n', hn', rfl⟩ := hn
    have hmem : π n' ∈ Subgroup.zpowers (π x') := hn'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hcomm : Commute (π ⟨g, hg⟩) (π n') := by
      rw [← hm]
      exact (show Commute (π ⟨g, hg⟩) (π x') from hxc ⟨g, hg⟩).zpow_right m
    refine ⟨⟨g, hg⟩ * n' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
    show π (⟨g, hg⟩ * n' * ⟨g, hg⟩⁻¹) ∈ Subgroup.zpowers (π x')
    rw [map_mul, map_mul, map_inv, hcomm.eq, mul_inv_cancel_right]
    exact hmem
  have hpowN : ∀ g ∈ X, ∃ k : ℕ, g ^ 2 ^ k ∈ N := by
    intro g hg
    obtain ⟨r, hr, j, hj⟩ := hdec g hg
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_oTwoIn hr
    refine ⟨k, ⟨⟨g, hg⟩ ^ 2 ^ k, ?_, by simp⟩⟩
    show π (⟨g, hg⟩ ^ 2 ^ k) ∈ Subgroup.zpowers (π x')
    have hg' : (⟨g, hg⟩ : ↥X) = ⟨r, oTwoIn_le X hr⟩ * x' ^ j := Subtype.ext (by simpa [x'] using hj)
    have hr1 : (⟨r, oTwoIn_le X hr⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    have hc : Commute (π ⟨r, oTwoIn_le X hr⟩) (π x' ^ j) :=
      (show Commute (π ⟨r, oTwoIn_le X hr⟩) (π x') from
        (hcentral ⟨r, oTwoIn_le X hr⟩ x' hr).symm).pow_right j
    rw [hg', map_pow, map_mul, map_pow, hc.mul_pow, ← map_pow, hr1, map_one, one_mul,
      ← pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hXN : X ≤ N := noTwoQuot_of_short hX N hNn hpowN
  intro r hr
  have hrX : r ∈ X := oTwoIn_le X hr
  obtain ⟨r', hr', hrr⟩ := hXN hrX
  have hr'eq : r' = ⟨r, hrX⟩ := Subtype.ext hrr
  subst hr'eq
  have hmem : π ⟨r, hrX⟩ ∈ Subgroup.zpowers (π x') := hr'
  have hxp : (π x') ^ p = 1 := by
    rw [← map_pow]
    have : x' ^ p = 1 := Subtype.ext (by simpa [x'] using hxo ▸ pow_orderOf_eq_one x)
    rw [this, map_one]
  have hrp : (π ⟨r, hrX⟩) ^ p = 1 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hrU : r ^ p ∈ blockU X := by
    rw [← map_pow] at hrp
    have := (QuotientGroup.eq_one_iff _).1 hrp
    simpa [U', Subgroup.mem_subgroupOf] using this
  exact mem_of_pow_mem_odd (exists_pow_eq_one_of_mem_oTwoIn hr) (hp.odd_of_ne_two hp2) _ hrU

end CFSG.CGT.PushingUpLit

module

public import CFSG.GH74.Generic.BProg.B3.LocBalSL4Abs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace LocBalSL4Three

open LocBalSL4Abs

section Twist

variable {X : Type} [Group X] [Finite X]

instance finite_mulAut_three : Finite (MulAut X) :=
  Finite.of_injective (fun f : MulAut X => (f : X → X)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem oddCore_props {G : Type*} [Group G] [Finite G] (b : G) :
    involutionOddCore b ≤ centralizer ({b} : Set G) ∧
    (∀ g ∈ centralizer ({b} : Set G), ∀ n ∈ involutionOddCore b,
      g * n * g⁻¹ ∈ involutionOddCore b) ∧
    Odd (Nat.card ↥(involutionOddCore b)) := by
  refine ⟨involutionOddCore_le_centralizer b, ?_, ?_⟩
  · intro g hg n hn
    obtain ⟨n₀, hn₀, rfl⟩ := hn
    refine ⟨⟨g, hg⟩ * n₀ * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance n₀ hn₀ ⟨g, hg⟩
  · unfold involutionOddCore
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), oddCore_eq_pPrimeCore]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

omit [Finite X] in
theorem conj_injective_of_centerless (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  apply hZ t
  intro g
  have h2 := congrArg (fun f : MulAut X => f g) ht
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

theorem twist_mem (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1)
    {H : Subgroup (MulAut X)} (hH : (MulAut.conj : X →* MulAut X).range ≤ H) {t : X} {c : ↥H}
    (hc : c ∈ involutionOddCore (phi hH t)) :
    ∃ Q : Subgroup X, Q ≤ centralizer ({t} : Set X) ∧
      (∀ w ∈ centralizer ({t} : Set X), ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) ∧ Odd (Nat.card ↥Q) ∧
      ∀ w ∈ centralizer ({t} : Set X), ((c : ↥H) : MulAut X) w * w⁻¹ ∈ Q := by
  obtain ⟨hN1, hN2, hN3⟩ := oddCore_props (phi hH t)
  have hφinj : Function.Injective (phi hH) := fun a b h =>
    conj_injective_of_centerless hZ (congrArg Subtype.val h)
  set ĉ : MulAut X := (c : MulAut X) with hĉ
  let Q₀ : Subgroup X := (involutionOddCore (phi hH t)).comap (phi hH)
  have hphiC : ∀ w ∈ centralizer ({t} : Set X), phi hH w ∈ centralizer ({phi hH t} : Set ↥H) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    rw [← map_mul, ← map_mul, hw]
  have hQC : Q₀ ≤ centralizer ({t} : Set X) := by
    intro q hq
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hN1 hq)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hφinj
    rw [map_mul, map_mul]
    exact h1
  have hQn : ∀ w ∈ centralizer ({t} : Set X), ∀ q ∈ Q₀, w * q * w⁻¹ ∈ Q₀ := by
    intro w hw q hq
    have := hN2 (phi hH w) (hphiC w hw) (phi hH q) hq
    show phi hH (w * q * w⁻¹) ∈ involutionOddCore (phi hH t)
    rw [map_mul, map_mul, map_inv]
    exact this
  have hQo : Odd (Nat.card ↥Q₀) := by
    have h1 : Q₀.map (phi hH) ≤ involutionOddCore (phi hH t) := Subgroup.map_comap_le _ _
    have h2 := Subgroup.card_dvd_of_le h1
    rw [Subgroup.card_map_of_injective hφinj] at h2
    exact Odd.of_dvd_nat hN3 h2
  refine ⟨Q₀, hQC, hQn, hQo, ?_⟩
  intro w hw
  have h1 : phi hH (ĉ w * w⁻¹) = c * (phi hH w * c⁻¹ * (phi hH w)⁻¹) := by
    apply Subtype.ext
    simp only [coe_phi, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [← aut_mul_conj_mul_inv ĉ w, hĉ]
    group
  show phi hH (ĉ w * w⁻¹) ∈ involutionOddCore (phi hH t)
  rw [h1]
  exact Subgroup.mul_mem _ hc (hN2 _ (hphiC w hw) _ (Subgroup.inv_mem _ hc))

end Twist

section Complement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_odd_complement {z : G} (hzc : ∀ g : G, g * z = z * g) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    {m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 * m) :
    ∃ K : Subgroup G, (∀ g : G, g ∈ K ↔ g ^ m = 1) ∧ Nat.card ↥K = m := by
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hNc : Subgroup.zpowers z ≤ Subgroup.center G := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_center_iff.mpr hzc
  have hNn : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hNc
  have hNcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hord]
  have hidx : (Subgroup.zpowers z).index = m := by
    have h1 := (Subgroup.zpowers z).card_mul_index
    rw [hNcard, hcard] at h1
    omega
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers z)) (Subgroup.zpowers z).index := by
    rw [hNcard, hidx]
    exact Nat.coprime_two_left.mpr hm
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKcard : Nat.card ↥K = m := by
    have h1 := hK.card_mul_card
    rw [hNcard, hcard] at h1
    omega
  refine ⟨K, fun g => ⟨fun hg => ?_, fun hg => ?_⟩, hKcard⟩
  · have := pow_card_eq_one' (G := ↥K) (x := ⟨g, hg⟩)
    rw [hKcard] at this
    exact congrArg Subtype.val this
  · have hg' : g ∈ Subgroup.zpowers z ⊔ K := by
      rw [hK.sup_eq_top]
      trivial
    obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg'
    have hnz : n = 1 ∨ n = z := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rcases Int.emod_two_eq_zero_or_one j with h0 | h1
      · left
        rw [← Int.emod_add_mul_ediv j 2, h0, zpow_add, zpow_mul]
        have : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
        rw [this]
        simp
      · right
        rw [← Int.emod_add_mul_ediv j 2, h1, zpow_add, zpow_mul]
        have : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
        rw [this]
        simp
    have hkm : k ^ m = 1 := by
      have := pow_card_eq_one' (G := ↥K) (x := ⟨k, hk⟩)
      rw [hKcard] at this
      exact congrArg Subtype.val this
    have hncomm : Commute n k := by
      rcases hnz with h | h
      · rw [h]
        exact Commute.one_left k
      · rw [h]
        exact (hzc k).symm
    rw [hncomm.mul_pow, hkm, mul_one] at hg
    rcases hnz with h | h
    · rw [h, one_mul]
      exact hk
    · exfalso
      have hzm : z ^ m = z := by
        obtain ⟨j, hj⟩ := hm
        rw [hj, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
      rw [h, hzm] at hg
      exact hz1 hg

end Complement

section QBot

variable {P X : Type} [Group P] [Group X] [Finite P]

omit [Finite P] in
theorem Q_eq_bot {π : P →* X} (hπ : Function.Surjective π) {z : P} (hzc : ∀ g : P, g * z = z * g)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hker : ∀ g : P, π g = 1 ↔ g = 1 ∨ g = z) {u : P}
    (hO : ∀ R : Subgroup P, R ≤ centralizer ({u} : Set P) →
      (∀ g ∈ centralizer ({u} : Set P), ∀ r ∈ R, g * r * g⁻¹ ∈ R) → Odd (Nat.card ↥R) → R = ⊥)
    {Q : Subgroup X} (hQC : Q ≤ centralizer ({π u} : Set X))
    (hQn : ∀ w ∈ centralizer ({π u} : Set X), ∀ q ∈ Q, w * q * w⁻¹ ∈ Q)
    (hQo : Odd (Nat.card ↥Q)) : Q = ⊥ := by
  have : Finite ↥Q :=
    Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (fun h => by simp [h] at hQo)).ne'
  set m := Nat.card ↥Q with hm
  let R : Subgroup P := Q.comap π
  have hz2' : ∀ k : ℕ, z ^ (2 * k) = 1 := fun k => by rw [pow_mul, sq, hz2, one_pow]
  have hRC : R ≤ centralizer ({u} : Set P) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hπg : π g * π u = π u * π g := Subgroup.mem_centralizer_singleton_iff.mp (hQC hg)
    have hε : π (g * u * g⁻¹ * u⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπg]
      group
    have hε' : (g * u * g⁻¹ * u⁻¹ = 1) ∨ (g * u * g⁻¹ * u⁻¹ = z) := (hker _).1 hε
    rcases hε' with h1 | h1
    · calc g * u = (g * u * g⁻¹ * u⁻¹) * (u * g) := by group
        _ = u * g := by rw [h1, one_mul]
    · exfalso
      have hgu : g * u * g⁻¹ = z * u := by
        calc g * u * g⁻¹ = (g * u * g⁻¹ * u⁻¹) * u := by group
          _ = z * u := by rw [h1]
      have hpow : ∀ k : ℕ, g ^ k * u * (g ^ k)⁻¹ = z ^ k * u := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc g ^ (k + 1) * u * (g ^ (k + 1))⁻¹ = g * (g ^ k * u * (g ^ k)⁻¹) * g⁻¹ := by group
            _ = g * (z ^ k * u) * g⁻¹ := by rw [ih]
            _ = z ^ k * (g * u * g⁻¹) := by
              have hzg : g * z ^ k = z ^ k * g := by
                have := (Commute.pow_right (show Commute g z from hzc g) k).eq
                exact this
              calc g * (z ^ k * u) * g⁻¹ = (g * z ^ k) * u * g⁻¹ := by group
                _ = (z ^ k * g) * u * g⁻¹ := by rw [hzg]
                _ = z ^ k * (g * u * g⁻¹) := by group
            _ = z ^ (k + 1) * u := by rw [hgu]; group
      have hgm : π (g ^ m) = 1 := by
        rw [map_pow]
        have := pow_card_eq_one' (G := ↥Q) (x := ⟨π g, hg⟩)
        exact congrArg Subtype.val this
      have hgmz : g ^ m * u = u * g ^ m := by
        rcases (hker _).1 hgm with h2 | h2
        · rw [h2]; simp
        · rw [h2]; exact (hzc u).symm
      have h3 : z ^ m * u = u := by
        have := hpow m
        calc z ^ m * u = g ^ m * u * (g ^ m)⁻¹ := this.symm
          _ = u := by rw [hgmz]; group
      have hzm : z ^ m = z := by
        obtain ⟨j, hj⟩ := hQo
        rw [hj, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
      rw [hzm] at h3
      have : z = 1 := by
        have h4 : z * u = 1 * u := by rw [h3, one_mul]
        exact mul_right_cancel h4
      exact hz1 this
  have hRn : ∀ g ∈ centralizer ({u} : Set P), ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    have hg' : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hπg : π g ∈ centralizer ({π u} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg']
    show π (g * r * g⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact hQn _ hπg _ hr
  have hzR : z ∈ R := by
    show π z ∈ Q
    rw [(hker z).2 (Or.inr rfl)]
    exact Q.one_mem
  let z' : ↥R := ⟨z, hzR⟩
  let f : ↥R →* ↥Q := (π.comp R.subtype).codRestrict Q (fun r => r.2)
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨p, hp⟩ := hπ (q : X)
    have hpR : p ∈ R := by
      show π p ∈ Q
      rw [hp]
      exact q.2
    exact ⟨⟨p, hpR⟩, Subtype.ext hp⟩
  have hker_f : f.ker = Subgroup.zpowers z' := by
    apply le_antisymm
    · intro r hr
      have h1 : π (r : P) = 1 := congrArg Subtype.val hr
      rcases (hker _).1 h1 with h2 | h2
      · have : r = 1 := Subtype.ext h2
        rw [this]
        exact Subgroup.one_mem _
      · have : r = z' := Subtype.ext h2
        rw [this]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact Subtype.ext ((hker z).2 (Or.inr rfl))
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hord' : orderOf z' = 2 := orderOf_eq_prime (by rw [sq]; exact hz'2) hz'1
  have hRcard : Nat.card ↥R = 2 * m := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hker_f, Nat.card_zpowers, hord', MonoidHom.range_eq_top.mpr hfsurj,
      Subgroup.card_top] at h1
    exact h1.symm
  have hz'c : ∀ g : ↥R, g * z' = z' * g := fun g => Subtype.ext (hzc g)
  obtain ⟨K, hKmem, hKcard⟩ := exists_odd_complement hz'c hz'2 hz'1 hQo hRcard
  let R'' : Subgroup P := K.map R.subtype
  have hR''C : R'' ≤ centralizer ({u} : Set P) := by
    rintro _ ⟨k, hk, rfl⟩
    exact hRC k.2
  have hR''n : ∀ g ∈ centralizer ({u} : Set P), ∀ r ∈ R'', g * r * g⁻¹ ∈ R'' := by
    intro g hg r hr
    obtain ⟨k, hk, rfl⟩ := hr
    have hgR : g * (k : P) * g⁻¹ ∈ R := hRn g hg _ k.2
    refine ⟨⟨_, hgR⟩, ?_, rfl⟩
    show (⟨g * (k : P) * g⁻¹, hgR⟩ : ↥R) ∈ K
    rw [hKmem]
    apply Subtype.ext
    have := (hKmem k).1 hk
    have h1 : ((k : P)) ^ m = 1 := congrArg Subtype.val this
    show (g * (k : P) * g⁻¹) ^ m = 1
    rw [conj_pow, h1]
    group
  have hR''odd : Odd (Nat.card ↥R'') := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hKcard]
    exact hQo
  have hR''bot := hO R'' hR''C hR''n hR''odd
  have hKbot : K = ⊥ := by
    have h1 : Nat.card ↥R'' = 1 := by rw [hR''bot]; exact Subgroup.card_bot
    rw [Subgroup.card_map_of_injective R.subtype_injective, hKcard] at h1
    have h2 : Nat.card ↥K = 1 := by rw [hKcard]; exact h1
    exact Subgroup.eq_bot_of_card_eq K h2
  have hm1 : m = 1 := by
    rw [← hKcard, hKbot]
    exact Subgroup.card_bot
  exact Subgroup.eq_bot_of_card_eq Q hm1

end QBot

end LocBalSL4Three

end CFSG.GH74.Generic.BProg.B3

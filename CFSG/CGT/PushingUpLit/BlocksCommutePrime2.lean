module

public import CFSG.CGT.PushingUpLit.BlocksCommutePrime1

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mem_blockU_left {X : Subgroup G} {u x : G} (hu : u ∈ blockU X)
    (hx : x ∈ X) : ⁅u, x⁆ ∈ blockU X := by
  have := inv_mem (commutator_mem_blockU_of_mem hx (blockU_le_oTwoIn X hu))
  simpa using this

theorem blockU_surj_of_prime {X : Subgroup G} (hX : IsShortGroup ↥X) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) {x : G} (hx : x ∈ X) (hxo : orderOf x = p) :
    ∀ v ∈ blockU X, ∃ u ∈ blockU X, ⁅u, x⁆ = v := by
  have hp2 := prime_top_ne_two hX hcard
  have hdec := decomp_of_prime_top hp hcard hp2 hx hxo
  have hR : oTwoIn X = blockU X :=
    le_antisymm (oTwoIn_le_blockU_of_prime hX hp hcard hx hxo) (blockU_le_oTwoIn X)
  have hcomm : ∀ {u v : G}, u ∈ blockU X → v ∈ blockU X → u * v = v * u :=
    fun hu hv => blockU_commute hX hu hv
  let D : Subgroup G :=
    { carrier := {d | ∃ u ∈ blockU X, ⁅u, x⁆ = d}
      one_mem' := ⟨1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        refine ⟨u' * u, mul_mem hu' hu, ?_⟩
        have hc : u' * ⁅u, x⁆ = ⁅u, x⁆ * u' := hcomm hu' (commutator_mem_blockU_left hu hx)
        have e : ⁅u' * u, x⁆ = u' * ⁅u, x⁆ * u'⁻¹ * ⁅u', x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, hc]
        group
      inv_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        refine ⟨u⁻¹, inv_mem hu, ?_⟩
        have hc : u⁻¹ * (x * u * x⁻¹) = (x * u * x⁻¹) * u⁻¹ :=
          hcomm (inv_mem hu) (conj_mem_blockU (Subgroup.le_normalizer hx) hu)
        calc ⁅u⁻¹, x⁆ = u⁻¹ * (x * u * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
          _ = (x * u * x⁻¹) * u⁻¹ := hc
          _ = ⁅u, x⁆⁻¹ := by simp [commutatorElement_def, mul_assoc] }
  have h1 : blockU X = ⁅blockU X, X⁆ := by
    calc blockU X = ⁅oTwoIn X, X⁆ := rfl
      _ = ⁅blockU X, X⁆ := by rw [hR]
  have hUD : blockU X ≤ D := by
    rw [h1]
    refine Subgroup.commutator_le.2 fun u hu g hg => ?_
    obtain ⟨r, hr, k, hk⟩ := hdec g hg
    have hrU : r ∈ blockU X := hR ▸ hr
    have hkey : ∀ k : ℕ, ⁅u, x ^ k⁆ ∈ D := by
      intro k
      induction k with
      | zero => exact ⟨1, one_mem _, by simp⟩
      | succ k ih =>
        have e : ⁅u, x ^ (k + 1)⁆ = ⁅u, x ^ k⁆ * (x ^ k * ⁅u, x⁆ * (x ^ k)⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        refine mul_mem ih ⟨x ^ k * u * (x ^ k)⁻¹,
          conj_mem_blockU (Subgroup.le_normalizer (pow_mem hx k)) hu, ?_⟩
        simp only [commutatorElement_def]
        group
    have hux : ⁅u, x ^ k⁆ ∈ blockU X := commutator_mem_blockU_left hu (pow_mem hx k)
    have hc : r * ⁅u, x ^ k⁆ = ⁅u, x ^ k⁆ * r := hcomm hrU hux
    have hcu : u * r = r * u := hcomm hu hrU
    have e : ⁅u, r * x ^ k⁆ = ⁅u, x ^ k⁆ := by
      have e' : ⁅u, r * x ^ k⁆ = ⁅u, r⁆ * (r * ⁅u, x ^ k⁆ * r⁻¹) := by
        simp only [commutatorElement_def]
        group
      have hur : ⁅u, r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcu
      rw [e', hur, one_mul, hc]
      group
    rw [hk, e]
    exact hkey k
  intro v hv
  exact hUD hv

theorem blockZ_eq_bot_of_prime {X : Subgroup G} (hX : IsShortGroup ↥X) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) {x : G} (hx : x ∈ X) (hxo : orderOf x = p) :
    blockZ X = ⊥ := by
  have hp2 := prime_top_ne_two hX hcard
  have hsurj := blockU_surj_of_prime hX hp hcard hx hxo
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨u₀, hu₀, hzu⟩ := hsurj z hz.1
  have hcz : x * z = z * x := (Subgroup.mem_centralizer_iff.1 hz.2) x hx
  have hxz : ∀ k : ℕ, x * (z ^ k)⁻¹ * x⁻¹ = (z ^ k)⁻¹ := by
    intro k
    have : x * (z ^ k)⁻¹ = (z ^ k)⁻¹ * x := (((show Commute x z from hcz).pow_right k).inv_right).eq
    rw [this]
    group
  have e1 : x * u₀ * x⁻¹ = z⁻¹ * u₀ := by
    rw [← hzu]
    simp only [commutatorElement_def]
    group
  have key : ∀ k : ℕ, x ^ k * u₀ * (x ^ k)⁻¹ = (z ^ k)⁻¹ * u₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * u₀ * (x ^ (k + 1))⁻¹ = x * (x ^ k * u₀ * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * ((z ^ k)⁻¹ * u₀) * x⁻¹ := by rw [ih]
        _ = (x * (z ^ k)⁻¹ * x⁻¹) * (x * u₀ * x⁻¹) := by group
        _ = (z ^ k)⁻¹ * (z⁻¹ * u₀) := by rw [hxz k, e1]
        _ = (z ^ (k + 1))⁻¹ * u₀ := by group
  have hzp : z ^ p = 1 := by
    have h4 := key p
    rw [hxp] at h4
    have h5 : (z ^ p)⁻¹ = 1 := by
      have : (z ^ p)⁻¹ * u₀ = 1 * u₀ := by simpa using h4.symm
      exact mul_right_cancel this
    exact inv_eq_one.1 h5
  exact mem_of_pow_mem_odd (exists_pow_eq_one_of_mem_oTwoIn (blockU_le_oTwoIn X hz.1))
    (hp.odd_of_ne_two hp2) ⊥ (by rw [hzp]; exact one_mem _)

omit [Finite G] in
theorem conj_pow_mem_of_invariant {x : G} {N : Subgroup G} (hN : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (k : ℕ) {n : G} (hn : n ∈ N) : x ^ k * n * (x ^ k)⁻¹ ∈ N := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    have := hN _ ih
    have e : x ^ (k + 1) * n * (x ^ (k + 1))⁻¹ = x * (x ^ k * n * (x ^ k)⁻¹) * x⁻¹ := by group
    rw [e]
    exact this

theorem blockU_irr_of_prime {X : Subgroup G} (hX : IsShortGroup ↥X) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) {x : G} (hx : x ∈ X) (hxo : orderOf x = p) :
    ∀ N : Subgroup G, N ≤ blockU X → (∀ n ∈ N, x * n * x⁻¹ ∈ N) → N = ⊥ ∨ N = blockU X := by
  have hp2 := prime_top_ne_two hX hcard
  have hdec := decomp_of_prime_top hp hcard hp2 hx hxo
  have hR : oTwoIn X = blockU X :=
    le_antisymm (oTwoIn_le_blockU_of_prime hX hp hcard hx hxo) (blockU_le_oTwoIn X)
  have hZ := blockZ_eq_bot_of_prime hX hp hcard hx hxo
  intro N hNU hNx
  have hNn : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    obtain ⟨r, hr, k, hk⟩ := hdec g hg
    have hrU : r ∈ blockU X := hR ▸ hr
    have h1 := conj_pow_mem_of_invariant hNx k hn
    have hc : r * (x ^ k * n * (x ^ k)⁻¹) = (x ^ k * n * (x ^ k)⁻¹) * r :=
      blockU_commute hX hrU (hNU h1)
    rw [hk]
    have : r * x ^ k * n * (r * x ^ k)⁻¹ = x ^ k * n * (x ^ k)⁻¹ := by
      calc r * x ^ k * n * (r * x ^ k)⁻¹ = (r * (x ^ k * n * (x ^ k)⁻¹)) * r⁻¹ := by group
        _ = ((x ^ k * n * (x ^ k)⁻¹) * r) * r⁻¹ := by rw [hc]
        _ = x ^ k * n * (x ^ k)⁻¹ := by group
    rw [this]
    exact h1
  rcases blockU_irred_of_short hX N (by rw [hZ]; exact bot_le) hNU hNn with h | h
  · left
    rw [h, hZ]
  · right
    exact h

theorem blockU_sq_of_prime {X : Subgroup G} (hX : IsShortGroup ↥X) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) {x : G} (hx : x ∈ X) (hxo : orderOf x = p) :
    ∀ u ∈ blockU X, u * u = 1 := by
  have hirr := blockU_irr_of_prime hX hp hcard hx hxo
  have hcomm : ∀ {u v : G}, u ∈ blockU X → v ∈ blockU X → u * v = v * u :=
    fun hu hv => blockU_commute hX hu hv
  let N : Subgroup G :=
    { carrier := {u | u ∈ blockU X ∧ u * u = 1}
      one_mem' := ⟨one_mem _, one_mul 1⟩
      mul_mem' := by
        rintro u v ⟨hu, hu1⟩ ⟨hv, hv1⟩
        refine ⟨mul_mem hu hv, ?_⟩
        have hc := hcomm hv hu
        calc u * v * (u * v) = u * (v * u) * v := by group
          _ = u * (u * v) * v := by rw [hc]
          _ = (u * u) * (v * v) := by group
          _ = 1 := by rw [hu1, hv1, one_mul]
      inv_mem' := by
        rintro u ⟨hu, hu1⟩
        refine ⟨inv_mem hu, ?_⟩
        calc u⁻¹ * u⁻¹ = (u * u)⁻¹ := by group
          _ = 1 := by rw [hu1, inv_one] }
  have hNU : N ≤ blockU X := fun u hu => hu.1
  have hNx : ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    rintro n ⟨hn, hn1⟩
    refine ⟨conj_mem_blockU (Subgroup.le_normalizer hx) hn, ?_⟩
    calc x * n * x⁻¹ * (x * n * x⁻¹) = x * (n * n) * x⁻¹ := by group
      _ = 1 := by rw [hn1]; group
  have hUP : IsPGroup 2 ↥(blockU X) := (isPGroup_oTwoIn X).to_le (blockU_le_oTwoIn X)
  have hnt : Nontrivial ↥(blockU X) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 (blockU_ne_bot_of_short hX)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn0, hn⟩ := (hUP.nontrivial_iff_card).1 hnt
  have h2 : 2 ∣ Nat.card ↥(blockU X) := by
    rw [hn]
    exact dvd_pow_self 2 (ne_of_gt hn0)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(blockU X)) 2 h2
  have hu1 : (u : G) ≠ 1 := by
    intro h
    have : u = 1 := Subtype.ext h
    rw [this, orderOf_one] at hu
    omega
  have huN : (u : G) ∈ N := by
    refine ⟨u.2, ?_⟩
    have := pow_orderOf_eq_one u
    rw [hu, pow_two] at this
    exact congrArg Subtype.val this
  rcases hirr N hNU hNx with h | h
  · exfalso
    rw [h] at huN
    exact hu1 huN
  · intro v hv
    have : v ∈ N := by rw [h]; exact hv
    exact this.2

theorem blockU_not_le_zpowers_of_prime {X : Subgroup G} (hX : IsShortGroup ↥X) {p : ℕ}
    (hp : p.Prime) (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) {x : G} (hx : x ∈ X)
    (hxo : orderOf x = p) : ∀ e ∈ blockU X, ¬ blockU X ≤ Subgroup.zpowers e := by
  have hp2 := prime_top_ne_two hX hcard
  have hdec := decomp_of_prime_top hp hcard hp2 hx hxo
  have hR : oTwoIn X = blockU X :=
    le_antisymm (oTwoIn_le_blockU_of_prime hX hp hcard hx hxo) (blockU_le_oTwoIn X)
  have hZ := blockZ_eq_bot_of_prime hX hp hcard hx hxo
  have hsq := blockU_sq_of_prime hX hp hcard hx hxo
  intro e he hle
  have hne : e ≠ 1 := by
    intro h1
    have : blockU X ≤ ⊥ := by
      rw [h1, Subgroup.zpowers_one_eq_bot] at hle
      exact hle
    exact blockU_ne_bot_of_short hX (le_bot_iff.1 this)
  have hv : ∀ v ∈ blockU X, v = 1 ∨ v = e := by
    intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hle hv)
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, zpow_two, hsq e he, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, zpow_two, hsq e he, one_zpow, one_mul, zpow_one]
  have hxe : x * e * x⁻¹ = e := by
    rcases hv _ (conj_mem_blockU (Subgroup.le_normalizer hx) he) with h | h
    · exfalso
      apply hne
      have : x * e * x⁻¹ = 1 := h
      simpa using this
    · exact h
  have hxke : ∀ k : ℕ, x ^ k * e * (x ^ k)⁻¹ = e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * e * (x ^ (k + 1))⁻¹ = x * (x ^ k * e * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = e := by rw [ih, hxe]
  have hecent : e ∈ blockZ X := by
    refine Subgroup.mem_inf.2 ⟨he, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨r, hr, k, hk⟩ := hdec g hg
    have hrU : r ∈ blockU X := hR ▸ hr
    have hc : r * e = e * r := blockU_commute hX hrU he
    rw [hk]
    calc r * x ^ k * e = r * (x ^ k * e * (x ^ k)⁻¹) * x ^ k := by group
      _ = r * e * x ^ k := by rw [hxke k]
      _ = e * (r * x ^ k) := by rw [hc]; group
  rw [hZ] at hecent
  exact hne hecent

structure IsPrimeBlockData (X : Subgroup G) (p : ℕ) (x : G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  mem : x ∈ X
  order : orderOf x = p
  decomp : ∀ g ∈ X, ∃ r ∈ oTwoIn X, ∃ k : ℕ, g = r * x ^ k
  oTwoIn_eq : oTwoIn X = blockU X
  surj : ∀ v ∈ blockU X, ∃ u ∈ blockU X, ⁅u, x⁆ = v
  blockZ_eq : blockZ X = ⊥
  irr : ∀ N : Subgroup G, N ≤ blockU X → (∀ n ∈ N, x * n * x⁻¹ ∈ N) → N = ⊥ ∨ N = blockU X
  sq : ∀ u ∈ blockU X, u * u = 1
  not_le_zpowers : ∀ e ∈ blockU X, ¬ blockU X ≤ Subgroup.zpowers e

theorem isPrimeBlockData_of {X : Subgroup G} (hX : IsShortGroup ↥X) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (↥X ⧸ pCore 2 ↥X) = p) {x : G} (hx : x ∈ X) (hxo : orderOf x = p) :
    IsPrimeBlockData X p x :=
  { prime := hp
    odd := prime_top_ne_two hX hcard
    mem := hx
    order := hxo
    decomp := decomp_of_prime_top hp hcard (prime_top_ne_two hX hcard) hx hxo
    oTwoIn_eq := le_antisymm (oTwoIn_le_blockU_of_prime hX hp hcard hx hxo) (blockU_le_oTwoIn X)
    surj := blockU_surj_of_prime hX hp hcard hx hxo
    blockZ_eq := blockZ_eq_bot_of_prime hX hp hcard hx hxo
    irr := blockU_irr_of_prime hX hp hcard hx hxo
    sq := blockU_sq_of_prime hX hp hcard hx hxo
    not_le_zpowers := blockU_not_le_zpowers_of_prime hX hp hcard hx hxo }

end CFSG.CGT.PushingUpLit

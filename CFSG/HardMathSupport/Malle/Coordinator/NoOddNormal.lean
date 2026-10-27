module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

open scoped commutatorElement

variable {G : Type*} [Group G]

def conjPowSubgroup (Z : Subgroup G) (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (y : G) (k : ℕ) :
    Subgroup G where
  carrier := {z | z ∈ Z ∧ y * z * y⁻¹ = z ^ k}
  mul_mem' {a b} ha hb := by
    refine ⟨Z.mul_mem ha.1 hb.1, ?_⟩
    have hc : Commute a b := hZ a ha.1 b hb.1
    calc y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      _ = (a * b) ^ k := by rw [ha.2, hb.2, hc.mul_pow]
  one_mem' := ⟨Z.one_mem, by simp⟩
  inv_mem' {a} ha := ⟨Z.inv_mem ha.1, by rw [inv_pow, ← ha.2]; group⟩

theorem conj_mul_eq_of_conj_eq_pow {Z : Subgroup G} {a b : G} {k : ℕ}
    (ha : ∀ z ∈ Z, a * z * a⁻¹ = z ^ k) (hb : ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) {z : G} (hz : z ∈ Z) :
    (a * b) * z * (a * b)⁻¹ = (b * a) * z * (b * a)⁻¹ := by
  calc (a * b) * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by group
    _ = (b * z * b⁻¹) ^ k := ha _ (hb z hz)
    _ = b * z ^ k * b⁻¹ := conj_pow
    _ = b * (a * z * a⁻¹) * b⁻¹ := by rw [ha z hz]
    _ = (b * a) * z * (b * a)⁻¹ := by group

theorem exists_conj_ne_pow {Z : Subgroup G} {a b : G} (hb : ∀ z ∈ Z, b * z * b⁻¹ ∈ Z)
    (hab : ∃ z ∈ Z, (a * b) * z * (a * b)⁻¹ ≠ (b * a) * z * (b * a)⁻¹) (k : ℕ) :
    ∃ z ∈ Z, a * z * a⁻¹ ≠ z ^ k := by
  obtain ⟨z, hz, hne⟩ := hab
  by_contra h
  exact hne (conj_mul_eq_of_conj_eq_pow
    (fun x hx => Classical.byContradiction fun h' => h ⟨x, hx, h'⟩) hb hz)

theorem card_eq_five_of_le [Finite G] {C Z : Subgroup G} (hCZ : C ≤ Z) (hZ : Nat.card Z = 25)
    {c : G} (hc : c ∈ C) (hc1 : c ≠ 1) {z : G} (hz : z ∈ Z) (hzC : z ∉ C) : Nat.card C = 5 := by
  have hdvd : Nat.card C ∣ 5 ^ 2 := by
    have := Subgroup.card_dvd_of_le hCZ
    rwa [hZ] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvd
  interval_cases k
  · rw [pow_zero, Subgroup.card_eq_one] at hk'
    rw [hk', Subgroup.mem_bot] at hc
    exact absurd hc hc1
  · simpa using hk'
  · have hCeq := Subgroup.eq_of_le_of_card_ge hCZ (by norm_num [hk', hZ])
    rw [hCeq] at hzC
    exact absurd hz hzC

theorem conj_eq_self_of_card_eq_five {C : Subgroup G} (hC : Nat.card C = 5) {w : G}
    (hw : w ^ 3 = 1) (hwC : ∀ c ∈ C, w * c * w⁻¹ ∈ C) {c : G} (hc : c ∈ C) :
    w * c * w⁻¹ = c := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have : IsCyclic C := isCyclic_of_prime_card hC
  have hwN : w ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hwC h, fun hh => ?_⟩
    have h' := hwC _ (hwC _ hh)
    have heq : w * (w * (w * h * w⁻¹) * w⁻¹) * w⁻¹ = (w * w * w) * h * (w * w * w)⁻¹ := by
      group
    rw [heq, ← pow_three', hw] at h'
    simpa using h'
  set σ := C.normalizerMonoidHom ⟨w, hwN⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨w, hwN⟩ : Subgroup.normalizer (C : Set G)) ^ 3 = 1 := Subtype.ext hw
    rw [hσ, ← map_pow, h1, map_one]
  have h4 : orderOf σ ∣ 4 := by
    have := orderOf_dvd_natCard σ
    rwa [IsCyclic.card_mulAut, hC, Nat.totient_prime Nat.prime_five] at this
  have hσ1 : σ = 1 := by
    rw [← orderOf_eq_one_iff]
    have h3 := orderOf_dvd_of_pow_eq_one hσ3
    have hg : Nat.gcd 3 4 = 1 := by norm_num
    exact Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd h3 h4)
  have h := congrArg Subtype.val (DFunLike.congr_fun hσ1 ⟨c, hc⟩)
  simpa [hσ] using h

theorem mem_or_inv_mul_mem_or_mul_mem {P W : Subgroup G} [(P.subgroupOf W).Normal]
    (h3 : P.relIndex W = 3) {w : G} (hwW : w ∈ W) (hwP : w ∉ P) (hw3 : w ^ 3 = 1) {x : G}
    (hxW : x ∈ W) : x ∈ P ∨ w⁻¹ * x ∈ P ∨ w * x ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (W ⧸ P.subgroupOf W) = 3 := h3
  have ha : ((⟨w, hwW⟩ : W) : W ⧸ P.subgroupOf W) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hwP
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_of_prime_card hcard ha (g' := ((⟨x, hxW⟩ : W) : W ⧸ P.subgroupOf W)))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hn
  have hpow : (w ^ n)⁻¹ * x ∈ P := by simpa using hn
  have hmod : w ^ n = w ^ (n % 3) := by
    conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hw3, one_pow, mul_one]
  rw [hmod] at hpow
  obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  · rw [h] at hpow
    exact Or.inl (by simpa using hpow)
  · rw [h] at hpow
    exact Or.inr (Or.inl (by simpa using hpow))
  · rw [h] at hpow
    have hw2 : (w ^ 2)⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hw3)
    rw [hw2] at hpow
    exact Or.inr (Or.inr hpow)

theorem conj_eq_self_of_sq_conj_eq_inv [Finite G] {Z : Subgroup G}
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ5 : ∀ z ∈ Z, z ^ 5 = 1)
    (hZcard : Nat.card Z = 25) {y w : G} (hyZ : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z)
    (hwZ : ∀ z ∈ Z, w * z * w⁻¹ ∈ Z) (hyy : ∀ z ∈ Z, (y * y) * z * (y * y)⁻¹ = z⁻¹)
    (hy2 : ∃ z ∈ Z, y * z * y⁻¹ ≠ z ^ 2) (hy3 : ∃ z ∈ Z, y * z * y⁻¹ ≠ z ^ 3) (hw3 : w ^ 3 = 1)
    (hwy : ∀ z ∈ Z, w * (y * z * y⁻¹) * w⁻¹ = y * (w * z * w⁻¹) * y⁻¹) {z : G} (hz : z ∈ Z) :
    w * z * w⁻¹ = z := by
  set E := conjPowSubgroup Z hZab y
  have hEZ : ∀ k, E k ≤ Z := fun k x hx => hx.1
  have hwE : ∀ k, ∀ c ∈ E k, w * c * w⁻¹ ∈ E k := by
    intro k c hc
    refine ⟨hwZ c hc.1, ?_⟩
    rw [← hwy c hc.1, hc.2, conj_pow]
  have hyy' : ∀ x ∈ Z, y * (y * x * y⁻¹) * y⁻¹ = x⁻¹ := fun x hx => by
    rw [← hyy x hx]; group
  have hinv2 : ∀ x ∈ Z, x⁻¹ = (x ^ 2) ^ 2 := fun x hx =>
    inv_eq_of_mul_eq_one_left (by
      have e : (x ^ 2) ^ 2 * x = x ^ 5 := by group
      rw [e, hZ5 x hx])
  have hinv3 : ∀ x ∈ Z, x⁻¹ = (x ^ 3) ^ 3 := fun x hx =>
    inv_eq_of_mul_eq_one_left (by
      have e : (x ^ 3) ^ 3 * x = (x ^ 5) ^ 2 := by group
      rw [e, hZ5 x hx, one_pow])
  have hmem2 : ∀ x ∈ Z, (y * x * y⁻¹) * x ^ 2 ∈ E 2 := by
    intro x hx
    have ht := hyZ x hx
    have hc : Commute (y * x * y⁻¹) x := hZab _ ht _ hx
    refine ⟨Z.mul_mem ht (Z.pow_mem hx 2), ?_⟩
    calc y * ((y * x * y⁻¹) * x ^ 2) * y⁻¹
        = (y * (y * x * y⁻¹) * y⁻¹) * (y * x * y⁻¹) ^ 2 := by rw [conj_pow]; group
      _ = (y * x * y⁻¹) ^ 2 * (x ^ 2) ^ 2 := by
          rw [hyy' x hx, hinv2 x hx]
          exact (((hc.pow_left 2).pow_right 2).pow_right 2).eq.symm
      _ = ((y * x * y⁻¹) * x ^ 2) ^ 2 := ((hc.pow_right 2).mul_pow 2).symm
  have hmem3 : ∀ x ∈ Z, (y * x * y⁻¹) * x ^ 3 ∈ E 3 := by
    intro x hx
    have ht := hyZ x hx
    have hc : Commute (y * x * y⁻¹) x := hZab _ ht _ hx
    refine ⟨Z.mul_mem ht (Z.pow_mem hx 3), ?_⟩
    calc y * ((y * x * y⁻¹) * x ^ 3) * y⁻¹
        = (y * (y * x * y⁻¹) * y⁻¹) * (y * x * y⁻¹) ^ 3 := by rw [conj_pow]; group
      _ = (y * x * y⁻¹) ^ 3 * (x ^ 3) ^ 3 := by
          rw [hyy' x hx, hinv3 x hx]
          exact (((hc.pow_left 3).pow_right 3).pow_right 3).eq.symm
      _ = ((y * x * y⁻¹) * x ^ 3) ^ 3 := ((hc.pow_right 3).mul_pow 3).symm
  have hdec : ∀ x ∈ Z, ((y * x * y⁻¹) * x ^ 3) * ((y * x * y⁻¹) * x ^ 2)⁻¹ = x := by
    intro x hx
    have hc : (y * x * y⁻¹) * x = x * (y * x * y⁻¹) := hZab _ (hyZ x hx) _ hx
    calc ((y * x * y⁻¹) * x ^ 3) * ((y * x * y⁻¹) * x ^ 2)⁻¹
        = ((y * x * y⁻¹) * x) * (y * x * y⁻¹)⁻¹ := by group
      _ = x := by rw [hc]; group
  have hne2 : ∀ x ∈ Z, y * x * y⁻¹ ≠ x ^ 3 → (y * x * y⁻¹) * x ^ 2 ≠ 1 := by
    intro x hx hne h
    apply hne
    calc y * x * y⁻¹ = ((y * x * y⁻¹) * x ^ 2) * (x ^ 5)⁻¹ * x ^ 3 := by group
      _ = x ^ 3 := by rw [h, hZ5 x hx]; group
  have hne3 : ∀ x ∈ Z, y * x * y⁻¹ ≠ x ^ 2 → (y * x * y⁻¹) * x ^ 3 ≠ 1 := by
    intro x hx hne h
    apply hne
    calc y * x * y⁻¹ = ((y * x * y⁻¹) * x ^ 3) * (x ^ 5)⁻¹ * x ^ 2 := by group
      _ = x ^ 2 := by rw [h, hZ5 x hx]; group
  obtain ⟨a, ha, ha2⟩ := hy2
  obtain ⟨b, hb, hb3⟩ := hy3
  have hcard2 : Nat.card (E 2) = 5 :=
    card_eq_five_of_le (hEZ 2) hZcard (hmem2 b hb) (hne2 b hb hb3) ha (fun h => ha2 h.2)
  have hcard3 : Nat.card (E 3) = 5 :=
    card_eq_five_of_le (hEZ 3) hZcard (hmem3 a ha) (hne3 a ha ha2) hb (fun h => hb3 h.2)
  have h2 := conj_eq_self_of_card_eq_five hcard2 hw3 (hwE 2) (hmem2 z hz)
  have h3 := conj_eq_self_of_card_eq_five hcard3 hw3 (hwE 3) (hmem3 z hz)
  calc w * z * w⁻¹ = w * (((y * z * y⁻¹) * z ^ 3) * ((y * z * y⁻¹) * z ^ 2)⁻¹) * w⁻¹ := by
        rw [hdec z hz]
    _ = (w * ((y * z * y⁻¹) * z ^ 3) * w⁻¹) * (w * ((y * z * y⁻¹) * z ^ 2) * w⁻¹)⁻¹ := by
        group
    _ = z := by rw [h3, h2, hdec z hz]

theorem eq_of_odd_normal [Finite G] {N P Z W : Subgroup G} (_hPN : P ≤ N)
    (hPnorm : N ≤ Subgroup.normalizer (P : Set G))
    (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP5 : IsPGroup 5 P)
    (hZP : Z ≤ P) (hZ5 : ∀ z ∈ Z, z ^ 5 = 1) (hZcard : Nat.card Z = 25)
    (hZN : N ≤ Subgroup.normalizer (Z : Set G))
    (hCZ : N ⊓ Subgroup.centralizer (Z : Set G) ≤ P)
    (hidx : P.relIndex N = 96)
    {i j : G} (hiN : i ∈ N) (hjN : j ∈ N)
    (hii : ∀ z ∈ Z, (i * i) * z * (i * i)⁻¹ = z⁻¹) (hjj : ∀ z ∈ Z, (j * j) * z * (j * j)⁻¹ = z⁻¹)
    (hij : ∀ z ∈ Z, ⁅i, j⁆ * z * ⁅i, j⁆⁻¹ = z⁻¹)
    (hPW : P ≤ W) (hWN : W ≤ N) (hWn : ∀ n ∈ N, ∀ w ∈ W, n * w * n⁻¹ ∈ W)
    (hWodd : Odd (Nat.card W)) : W = P := by
  have hdvd : P.relIndex W ∣ 3 * 2 ^ 5 := by
    refine ⟨W.relIndex N, ?_⟩
    rw [Subgroup.relIndex_mul_relIndex P W N hPW hWN, hidx]
    norm_num
  have hodd : Odd (P.relIndex W) := hWodd.of_dvd_nat (Subgroup.relIndex_dvd_card P W)
  have h3 : P.relIndex W ∣ 3 :=
    (Nat.Coprime.pow_right 5 (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hPW
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨w, hwW⟩, hw'⟩ := exists_prime_orderOf_dvd_card' (G := W) 3
    (h3 ▸ Subgroup.relIndex_dvd_card P W)
  have hwN : w ∈ N := hWN hwW
  have hwo : orderOf w = 3 := by rw [← Subgroup.orderOf_mk w hwW, hw']
  have hw3 : w ^ 3 = 1 := hwo ▸ pow_orderOf_eq_one w
  have hwP : w ∉ P := by
    intro hwP
    obtain ⟨k, hk⟩ := hP5 ⟨w, hwP⟩
    have h1 := orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_mk, hwo] at h1
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1) (by norm_num)
  have hPconj : ∀ n ∈ N, ∀ p ∈ P, n * p * n⁻¹ ∈ P := fun n hn p hp =>
    (Subgroup.mem_normalizer_iff.mp (hPnorm hn) p).mp hp
  have hZconj : ∀ n ∈ N, ∀ z ∈ Z, n * z * n⁻¹ ∈ Z := fun n hn z hz =>
    (Subgroup.mem_normalizer_iff.mp (hZN hn) z).mp hz
  have hZconj' : ∀ n ∈ N, ∀ z ∈ Z, n⁻¹ * z * n ∈ Z := fun n hn z hz =>
    (Subgroup.mem_normalizer_iff''.mp (hZN hn) z).mp hz
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hab a (hZP ha) b (hZP hb)
  have : (P.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPW).mpr (hWN.trans hPnorm)
  have htri : ∀ n ∈ N, w⁻¹ * (n * w * n⁻¹) ∈ P ∨ w * (n * w * n⁻¹) ∈ P := by
    intro n hn
    rcases mem_or_inv_mul_mem_or_mul_mem h3 hwW hwP hw3 (hWn n hn w hwW) with h | h | h
    · refine absurd ?_ hwP
      have e : n⁻¹ * (n * w * n⁻¹) * n⁻¹⁻¹ = w := by group
      rw [← e]
      exact hPconj _ (N.inv_mem hn) _ h
    · exact Or.inl h
    · exact Or.inr h
  have hcomm : ∀ y : G, w⁻¹ * (y * w * y⁻¹) ∈ P → ∀ z ∈ Z, y * z * y⁻¹ ∈ Z →
      w * (y * z * y⁻¹) * w⁻¹ = y * (w * z * w⁻¹) * y⁻¹ := by
    intro y hy z hz hyz
    have hc : (w⁻¹ * (y * w * y⁻¹)) * (y * z * y⁻¹) = (y * z * y⁻¹) * (w⁻¹ * (y * w * y⁻¹)) :=
      hab _ hy _ (hZP hyz)
    calc w * (y * z * y⁻¹) * w⁻¹
        = w * ((w⁻¹ * (y * w * y⁻¹)) * (y * z * y⁻¹) * (w⁻¹ * (y * w * y⁻¹))⁻¹) * w⁻¹ := by
          rw [hc]; group
      _ = y * (w * z * w⁻¹) * y⁻¹ := by group
  have hfinal : ∀ y ∈ N, ∀ b ∈ N, w⁻¹ * (y * w * y⁻¹) ∈ P →
      (∀ z ∈ Z, (y * y) * z * (y * y)⁻¹ = z⁻¹) →
      (∃ z ∈ Z, (y * b) * z * (y * b)⁻¹ ≠ (b * y) * z * (b * y)⁻¹) → False := by
    intro y hyN b hbN hy hyy hyb
    apply hwP
    refine hCZ (Subgroup.mem_inf.mpr ⟨hwN, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩)
    have hwz := conj_eq_self_of_sq_conj_eq_inv hZab hZ5 hZcard (hZconj y hyN) (hZconj w hwN) hyy
      (exists_conj_ne_pow (hZconj b hbN) hyb 2) (exists_conj_ne_pow (hZconj b hbN) hyb 3) hw3
      (fun x hx => hcomm y hy x hx (hZconj y hyN x hx)) hz
    calc z * w = (w * z * w⁻¹) * w := by rw [hwz]
      _ = w * z := by group
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    rcases Z.bot_or_exists_ne_one with h | h
    · rw [h, Subgroup.card_bot] at hZcard
      norm_num at hZcard
    · exact h
  have hZinv : ∀ u ∈ Z, u ≠ 1 → u⁻¹ ≠ u := by
    intro u hu hu1 h
    apply hu1
    have hsq : u * u = 1 := by
      calc u * u = u * u⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel u
    calc u = u ^ 5 * ((u * u)⁻¹ * (u * u)⁻¹) := by group
      _ = 1 := by rw [hsq, hZ5 u hu]; group
  have hW1 : ∃ z ∈ Z, (i * j) * z * (i * j)⁻¹ ≠ (j * i) * z * (j * i)⁻¹ := by
    refine ⟨(j * i)⁻¹ * z₀ * (j * i), hZconj' _ (N.mul_mem hjN hiN) z₀ hz₀, ?_⟩
    have e1 : (i * j) * ((j * i)⁻¹ * z₀ * (j * i)) * (i * j)⁻¹ = ⁅i, j⁆ * z₀ * ⁅i, j⁆⁻¹ := by
      rw [commutatorElement_def]; group
    have e2 : (j * i) * ((j * i)⁻¹ * z₀ * (j * i)) * (j * i)⁻¹ = z₀ := by group
    rw [e1, e2, hij z₀ hz₀]
    exact hZinv z₀ hz₀ hz₀1
  have hW3 : ∃ z ∈ Z,
      ((i * j) * i) * z * ((i * j) * i)⁻¹ ≠ (i * (i * j)) * z * (i * (i * j))⁻¹ := by
    have hu : j * z₀ * j⁻¹ ∈ Z := hZconj j hjN z₀ hz₀
    have hu1 : j * z₀ * j⁻¹ ≠ 1 := by
      intro h
      apply hz₀1
      calc z₀ = j⁻¹ * (j * z₀ * j⁻¹) * j := by group
        _ = 1 := by rw [h]; group
    refine ⟨z₀, hz₀, ?_⟩
    have e1 : ((i * j) * i) * z₀ * ((i * j) * i)⁻¹ =
        ⁅i, j⁆ * (j * ((i * i) * z₀ * (i * i)⁻¹) * j⁻¹) * ⁅i, j⁆⁻¹ := by
      rw [commutatorElement_def]; group
    have e2 : (i * (i * j)) * z₀ * (i * (i * j))⁻¹ = (i * i) * (j * z₀ * j⁻¹) * (i * i)⁻¹ := by
      group
    have e3 : j * z₀⁻¹ * j⁻¹ = (j * z₀ * j⁻¹)⁻¹ := by group
    rw [e1, e2, hii z₀ hz₀, e3, hij _ (Z.inv_mem hu), inv_inv, hii _ hu]
    exact (hZinv _ hu hu1).symm
  have hijij : ∀ z ∈ Z, ((i * j) * (i * j)) * z * ((i * j) * (i * j))⁻¹ = z⁻¹ := by
    intro z hz
    have hu : j * z * j⁻¹ ∈ Z := hZconj j hjN z hz
    have e1 : ((i * j) * (i * j)) * z * ((i * j) * (i * j))⁻¹ =
        ⁅i, j⁆ * (j * ((i * i) * (j * z * j⁻¹) * (i * i)⁻¹) * j⁻¹) * ⁅i, j⁆⁻¹ := by
      rw [commutatorElement_def]; group
    have e2 : ∀ u : G, j * u⁻¹ * j⁻¹ = (j * u * j⁻¹)⁻¹ := fun u => by group
    have hjj' : j * (j * z * j⁻¹) * j⁻¹ = z⁻¹ := by rw [← hjj z hz]; group
    rw [e1, hii _ hu, e2, hjj', inv_inv, hij z hz]
  rcases htri i hiN with hi | hi
  · exact hfinal i hiN j hjN hi hii hW1
  rcases htri j hjN with hj | hj
  · obtain ⟨z, hz, hne⟩ := hW1
    exact hfinal j hjN i hiN hj hjj ⟨z, hz, hne.symm⟩
  refine hfinal (i * j) (N.mul_mem hiN hjN) i hiN ?_ hijij hW3
  have e : w⁻¹ * ((i * j) * w * (i * j)⁻¹) =
      (w⁻¹ * (w * (i * w * i⁻¹))⁻¹ * w⁻¹⁻¹) * (i * (w * (j * w * j⁻¹)) * i⁻¹) := by group
  rw [e]
  exact P.mul_mem (hPconj _ (N.inv_mem hwN) _ (P.inv_mem hi)) (hPconj _ hiN _ hj)

end CFSG.HardMathSupport.Malle.Coordinator

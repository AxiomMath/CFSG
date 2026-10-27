module

public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.GroupTheory.PCore.CharacteristicPPrimeCore

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] {L : Subgroup G}

theorem central_displacement_trivial {Λ : Type} [Group Λ] (x' e z : Λ) (n : ℕ)
    (hn : ¬ 2 ∣ n) (hzc : ∀ g : Λ, g * z = z * g) (hz : e * x' * e⁻¹ = x' * z)
    (hx2 : ∀ y : Λ, y * (x' * x') = (x' * x') * y) (hen : ∀ g : Λ, g * e ^ n = e ^ n * g) :
    z = 1 := by
  have hz2 : z * z = 1 := by
    have h1 : (e * x' * e⁻¹) * (e * x' * e⁻¹) = (x' * x') := by
      have := hx2 e
      calc (e * x' * e⁻¹) * (e * x' * e⁻¹) = e * (x' * x') * e⁻¹ := by group
        _ = (x' * x') * e * e⁻¹ := by rw [← mul_assoc, ← this]; group
        _ = x' * x' := by group
    rw [hz] at h1
    have h2 : (x' * z) * (x' * z) = (x' * x') * (z * z) := by
      calc (x' * z) * (x' * z) = x' * (z * x') * z := by group
        _ = x' * (x' * z) * z := by rw [← hzc x']
        _ = (x' * x') * (z * z) := by group
    rw [h2] at h1
    have h3 : (x' * x') * (z * z) = (x' * x') * 1 := by rw [mul_one]; exact h1
    exact mul_left_cancel h3
  have hk : ∀ k : ℕ, e ^ k * x' * (e ^ k)⁻¹ = x' * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzk : ∀ g : Λ, g * z ^ k = z ^ k * g := fun g =>
        (Commute.pow_right (show Commute g z from hzc g) k).eq
      calc e ^ (k + 1) * x' * (e ^ (k + 1))⁻¹
          = e * (e ^ k * x' * (e ^ k)⁻¹) * e⁻¹ := by rw [pow_succ']; group
        _ = e * (x' * z ^ k) * e⁻¹ := by rw [ih]
        _ = (e * x' * e⁻¹) * (e * z ^ k * e⁻¹) := by group
        _ = (x' * z) * z ^ k := by rw [hz, hzk e]; group
        _ = x' * z ^ (k + 1) := by rw [pow_succ']; group
  have hzn : z ^ n = 1 := by
    have h1 := hk n
    have h2 : e ^ n * x' * (e ^ n)⁻¹ = x' := by
      rw [← hen x']; group
    rw [h2] at h1
    have h3 : x' * 1 = x' * z ^ n := by rw [mul_one]; exact h1
    exact (mul_left_cancel h3).symm
  obtain ⟨m, hm⟩ : Odd n := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hn)
  have : z ^ n = z := by
    rw [hm, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
  rw [← this]; exact hzn

theorem sq_central {w x : G} (hw2 : w * w = 1) (hxL : x ∈ L)
    (hx : ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x) :
    ∀ y : L, y * ((⟨x, hxL⟩ : L) * ⟨x, hxL⟩) = ((⟨x, hxL⟩ : L) * ⟨x, hxL⟩) * y := by
  intro y
  have hy1 : x⁻¹ * (y : G) * x ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hxL) y.2) hxL
  have h1 := hx (x⁻¹ * (y : G) * x) hy1
  have h2 := hx y y.2
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hw : w⁻¹ * (w⁻¹ * (y : G) * w) * w = y := by
    rw [hwinv]
    calc w * (w * (y : G) * w) * w = (w * w) * y * (w * w) := by group
      _ = y := by rw [hw2]; group
  have hy : (y : G) = x⁻¹ * (x⁻¹ * (y : G) * x) * x := by
    calc (y : G) = w⁻¹ * (w⁻¹ * (y : G) * w) * w := hw.symm
      _ = w⁻¹ * (x⁻¹ * (y : G) * x) * w := by rw [h2]
      _ = x⁻¹ * (x⁻¹ * (y : G) * x) * x := h1
  apply Subtype.ext
  show (y : G) * (x * x) = (x * x) * y
  calc (y : G) * (x * x) = (x * x) * (x⁻¹ * (x⁻¹ * (y : G) * x) * x) := by group
    _ = (x * x) * y := by rw [← hy]

theorem exists_odd_normal_of_torus [Finite G] {w x : G} (hw2 : w * w = 1) (hxL : x ∈ L)
    (hx : ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x)
    (T : Subgroup (L ⧸ Subgroup.center L))
    (hTt : ∀ y ∈ T, y * (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) =
        (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) * y)
    (hTn : ∀ c : L ⧸ Subgroup.center L,
        c * (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) =
          (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) * c →
        ∀ y ∈ T, c * y * c⁻¹ ∈ T)
    (hTcyc : IsCyclic T) (hTodd : ¬ 2 ∣ Nat.card T) (hT1 : T ≠ ⊥) :
    ∃ N₀ : Subgroup G, N₀ ≤ L ⊓ Subgroup.centralizer ({w} : Set G) ∧
      (∀ k ∈ L ⊓ Subgroup.centralizer ({w} : Set G), ∀ n ∈ N₀, k * n * k⁻¹ ∈ N₀) ∧
      ¬ 2 ∣ Nat.card N₀ ∧ N₀ ≠ ⊥ := by
  classical
  set Z := Subgroup.center L with hZ
  let π : L →* L ⧸ Z := QuotientGroup.mk' Z
  set x' : L := ⟨x, hxL⟩ with hx'
  let E : Subgroup L := T.comap π
  have hπmem : ∀ e : L, e ∈ E ↔ π e ∈ T := fun e => Iff.rfl
  have hx2 := sq_central hw2 hxL hx
  have hEx : ∀ e ∈ E, e * x' = x' * e := by
    intro e he
    have hzmem : x'⁻¹ * e * x' * e⁻¹ ∈ Z := by
      rw [← QuotientGroup.eq_one_iff (N := Z)]
      have h := hTt (π e) he
      show π (x'⁻¹ * e * x' * e⁻¹) = 1
      simp only [map_mul, map_inv]
      calc (π x')⁻¹ * π e * π x' * (π e)⁻¹ = (π x')⁻¹ * (π e * π x') * (π e)⁻¹ := by group
        _ = (π x')⁻¹ * (π x' * π e) * (π e)⁻¹ := by rw [show π e * π x' = π x' * π e from h]
        _ = 1 := by group
    have hzc : ∀ g : L, g * (x'⁻¹ * e * x' * e⁻¹) = (x'⁻¹ * e * x' * e⁻¹) * g :=
      fun g => Subgroup.mem_center_iff.mp hzmem g
    have hen : ∀ g : L, g * e ^ Nat.card T = e ^ Nat.card T * g := by
      have hpow : π (e ^ Nat.card T) = 1 := by
        rw [map_pow]
        have : (⟨π e, he⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
        exact congrArg Subtype.val this
      have hmem : e ^ Nat.card T ∈ Z := (QuotientGroup.eq_one_iff _).mp hpow
      exact fun g => Subgroup.mem_center_iff.mp hmem g
    have hz1 := central_displacement_trivial x' e (x'⁻¹ * e * x' * e⁻¹) (Nat.card T) hTodd hzc
      (by group) hx2 hen
    calc e * x' = x' * (x'⁻¹ * e * x' * e⁻¹) * e := by group
      _ = x' * 1 * e := by rw [hz1]
      _ = x' * e := by group
  have : IsCyclic T := hTcyc
  have hEab : IsMulCommutative E := by
    let f : E →* T := (π.comp E.subtype).codRestrict T (fun e => e.2)
    refine f.isMulCommutative_of_isCyclic_of_ker_le_center ?_
    intro e he
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : π e.1 = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp he)
      exact this
    have hmem : (e.1 : L) ∈ Z := (QuotientGroup.eq_one_iff _).mp h1
    exact Subtype.ext (Subgroup.mem_center_iff.mp hmem g.1)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let N₀L : Subgroup L :=
    { carrier := {e | e ∈ E ∧ Odd (orderOf e)}
      mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, Odd.of_dvd_nat (ha.2.mul hb.2)
        (Commute.orderOf_mul_dvd_mul_orderOf (hEcomm a ha.1 b hb.1))⟩
      one_mem' := ⟨E.one_mem, by simp⟩
      inv_mem' := fun {a} ha => ⟨E.inv_mem ha.1, by rw [orderOf_inv]; exact ha.2⟩ }
  refine ⟨N₀L.map L.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    refine ⟨e.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : (e : G) * x = x * e := congrArg Subtype.val (hEx e he.1)
    have h2 := hx e e.2
    have h3 : x⁻¹ * (e : G) * x = e := by
      calc x⁻¹ * (e : G) * x = x⁻¹ * (x * e) := by rw [mul_assoc, h1, ← mul_assoc]
        _ = e := by group
    rw [h3] at h2
    show (e : G) * w = w * e
    calc (e : G) * w = w * (w⁻¹ * e * w) := by group
      _ = w * e := by rw [h2]
  · rintro k ⟨hkL, hkw⟩ _ ⟨e, he, rfl⟩
    let k' : L := ⟨k, hkL⟩
    have hkw' : k * w = w * k := Subgroup.mem_centralizer_singleton_iff.mp hkw
    have hkx : k * x = x * k := by
      have h2 := hx k hkL
      have h3 : w⁻¹ * k * w = k := by
        calc w⁻¹ * k * w = w⁻¹ * (k * w) := by group
          _ = w⁻¹ * (w * k) := by rw [hkw']
          _ = k := by group
      rw [h3] at h2
      calc k * x = x * (x⁻¹ * k * x) := by group
        _ = x * k := by rw [← h2]
    have hk'x : k' * x' = x' * k' := Subtype.ext hkx
    refine ⟨k' * e * k'⁻¹, ⟨?_, ?_⟩, by simp [k']⟩
    · rw [hπmem, map_mul, map_mul, map_inv]
      refine hTn (π k') ?_ (π e) he.1
      show π k' * π x' = π x' * π k'
      rw [← map_mul, ← map_mul, hk'x]
    · have := orderOf_injective (MulAut.conj k').toMonoidHom (MulAut.conj k').injective e
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this]
      exact he.2
  · intro h2
    have hcard : Nat.card (N₀L.map L.subtype) = Nat.card N₀L :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [hcard] at h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have := g.2.2
    rw [Subgroup.orderOf_coe, hg] at this
    exact absurd this (by decide)
  · obtain ⟨t₁, ht₁T, ht₁⟩ : ∃ t₁ ∈ T, t₁ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hT1 ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective t₁
    have heE : e ∈ E := ht₁T
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos e).ne'
    have he'E : e ^ (2 ^ k) ∈ E := E.pow_mem heE _
    have he'odd : Odd (orderOf (e ^ (2 ^ k))) := by
      have : (e ^ (2 ^ k)) ^ m = 1 := by rw [← pow_mul, ← hkm]; exact pow_orderOf_eq_one e
      exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one this)
    have he'ne : e ^ (2 ^ k) ≠ 1 := by
      intro h
      have h1 : (π e) ^ (2 ^ k) = 1 := by
        rw [← map_pow, h, map_one]
      have h2 : orderOf (π e) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
      have h3 : orderOf (π e) ∣ Nat.card T := by
        have := orderOf_dvd_natCard (⟨π e, ht₁T⟩ : T)
        rw [← Subgroup.orderOf_coe] at this
        exact this
      rcases (Nat.dvd_prime_pow Nat.prime_two).mp h2 with ⟨i, -, hi⟩
      rcases i with _ | i
      · simp only [pow_zero] at hi
        exact ht₁ (orderOf_eq_one_iff.mp hi)
      · apply hTodd
        have : 2 ∣ orderOf (π e) := by rw [hi]; exact dvd_pow_self 2 (by omega)
        exact this.trans h3
    intro hbot
    have : ((e ^ (2 ^ k) : L) : G) ∈ N₀L.map L.subtype := ⟨e ^ (2 ^ k), ⟨he'E, he'odd⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact he'ne (Subtype.ext this)

theorem eq_bot_of_charTwo_odd_normal [Finite G] {K N : Subgroup G} (hK : CharTwo K) (hNK : N ≤ K)
    (hN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hodd : ¬ 2 ∣ Nat.card N) : N = ⊥ := by
  have hchar := EscapingLocal.isCharacteristicP_of_charTwo hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.characteristic_p_normal_prime_complement_trivial hchar).1
  have hN'n : (N.subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN (k : G) k.2 (n : G) hn
  have hcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hbot := h (N.subgroupOf K) hN'n (by rw [hcard]; exact hodd)
  rw [eq_bot_iff]
  intro n hn
  have : (⟨n, hNK hn⟩ : K) ∈ N.subgroupOf K := hn
  rw [hbot, Subgroup.mem_bot] at this
  have h1 : n = 1 := congrArg Subtype.val this
  rw [h1]; exact Subgroup.one_mem _

theorem not_charTwo_of_torus [Finite G] {w x : G} (hw2 : w * w = 1) (hxL : x ∈ L)
    (hx : ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x)
    (T : Subgroup (L ⧸ Subgroup.center L))
    (hTt : ∀ y ∈ T, y * (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) =
        (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) * y)
    (hTn : ∀ c : L ⧸ Subgroup.center L,
        c * (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) =
          (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) * c →
        ∀ y ∈ T, c * y * c⁻¹ ∈ T)
    (hTcyc : IsCyclic T) (hTodd : ¬ 2 ∣ Nat.card T) (hT1 : T ≠ ⊥) :
    ¬ CharTwo (L ⊓ Subgroup.centralizer ({w} : Set G)) := by
  intro hK
  obtain ⟨N₀, hle, hn, hodd, hne⟩ :=
    exists_odd_normal_of_torus hw2 hxL hx T hTt hTn hTcyc hTodd hT1
  exact hne (eq_bot_of_charTwo_odd_normal hK hle hn hodd)

end CFSG.QuasithinUnique.K1

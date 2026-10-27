module

public import CFSG.GH74.Uniqueness.SU.SU13TB3W
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.GH74.Uniqueness.SU.KInputs2
public import CFSG.GH74.Uniqueness.SU.SU13TB1Main

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] {z : G}

theorem conj_inv_of_mem_zpowers {s u x : G} (hu : u * s * u⁻¹ = s⁻¹) (hx : x ∈ zpowers s) :
    u * x * u⁻¹ = x⁻¹ := by
  obtain ⟨k, rfl⟩ := hx
  beta_reduce
  rw [← conj_zpow, hu, inv_zpow]

variable [Finite G]

omit [Finite G] in
theorem zpowers_le_oc (e : Elts G z) : zpowers e.s₁ ≤ oc (centralizer ({e.s₁} : Set G)) := by
  refine le_oc_of_normal_odd ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr rfl)) ?_ ?_
  · intro g hg n hn
    have := zpowers_comm_of_mem_centralizer hg hn
    rw [← this]; simpa using hn
  · rw [Nat.card_zpowers, e.s₁_ord]; decide

theorem t_mem_normalizer_oc (e : Elts G z) :
    e.t ∈ normalizer ((oc (centralizer ({e.s₁} : Set G)) : Subgroup G) : Set G) :=
  mem_normalizer_oc (mem_normalizer_centralizer_of_conj_inv e.t_s₁)

theorem card_W (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) :
    Nat.card (oc (centralizer ({e.s₁} : Set G))) =
      3 * Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t} : Set G) : Subgroup G) *
        Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t * z} : Set G) : Subgroup G) := by
  set X := centralizer ({e.s₁} : Set G) with hX
  set W := oc X with hW
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have ht_sq : e.t * e.t = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two e.t_ord
  have hz_sq : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have hcomm : Commute e.t z := e.t_comm
  let T : Subgroup G := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions e.t z ht_sq hz_sq hcomm
  have hTk : IsKleinFour T :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions e.t z ht_sq hz_sq ht1 hz1
      e.t_ne hcomm
  have hTmem : ∀ x ∈ T, x = e.t * z ∨ x = e.t ∨ x = z ∨ x = 1 := by
    intro x hx
    have : x ∈ ({e.t * z, e.t, z, 1} : Set G) := hx
    simpa using this
  have htT : e.t ∈ T := by
    show e.t ∈ ({e.t * z, e.t, z, 1} : Set G)
    simp
  have hzT : z ∈ T := by
    show z ∈ ({e.t * z, e.t, z, 1} : Set G)
    simp
  have hzN : z ∈ normalizer (W : Set G) := le_normalizer_oc X (z_mem_centralizer e f)
  have htN : e.t ∈ normalizer (W : Set G) := t_mem_normalizer_oc e
  have hTn : T ≤ normalizer (W : Set G) := by
    intro x hx
    rcases hTmem x hx with rfl | rfl | rfl | rfl
    · exact mul_mem htN hzN
    · exact htN
    · exact hzN
    · exact one_mem _
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (T := T) (K := W)
    (odd_card_oc X) hTn (a := e.t) (b := z) htT hzT ht1 hz1 e.t_ne
  have hPle : zpowers e.s₁ ≤ W := zpowers_le_oc e
  have hWz : W ⊓ centralizer ({z} : Set G) = zpowers e.s₁ := by
    refine le_antisymm (W_inf_centralizer_le e f) (le_inf hPle ?_)
    refine (zpowers_le).mpr ?_
    exact mem_centralizer_singleton_iff.mpr e.s₁_comm
  have hWzcard : Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) = 3 := by
    rw [hWz, Nat.card_zpowers, e.s₁_ord]
  have hWT : W ⊓ centralizer (T : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxT⟩ := mem_inf.mp hx
    have hxz : x * z = z * x := (mem_centralizer_iff.mp hxT z hzT).symm
    have hxt : e.t * x = x * e.t := mem_centralizer_iff.mp hxT e.t htT
    have hxP : x ∈ zpowers e.s₁ := by
      rw [← hWz]
      exact mem_inf.mpr ⟨hxW, mem_centralizer_singleton_iff.mpr hxz⟩
    have hinv := conj_inv_of_mem_zpowers e.t_s₁ hxP
    have hx2 : x * x = 1 := by
      have h1 : e.t * x * e.t⁻¹ = x := by rw [hxt]; group
      have h2 : x = x⁻¹ := h1.symm.trans hinv
      calc x * x = x * x⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel x
    exact mem_bot.mpr (eq_one_of_mem_oc_of_sq (hPle hxP) hx2)
  have hWTcard : Nat.card (W ⊓ centralizer (T : Set G) : Subgroup G) = 1 := by
    rw [hWT]; exact Subgroup.card_bot
  rw [hWzcard, hWTcard] at hBW
  simp only [one_pow, mul_one] at hBW
  rw [hBW]
  ring

theorem inverted_by_z (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) {u : G}
    (hus : u * e.s₁ * u⁻¹ = e.s₁⁻¹) (huz : u * z = z * u) {x : G}
    (hx : x ∈ oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({u} : Set G)) :
    z * x * z⁻¹ = x⁻¹ := by
  obtain ⟨hxW, hxu⟩ := mem_inf.mp hx
  have hxu' : x * u = u * x := mem_centralizer_singleton_iff.mp hxu
  obtain ⟨c, hc, h1⟩ := z_inv_mod hz e f hxW
  have hp : c * c ∈ zpowers e.s₁ := mul_mem hc hc
  have hpc : c * c = (z * x * z⁻¹) * x := by rw [h1]; group
  have hzu : Commute z u := huz.symm
  have hzxu : (z * x * z⁻¹) * u = u * (z * x * z⁻¹) := by
    calc z * x * z⁻¹ * u = z * x * (z⁻¹ * u) := by group
      _ = z * x * (u * z⁻¹) := by rw [(Commute.inv_left hzu).eq]
      _ = z * (x * u) * z⁻¹ := by group
      _ = z * (u * x) * z⁻¹ := by rw [hxu']
      _ = (z * u) * x * z⁻¹ := by group
      _ = (u * z) * x * z⁻¹ := by rw [hzu.eq]
      _ = u * (z * x * z⁻¹) := by group
  have hpu : u * (c * c) = (c * c) * u := by
    rw [hpc]
    calc u * (z * x * z⁻¹ * x) = (u * (z * x * z⁻¹)) * x := by group
      _ = (z * x * z⁻¹ * u) * x := by rw [hzxu]
      _ = z * x * z⁻¹ * (u * x) := by group
      _ = z * x * z⁻¹ * (x * u) := by rw [hxu']
      _ = (z * x * z⁻¹ * x) * u := by group
  have hinv := conj_inv_of_mem_zpowers hus hp
  have hp1 : (c * c) * (c * c) = 1 := by
    have h2 : u * (c * c) * u⁻¹ = c * c := by rw [hpu]; group
    have h3 : c * c = (c * c)⁻¹ := h2.symm.trans hinv
    calc c * c * (c * c) = c * c * (c * c)⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel _
  have hpW : c * c ∈ oc (centralizer ({e.s₁} : Set G)) := zpowers_le_oc e hp
  have := eq_one_of_mem_oc_of_sq hpW hp1
  rw [h1, this, one_mul]

omit [Finite G] in
theorem dvd_1575 {a : ℕ} (hodd : Odd a)
    (h : ∀ p k : ℕ, p.Prime → p ≠ 2 → p ^ k ∣ a → p ^ k ∣ 5 ^ 2 ∨ p ^ k ∣ 7 ∨ p ^ k ∣ 9) :
    a ∣ 1575 := by
  refine (Nat.dvd_iff_prime_pow_dvd_dvd 1575 a).mpr fun p k hp hpk => ?_
  by_cases hp2 : p = 2
  · subst hp2
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]; simp
    · exfalso
      have h2 : 2 ∣ a := (dvd_pow_self 2 hk.ne').trans hpk
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · rcases h p k hp hp2 hpk with h25 | h7 | h9
    · exact h25.trans (by norm_num)
    · exact h7.trans (by norm_num)
    · exact h9.trans (by norm_num)

theorem sylow_bound (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) {u : G} (hus : u * e.s₁ * u⁻¹ = e.s₁⁻¹)
    (huz : u * z = z * u) (hk : ∃ k : G, k * z * k⁻¹ = u) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ^ k ∣ Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({u} : Set G) : Subgroup G)) :
    p ^ k ∣ 5 ^ 2 ∨ p ^ k ∣ 7 ∨ p ^ k ∣ 9 := by
  obtain ⟨kk, hkk⟩ := hk
  have hTwo : K.IsTwoAlt ↥(centralizer ({u} : Set G)) 10 := by
    have := isTwoAlt_centralizer_conj (k := kk) hH
    rw [hkk] at this
    exact this
  set A : Subgroup G := oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({u} : Set G) with hA
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Kp, hKp⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) p hdvd
  have hKA : Kp.map A.subtype ≤ centralizer ({u} : Set G) := by
    rintro _ ⟨y, -, rfl⟩
    exact (mem_inf.mp y.2).2
  set Y' : Subgroup ↥(centralizer ({u} : Set G)) := (Kp.map A.subtype).subgroupOf (centralizer ({u} : Set G))
    with hY'
  have hYcard : Nat.card Y' = p ^ k := by
    rw [hY', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv,
      Subgroup.card_map_of_injective A.subtype_injective, hKp]
  have hYp : IsPGroup p Y' := IsPGroup.of_card hYcard
  have hzu : z ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr huz.symm
  let a : ↥(centralizer ({u} : Set G)) := ⟨z, hzu⟩
  have ha2 : orderOf a = 2 := by rw [← hz]; exact Subgroup.orderOf_mk z hzu
  have hinv : ∀ y ∈ Y', a * y * a⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨y0, hy0, hy0e⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
    apply Subtype.ext
    have hyA : (y : G) ∈ A := by rw [← hy0e]; exact y0.2
    show z * (y : G) * z⁻¹ = (y : G)⁻¹
    exact inverted_by_z hz e f hus huz hyA
  have := hKI7d 10 (Or.inr rfl) ↥(centralizer ({u} : Set G)) hTwo a ha2 p hp hp2 Y' hYp hinv
  rw [hYcard] at this
  simpa using this

omit [Finite G] in
theorem tz_facts (hz : orderOf z = 2) (e : Elts G z) :
    (e.t * z) * e.s₁ * (e.t * z)⁻¹ = e.s₁⁻¹ ∧ (e.t * z) * z = z * (e.t * z) := by
  have hz_sq : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  refine ⟨?_, ?_⟩
  · calc (e.t * z) * e.s₁ * (e.t * z)⁻¹ = e.t * (z * e.s₁ * z⁻¹) * e.t⁻¹ := by group
      _ = e.t * e.s₁ * e.t⁻¹ := by rw [show z * e.s₁ * z⁻¹ = e.s₁ by rw [← e.s₁_comm]; group]
      _ = e.s₁⁻¹ := e.t_s₁
  · calc e.t * z * z = e.t * (z * z) := by group
      _ = e.t := by rw [hz_sq, mul_one]
      _ = z * (e.t * z) := by rw [← mul_assoc, ← e.t_comm, mul_assoc, hz_sq, mul_one]

theorem W_dvd (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) (l : Lem232 z e) :
    Nat.card (oc (centralizer ({e.s₁} : Set G))) ∣ 3 ^ 5 * 5 ^ 4 * 7 ^ 2 := by
  rw [card_W hz e f]
  have hodd : ∀ u : G, Odd (Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({u} : Set G) : Subgroup G)) :=
    fun u => Odd.of_dvd_nat (odd_card_oc _) (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨k₁, -, hk₁⟩ := l.k₁
  obtain ⟨k₂, -, hk₂⟩ := l.k₂
  have ha : Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t} : Set G) : Subgroup G) ∣ 1575 :=
    dvd_1575 (hodd _) fun p k hp hp2 hpk =>
      sylow_bound hKI7d hH hz e f e.t_s₁ e.t_comm ⟨k₁, hk₁⟩ hp hp2 hpk
  have hb : Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t * z} : Set G) : Subgroup G) ∣ 1575 :=
    dvd_1575 (hodd _) fun p k hp hp2 hpk =>
      sylow_bound hKI7d hH hz e f (tz_facts hz e).1 (tz_facts hz e).2 ⟨k₂, hk₂⟩ hp hp2 hpk
  calc 3 * Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t} : Set G) : Subgroup G) *
        Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t * z} : Set G) : Subgroup G)
      ∣ 3 * 1575 * 1575 := mul_dvd_mul (mul_dvd_mul dvd_rfl ha) hb
    _ = 3 ^ 5 * 5 ^ 4 * 7 ^ 2 := by norm_num

end CFSG.GH74.Uniqueness.SU.SU13

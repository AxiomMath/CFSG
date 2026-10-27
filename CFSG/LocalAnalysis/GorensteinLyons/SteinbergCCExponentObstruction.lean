module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup

variable {G : Type*} [Group G]

theorem conj_eq_of_mem_normalizer_of_commutator_eq {L : Subgroup G} {z : G}
    (hLz : ⁅L, L⁆ = zpowers z) (hz : orderOf z = 2) {g : G}
    (hg : g ∈ normalizer (L : Set G)) : g * z * g⁻¹ = z := by
  have hL : L.map (MulAut.conj g).toMonoidHom = L := by
    have h := mem_normalizer_iff_conjugate_eq.mp (inv_mem hg)
    unfold CFSG.conjugate at h
    rwa [inv_inv] at h
  have hmem : g * z * g⁻¹ ∈ zpowers z := by
    rw [← hLz, ← hL, ← map_commutator]
    exact ⟨z, by rw [hLz]; exact mem_zpowers z, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers hz hmem with h | h
  · exfalso
    have hz1 : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact h

theorem cyclic_involution_normalizer_exponent_obstruction [Finite G] {L : Subgroup G}
    (_hL2 : IsPGroup 2 L) (_hLnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {z : G}
    (hLz : ⁅L, L⁆ = zpowers z) (hz : orderOf z = 2) {e : ℕ} (_he : 1 ≤ e)
    (hexp : ∀ x ∈ L, x ^ (2 ^ e) = 1) {X : Subgroup G} (hXL : X ≤ normalizer (L : Set G))
    (_hX1 : X ≠ ⊥) [IsCyclic X] (hX2 : IsPGroup 2 X) {a : G} (haX : a ∈ X)
    (ha : orderOf a = 2) (haL : ⁅zpowers a, L⁆ = zpowers z)
    (hNX : normalizer (X : Set G) = centralizer {a}) :
    (∃ q₀ ∈ L, CFSG.conjugate X q₀ ≠ X ∧
      (∀ q ∈ L, CFSG.conjugate X q = X ∨ CFSG.conjugate X q = CFSG.conjugate X q₀) ∧
      (∀ x ∈ X, ∀ y ∈ CFSG.conjugate X q₀, x * y = y * x) ∧ X ⊓ CFSG.conjugate X q₀ = ⊥ ∧
      L ≤ normalizer ((X ⊔ CFSG.conjugate X q₀ : Subgroup G) : Set G) ∧
      Nonempty ((X ⊔ CFSG.conjugate X q₀ : Subgroup G) ≃* X × X)) ∧
    (∀ q ∈ L, q⁻¹ * a * q ≠ a → ∀ s : G, zpowers s = X →
      s⁻¹ * (q⁻¹ * s * q) ∈ L ∧ orderOf (s⁻¹ * (q⁻¹ * s * q)) = Nat.card X) ∧
    Nat.card X ≤ 2 ^ e ∧
    (∀ b ∈ L, (∃ y ∈ L, b * y ≠ y * b) → ⁅zpowers b, L⁆ = zpowers z) := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzinv : z⁻¹ = z := by
    have h := pow_orderOf_eq_one z
    rw [hz, pow_two] at h
    exact inv_eq_of_mul_eq_one_right h
  have hfixz : ∀ g ∈ normalizer (L : Set G), g * z = z * g := fun g hg => by
    have h := conj_eq_of_mem_normalizer_of_commutator_eq hLz hz hg
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h]
  have haC : a ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hXC : X ≤ centralizer ({a} : Set G) := hNX ▸ le_normalizer
  have hconj_a : ∀ q ∈ L, q⁻¹ * a * q = a ∨ q⁻¹ * a * q = a * z := by
    intro q hq
    have hmem : a * q⁻¹ * a⁻¹ * q ∈ zpowers z := by
      rw [← haL]
      have h := commutator_mem_commutator (mem_zpowers a) (inv_mem hq)
      rwa [commutatorElement_def, inv_inv] at h
    rcases eq_one_or_eq_of_mem_zpowers hz hmem with h | h
    · left
      calc q⁻¹ * a * q = (a⁻¹ * (a * q⁻¹ * a⁻¹ * q))⁻¹ := by group
        _ = a := by rw [h]; group
    · right
      have haz : a * z = z * a := hfixz a (hXL haX)
      calc q⁻¹ * a * q = (a⁻¹ * (a * q⁻¹ * a⁻¹ * q))⁻¹ := by group
        _ = (a⁻¹ * z)⁻¹ := by rw [h]
        _ = z⁻¹ * a := by group
        _ = a * z := by rw [hzinv, haz]
  obtain ⟨q₀, hq₀L, hq₀⟩ : ∃ q ∈ L, q⁻¹ * a * q ≠ a := by
    by_contra hcon
    apply hz1
    have hle : zpowers a ≤ centralizer (L : Set G) := by
      rw [zpowers_le, mem_centralizer_iff]
      intro q hq
      have h : q⁻¹ * a * q = a := by
        by_contra hne
        exact hcon ⟨q, hq, hne⟩
      calc q * a = q * (q⁻¹ * a * q) := by rw [h]
        _ = a * q := by group
    have hbot : ⁅zpowers a, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [haL] at hbot
    have hzmem : z ∈ (⊥ : Subgroup G) := hbot ▸ mem_zpowers z
    exact mem_bot.mp hzmem
  have hq₀az : q₀⁻¹ * a * q₀ = a * z := (hconj_a q₀ hq₀L).resolve_left hq₀
  have hXq_iff : ∀ q : G, CFSG.conjugate X q = X ↔ q⁻¹ * a * q = a := by
    intro q
    rw [← mem_normalizer_iff_conjugate_eq, hNX, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc q⁻¹ * a * q = q⁻¹ * (q * a) := by rw [h]; group
        _ = a := by group
    · intro h
      calc q * a = q * (q⁻¹ * a * q) := by rw [h]
        _ = a * q := by group
  set X₁ := CFSG.conjugate X q₀ with hX₁
  have hX₁ne : X₁ ≠ X := fun h => hq₀ ((hXq_iff q₀).mp h)
  have htwo : ∀ q ∈ L, CFSG.conjugate X q = X ∨ CFSG.conjugate X q = X₁ := by
    intro q hq
    rcases hconj_a q hq with h | h
    · exact Or.inl ((hXq_iff q).mpr h)
    · right
      have hc : (q * q₀⁻¹)⁻¹ * a * (q * q₀⁻¹) = a := by
        calc (q * q₀⁻¹)⁻¹ * a * (q * q₀⁻¹) = q₀ * (q⁻¹ * a * q) * q₀⁻¹ := by group
          _ = q₀ * (q₀⁻¹ * a * q₀) * q₀⁻¹ := by rw [h, hq₀az]
          _ = a := by group
      have h1 := (hXq_iff _).mpr hc
      calc CFSG.conjugate X q = CFSG.conjugate X ((q * q₀⁻¹) * q₀) := by
            rw [inv_mul_cancel_right]
        _ = CFSG.conjugate (CFSG.conjugate X (q * q₀⁻¹)) q₀ := (conjugate_conjugate _ _ _).symm
        _ = X₁ := by rw [h1]
  have hX₁L : X₁ ≤ normalizer (L : Set G) := by
    intro y hy
    rw [mem_conjugate_iff_conj_mem] at hy
    have h1 := hXL hy
    have h2 : y = q₀⁻¹ * (q₀ * y * q₀⁻¹) * q₀ := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem (le_normalizer hq₀L)) h1) (le_normalizer hq₀L)
  have hX₁C : X₁ ≤ centralizer ({a * z} : Set G) := by
    intro y hy
    rw [mem_conjugate_iff_conj_mem] at hy
    have h1 := mem_centralizer_singleton_iff.mp (hXC hy)
    rw [mem_centralizer_singleton_iff, ← hq₀az]
    calc y * (q₀⁻¹ * a * q₀) = q₀⁻¹ * ((q₀ * y * q₀⁻¹) * a) * q₀ := by group
      _ = q₀⁻¹ * (a * (q₀ * y * q₀⁻¹)) * q₀ := by rw [h1]
      _ = q₀⁻¹ * a * q₀ * y := by group
  have hX₁a : X₁ ≤ centralizer ({a} : Set G) := by
    intro y hy
    have h1 := mem_centralizer_singleton_iff.mp (hX₁C hy)
    have h2 := hfixz y (hX₁L hy)
    rw [mem_centralizer_singleton_iff]
    calc y * a = y * (a * z) * z⁻¹ := by group
      _ = a * z * y * z⁻¹ := by rw [h1]
      _ = a * (z * y) * z⁻¹ := by group
      _ = a * (y * z) * z⁻¹ := by rw [h2]
      _ = a * y := by group
  have hXX₁ : X ≤ normalizer (X₁ : Set G) := by
    intro x hx
    have hxN : q₀ * x * q₀⁻¹ ∈ normalizer (X : Set G) := by
      rw [hNX, mem_centralizer_singleton_iff]
      have h1 := mem_centralizer_singleton_iff.mp (hXC hx)
      have h2 := hfixz x (hXL hx)
      calc q₀ * x * q₀⁻¹ * a = q₀ * (x * (q₀⁻¹ * a * q₀)) * q₀⁻¹ := by group
        _ = q₀ * (x * (a * z)) * q₀⁻¹ := by rw [hq₀az]
        _ = q₀ * (a * z * x) * q₀⁻¹ := by
          rw [show x * (a * z) = a * z * x by rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]]
        _ = q₀ * (q₀⁻¹ * a * q₀) * x * q₀⁻¹ := by rw [hq₀az]; group
        _ = a * (q₀ * x * q₀⁻¹) := by group
    rw [mem_normalizer_iff_conjugate_eq, hX₁, conjugate_conjugate]
    rw [mem_normalizer_iff_conjugate_eq] at hxN
    calc CFSG.conjugate X (q₀ * x) = CFSG.conjugate X ((q₀ * x * q₀⁻¹) * q₀) := by group
      _ = CFSG.conjugate (CFSG.conjugate X (q₀ * x * q₀⁻¹)) q₀ := (conjugate_conjugate _ _ _).symm
      _ = CFSG.conjugate X q₀ := by rw [hxN]
  have hX₁X : X₁ ≤ normalizer (X : Set G) := hNX ▸ hX₁a
  have hinf : X ⊓ X₁ = ⊥ := by
    by_contra hne
    have hp : IsPGroup 2 (X ⊓ X₁ : Subgroup G) := hX2.to_le inf_le_left
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hn0 : n ≠ 0 := by
      intro h0
      apply hne
      rw [h0, pow_zero] at hn
      exact (card_eq_one.mp hn)
    have h2 : 2 ∣ Nat.card (X ⊓ X₁ : Subgroup G) := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (X ⊓ X₁ : Subgroup G)) 2 h2
    have huX : (u : G) ∈ X := (mem_inf.mp u.2).1
    have huX₁ : (u : G) ∈ X₁ := (mem_inf.mp u.2).2
    have hu2 : orderOf (u : G) = 2 := (Subgroup.orderOf_coe u).trans hu
    have hua : (u : G) = a := by
      have := eq_of_orderOf_eq_two_of_isCyclic (X := X) (u := ⟨u, huX⟩) (v := ⟨a, haX⟩)
        ((Subgroup.orderOf_mk _ _).trans hu2) ((Subgroup.orderOf_mk _ _).trans ha)
      exact congrArg Subtype.val this
    have hu' : q₀ * (u : G) * q₀⁻¹ ∈ X := mem_conjugate_iff_conj_mem.mp huX₁
    have hu'2 : orderOf (q₀ * (u : G) * q₀⁻¹) = 2 := by
      rw [← hu2]
      have h := MulEquiv.orderOf_eq (MulAut.conj q₀) (u : G)
      rwa [MulAut.conj_apply] at h
    have hua' : q₀ * (u : G) * q₀⁻¹ = a := by
      have := eq_of_orderOf_eq_two_of_isCyclic (X := X) (u := ⟨_, hu'⟩) (v := ⟨a, haX⟩)
        ((Subgroup.orderOf_mk _ _).trans hu'2) ((Subgroup.orderOf_mk _ _).trans ha)
      exact congrArg Subtype.val this
    apply hq₀
    rw [hua] at hua'
    calc q₀⁻¹ * a * q₀ = q₀⁻¹ * (q₀ * a * q₀⁻¹) * q₀ := by rw [hua']
      _ = a := by group
  have hcomm : ∀ x ∈ X, ∀ y ∈ X₁, x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ X₁ := by
      have := (mem_normalizer_iff.mp (hXX₁ hx) y).mp hy
      exact mul_mem this (inv_mem hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ X := by
      have := (mem_normalizer_iff.mp (hX₁X hy) x⁻¹).mp (inv_mem hx)
      rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
      exact mul_mem hx this
    have h3 : x * y * x⁻¹ * y⁻¹ = 1 := by
      have := mem_inf.mpr ⟨h2, h1⟩
      rw [hinf, mem_bot] at this
      exact this
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  have hLN : L ≤ normalizer ((X ⊔ X₁ : Subgroup G) : Set G) := by
    intro q hq
    rw [mem_normalizer_iff_conjugate_eq]
    unfold CFSG.conjugate
    rw [Subgroup.map_sup]
    change CFSG.conjugate X q ⊔ CFSG.conjugate X₁ q = X ⊔ X₁
    have hX₁q : CFSG.conjugate X₁ q = X ∨ CFSG.conjugate X₁ q = X₁ := by
      rw [hX₁, conjugate_conjugate]
      exact htwo _ (mul_mem hq₀L hq)
    have hne : CFSG.conjugate X q ≠ CFSG.conjugate X₁ q := fun h =>
      hX₁ne (conjugate_injective q h).symm
    rcases htwo q hq with h | h
    · rcases hX₁q with h' | h'
      · exact absurd (h.trans h'.symm) hne
      · rw [h, h']
    · rcases hX₁q with h' | h'
      · rw [h, h', sup_comm]
      · exact absurd (h.trans h'.symm) hne
  have hiso : Nonempty ((X ⊔ X₁ : Subgroup G) ≃* X × X) := by
    let f : X →* G := X.subtype
    let g : X →* G := (MulAut.conj q₀⁻¹).toMonoidHom.comp X.subtype
    have hgX₁ : ∀ x : X, g x ∈ X₁ := fun x => by
      change q₀⁻¹ * (x : G) * q₀⁻¹⁻¹ ∈ X₁
      rw [inv_inv]
      exact inv_mul_mul_mem_conjugate x.2
    have hfg : ∀ (m n : X), Commute (f m) (g n) := fun m n => hcomm m m.2 (g n) (hgX₁ n)
    have hrange_g : g.range = X₁ := by
      rw [MonoidHom.range_comp, range_subtype]
      rfl
    have hinj : Function.Injective (MonoidHom.noncommCoprod f g hfg) := by
      rw [MonoidHom.noncommCoprod_injective]
      refine ⟨X.subtype_injective, ?_, ?_⟩
      · exact (MulAut.conj q₀⁻¹).injective.comp X.subtype_injective
      · rw [range_subtype, hrange_g, disjoint_iff]
        exact hinf
    have hrange : (MonoidHom.noncommCoprod f g hfg).range = X ⊔ X₁ := by
      rw [MonoidHom.noncommCoprod_range, range_subtype, hrange_g]
    exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩
  have hdclaim : ∀ q ∈ L, q⁻¹ * a * q ≠ a → ∀ s : G, zpowers s = X →
      s⁻¹ * (q⁻¹ * s * q) ∈ L ∧ orderOf (s⁻¹ * (q⁻¹ * s * q)) = Nat.card X := by
    intro q hq hqa s hs
    have hsX : s ∈ X := hs ▸ mem_zpowers s
    have hXq : CFSG.conjugate X q = X₁ :=
      (htwo q hq).resolve_left fun h => hqa ((hXq_iff q).mp h)
    have hsq : q⁻¹ * s * q ∈ X₁ := hXq ▸ inv_mul_mul_mem_conjugate hsX
    refine ⟨?_, ?_⟩
    · have h1 : s⁻¹ * q⁻¹ * s ∈ L := (mem_normalizer_iff''.mp (hXL hsX) q⁻¹).mp (inv_mem hq)
      rw [show s⁻¹ * (q⁻¹ * s * q) = s⁻¹ * q⁻¹ * s * q by group]
      exact mul_mem h1 hq
    · rw [← hs, Nat.card_zpowers, orderOf_eq_orderOf_iff]
      intro n
      have hc : Commute s⁻¹ (q⁻¹ * s * q) := hcomm _ (inv_mem hsX) _ hsq
      rw [hc.mul_pow]
      constructor
      · intro h
        have h1 : s⁻¹ ^ n = ((q⁻¹ * s * q) ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h
        have hmem : s⁻¹ ^ n ∈ X ⊓ X₁ := by
          refine mem_inf.mpr ⟨pow_mem (inv_mem hsX) n, ?_⟩
          rw [h1]
          exact inv_mem (pow_mem hsq n)
        rw [hinf, mem_bot, inv_pow, inv_eq_one] at hmem
        exact hmem
      · intro h
        have h2 : (q⁻¹ * s * q) ^ n = 1 := by
          rw [show q⁻¹ * s * q = q⁻¹ * s * q⁻¹⁻¹ by rw [inv_inv], conj_pow, h]
          group
        rw [inv_pow, h, h2, inv_one, one_mul]
  refine ⟨⟨q₀, hq₀L, hX₁ne, htwo, hcomm, hinf, hLN, hiso⟩, hdclaim, ?_, ?_⟩
  ·
    obtain ⟨⟨s, hsX⟩, hgen⟩ := IsCyclic.exists_generator (α := X)
    have hs : zpowers s = X := by
      apply le_antisymm (zpowers_le.mpr hsX)
      intro y hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hgen ⟨y, hy⟩)
      refine mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have hd := hdclaim q₀ hq₀L hq₀ s hs
    have hdvd : orderOf (s⁻¹ * (q₀⁻¹ * s * q₀)) ∣ 2 ^ e :=
      orderOf_dvd_of_pow_eq_one (hexp _ hd.1)
    rw [hd.2] at hdvd
    exact Nat.le_of_dvd (by positivity) hdvd
  ·
    intro b hb hbnc
    apply le_antisymm
    · rw [← hLz]
      exact commutator_mono (zpowers_le.mpr hb) le_rfl
    · obtain ⟨y, hy, hby⟩ := hbnc
      have hne : ⁅zpowers b, L⁆ ≠ ⊥ := by
        intro h
        apply hby
        have hle := commutator_eq_bot_iff_le_centralizer.mp h
        have := mem_centralizer_iff.mp (hle (mem_zpowers b)) y hy
        exact this.symm
      obtain ⟨⟨c, hc⟩, hc1⟩ := ne_bot_iff_exists_ne_one.mp hne
      have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
      have hcz : c ∈ zpowers z := by
        rw [← hLz]
        exact commutator_mono (zpowers_le.mpr hb) le_rfl hc
      rcases eq_one_or_eq_of_mem_zpowers hz hcz with h | h
      · exact absurd h hc1'
      · rw [zpowers_le, ← h]
        exact hc

end CFSG.LocalAnalysis.GorensteinLyons

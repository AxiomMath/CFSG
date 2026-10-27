module

public import CFSG.GF2Type.Aschbacher1976Full.WidthTI

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_Fz_of_normal_two {z : G} (hF2 : IsPGroup 2 (Fz z)) {K : Subgroup G}
    (hKH : K ≤ Hz z) (hKn : ∀ g ∈ Hz z, ∀ x ∈ K, g * x * g⁻¹ ∈ K) (hK2 : IsPGroup 2 K) :
    K ≤ Fz z := by
  have hK'' : IsPGroup 2 (K.comap (Hz z).subtype) := hK2.comap_subtype
  have hN : (K.comap (Hz z).subtype).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    have := hKn (g : G) g.2 _ hn
    simpa using this
  have hle : K.comap (Hz z).subtype ≤ CFSG.pCore 2 ↥(Hz z) :=
    le_sSup (s := {L : Subgroup ↥(Hz z) | L.Normal ∧ IsPGroup 2 L}) ⟨hN, hK''⟩
  rw [pCore_eq_gf hF2] at hle
  intro x hx
  have hxH : x ∈ Hz z := hKH hx
  have hmem : (⟨x, hxH⟩ : ↥(Hz z)) ∈ generalizedFitting ↥(Hz z) :=
    hle (Subgroup.mem_comap.mpr hx)
  exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hmem, rfl⟩

section Stab

variable {z : G} {w : ℕ} {Z A : Subgroup G}

def stabSub (hD : Z4Data z w Z A) (hz : orderOf z = 2) : Subgroup G where
  carrier := {h | h ∈ Hz z ∧ ∀ a ∈ Fz z, a⁻¹ * (h⁻¹ * a * h) ∈ Z}
  mul_mem' := by
    rintro h1 h2 ⟨h1H, h1c⟩ ⟨h2H, h2c⟩
    refine ⟨(Hz z).mul_mem h1H h2H, fun a ha => ?_⟩
    have e : a⁻¹ * ((h1 * h2)⁻¹ * a * (h1 * h2)) =
        (a⁻¹ * (h2⁻¹ * a * h2)) * (h2⁻¹ * (a⁻¹ * (h1⁻¹ * a * h1)) * h2⁻¹⁻¹) := by group
    show a⁻¹ * ((h1 * h2)⁻¹ * a * (h1 * h2)) ∈ Z
    rw [e]
    exact Z.mul_mem (h2c a ha) (Z_conj_mem hD hz ((Hz z).inv_mem h2H) (h1c a ha))
  one_mem' := by
    refine ⟨(Hz z).one_mem, fun a _ => ?_⟩
    simp
  inv_mem' := by
    rintro h ⟨hH, hc⟩
    refine ⟨(Hz z).inv_mem hH, fun a ha => ?_⟩
    have ha1 : h * a * h⁻¹ ∈ Fz z := Fz_conj_mem hH ha
    have hc1 := hc _ ha1
    have e : a⁻¹ * (h⁻¹⁻¹ * a * h⁻¹) =
        ((h * a * h⁻¹)⁻¹ * (h⁻¹ * (h * a * h⁻¹) * h))⁻¹ := by group
    show a⁻¹ * (h⁻¹⁻¹ * a * h⁻¹) ∈ Z
    rw [e]
    exact Z.inv_mem hc1

theorem mem_stabSub {hD : Z4Data z w Z A} {hz : orderOf z = 2} {h : G} :
    h ∈ stabSub hD hz ↔ h ∈ Hz z ∧ ∀ a ∈ Fz z, a⁻¹ * (h⁻¹ * a * h) ∈ Z := Iff.rfl

theorem stabSub_normal (hD : Z4Data z w Z A) (hz : orderOf z = 2) {g x : G}
    (hg : g ∈ Hz z) (hx : x ∈ stabSub hD hz) : g * x * g⁻¹ ∈ stabSub hD hz := by
  rw [mem_stabSub] at hx ⊢
  obtain ⟨hxH, hxc⟩ := hx
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxH) ((Hz z).inv_mem hg), fun a ha => ?_⟩
  have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ Fz z := Fz_conj_mem ((Hz z).inv_mem hg) ha
  have hc' := hxc _ ha'
  have e : a⁻¹ * ((g * x * g⁻¹)⁻¹ * a * (g * x * g⁻¹)) =
      g * ((g⁻¹ * a * g⁻¹⁻¹)⁻¹ * (x⁻¹ * (g⁻¹ * a * g⁻¹⁻¹) * x)) * g⁻¹ := by group
  show a⁻¹ * ((g * x * g⁻¹)⁻¹ * a * (g * x * g⁻¹)) ∈ Z
  rw [e]
  exact Z_conj_mem hD hz hg hc'

theorem stab_odd_eq_one (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    {h : G} (hh : h ∈ stabSub hD hz) (hodd : Odd (orderOf h)) : h = 1 := by
  rw [mem_stabSub] at hh
  obtain ⟨hH, hc⟩ := hh
  obtain ⟨t, ht⟩ := hodd
  have hmpow : h ^ orderOf h = 1 := pow_orderOf_eq_one h
  have hsq := sq_trivial hD hz hH
  have hpow2 : ∀ n : ℕ, ∀ x ∈ Z, h ^ (2 * n) * x * (h ^ (2 * n))⁻¹ = x := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      have e : h ^ (2 * (n + 1)) = h * h * h ^ (2 * n) := by
        rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add, sq]
      rw [e]
      calc h * h * h ^ (2 * n) * x * (h * h * h ^ (2 * n))⁻¹
          = h * (h * (h ^ (2 * n) * x * (h ^ (2 * n))⁻¹) * h⁻¹) * h⁻¹ := by group
        _ = h * (h * x * h⁻¹) * h⁻¹ := by rw [ih x hx]
        _ = x := hsq x hx
  have hfix : ∀ x ∈ Z, h * x * h⁻¹ = x := by
    intro x hx
    have e1 : h ^ (2 * (t + 1)) = h := by
      rw [show 2 * (t + 1) = orderOf h + 1 by omega, pow_succ, hmpow, one_mul]
    have := hpow2 (t + 1) x hx
    rw [e1] at this
    exact this
  have hfix' : ∀ x ∈ Z, h⁻¹ * x * h = x := by
    intro x hx
    calc h⁻¹ * x * h = h⁻¹ * (h * x * h⁻¹) * h := by rw [hfix x hx]
      _ = x := by group
  have hpowc : ∀ a ∈ Fz z, ∃ c ∈ Z, h⁻¹ * a * h = a * c := by
    intro a ha
    refine ⟨a⁻¹ * (h⁻¹ * a * h), hc a ha, ?_⟩
    group
  have hall : ∀ a ∈ Fz z, h⁻¹ * a * h = a := by
    intro a ha
    obtain ⟨c, hcZ, hac⟩ := hpowc a ha
    have hpow : ∀ n : ℕ, (h⁻¹) ^ n * a * h ^ n = a * c ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hcn : h⁻¹ * c ^ n * h = c ^ n := hfix' _ (Z.pow_mem hcZ n)
        calc (h⁻¹) ^ (n + 1) * a * h ^ (n + 1)
            = h⁻¹ * ((h⁻¹) ^ n * a * h ^ n) * h := by
              rw [pow_succ', pow_succ]; group
          _ = h⁻¹ * (a * c ^ n) * h := by rw [ih]
          _ = (h⁻¹ * a * h) * (h⁻¹ * c ^ n * h) := by group
          _ = (a * c) * c ^ n := by rw [hcn, hac]
          _ = a * c ^ (n + 1) := by rw [pow_succ]; group
    have hm := hpow (orderOf h)
    rw [inv_pow, hmpow, inv_one, one_mul, mul_one] at hm
    have hc1 : c ^ orderOf h = 1 := by
      have := hm.symm
      exact mul_eq_left.mp this
    have hcord : orderOf c = 1 := by
      have h1 : orderOf c ∣ orderOf h := orderOf_dvd_of_pow_eq_one hc1
      have h2 : orderOf c ∣ 4 := by
        have := orderOf_dvd_natCard (⟨c, hcZ⟩ : Z)
        rwa [hD.card_Z, Subgroup.orderOf_mk] at this
      have hcop : Nat.Coprime (orderOf h) 4 := by
        have h2' : Nat.Coprime (orderOf h) 2 := by
          apply Nat.Coprime.symm
          rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
          omega
        exact Nat.Coprime.pow_right 2 h2'
      have hg := Nat.dvd_gcd h1 h2
      rw [Nat.Coprime.gcd_eq_one hcop] at hg
      exact Nat.dvd_one.mp hg
    have hc_one : c = 1 := orderOf_eq_one_iff.mp hcord
    rw [hac, hc_one, mul_one]
  have hcentr : ∀ q ∈ coreAt z, h * q = q * h := by
    intro q hq
    rw [coreAt_eq_Fz hF2] at hq
    have hq' := hall q hq
    have e : h * (h⁻¹ * q * h) = q * h := by group
    rw [hq'] at e
    exact e
  have hhF : h ∈ Fz z := by
    have := selfCent_F hF2 h hH hcentr
    rwa [coreAt_eq_Fz hF2] at this
  obtain ⟨k, hk⟩ := hF2 ⟨h, hhF⟩
  have hk' : h ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime (orderOf h) (2 ^ k) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  have hg1 : h ^ Nat.gcd (orderOf h) (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hmpow, hk'⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg1
  exact hg1

end Stab

end CFSG.GF2Type.Aschbacher1976Full.Width

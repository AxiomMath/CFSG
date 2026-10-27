module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma13dDih

open DihedralGroup

section OddPart

variable {k : ℕ}

theorem exists_r_of_odd {g : DihedralGroup k} (h : Odd (orderOf g)) : ∃ i, g = r i := by
  rcases g with i | i
  · exact ⟨i, rfl⟩
  · rw [orderOf_sr] at h
    exact absurd h (by decide)

theorem orderOf_r_two_pow [NeZero k] {v k' : ℕ} (hk : k = 2 ^ v * k') :
    orderOf (r (((2 ^ v : ℕ)) : ZMod k)) = k' := by
  have h1 : r (((2 ^ v : ℕ)) : ZMod k) = (r (1 : ZMod k)) ^ (2 ^ v) := (r_one_pow _).symm
  have h2 : 2 ^ v ∣ orderOf (r (1 : ZMod k)) := by
    rw [orderOf_r_one]
    exact ⟨k', hk⟩
  rw [h1, orderOf_pow_of_dvd (pow_ne_zero v two_ne_zero) h2, orderOf_r_one, hk,
    Nat.mul_div_cancel_left _ (by positivity)]

theorem odd_orderOf_r_iff [NeZero k] {v k' : ℕ} (hk' : Odd k') (hk : k = 2 ^ v * k') (ζ : ZMod k) :
    Odd (orderOf (r ζ)) ↔ 2 ^ v ∣ ζ.val := by
  constructor
  · intro h
    rw [orderOf_r] at h
    set g := Nat.gcd k ζ.val with hg
    have hgk : g ∣ k := Nat.gcd_dvd_left _ _
    have hk2 : k = g * (k / g) := (Nat.mul_div_cancel' hgk).symm
    have hdvd : 2 ^ v ∣ g * (k / g) := by
      rw [← hk2, hk]
      exact Dvd.intro _ rfl
    have hcop : Nat.Coprime (2 ^ v) (k / g) :=
      Nat.Coprime.pow_left v (Nat.coprime_two_left.mpr h)
    exact (hcop.dvd_of_dvd_mul_right hdvd).trans (Nat.gcd_dvd_right _ _)
  · rintro ⟨m, hm⟩
    have h1 : r ζ = ((r (1 : ZMod k)) ^ (2 ^ v)) ^ m := by
      rw [← pow_mul, ← hm, r_one_pow, ZMod.natCast_zmod_val]
    have h2 : 2 ^ v ∣ orderOf (r (1 : ZMod k)) := by
      rw [orderOf_r_one]
      exact ⟨k', hk⟩
    have h3 : orderOf ((r (1 : ZMod k)) ^ (2 ^ v)) = k' := by
      rw [orderOf_pow_of_dvd (pow_ne_zero v two_ne_zero) h2, orderOf_r_one, hk,
        Nat.mul_div_cancel_left _ (by positivity)]
    rw [h1]
    exact Odd.of_dvd_nat (h3 ▸ hk') (orderOf_pow_dvd m)

theorem mem_zpowers_iff_odd [NeZero k] {v k' : ℕ} (hk' : Odd k') (hk : k = 2 ^ v * k')
    (g : DihedralGroup k) :
    g ∈ Subgroup.zpowers (r (((2 ^ v : ℕ)) : ZMod k)) ↔ Odd (orderOf g) := by
  constructor
  · intro hg
    exact Odd.of_dvd_nat (orderOf_r_two_pow hk ▸ hk') (orderOf_dvd_of_mem_zpowers hg)
  · intro hg
    obtain ⟨ζ, rfl⟩ := exists_r_of_odd hg
    obtain ⟨m, hm⟩ := (odd_orderOf_r_iff hk' hk ζ).mp hg
    have h1 : r ζ = (r (((2 ^ v : ℕ)) : ZMod k)) ^ m := by
      rw [r_pow, ← Nat.cast_mul, ← hm, ZMod.natCast_zmod_val]
    rw [h1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m

theorem orderOf_conj_eq {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) x
  rwa [MulAut.conj_apply] at this

theorem exists_odd_part [NeZero k] :
    ∃ X : Subgroup (DihedralGroup k), X.Normal ∧ IsCyclic X ∧ (∀ g, g ∈ X ↔ Odd (orderOf g)) ∧
      Odd (Nat.card X) ∧ ∃ s : ℕ, Nat.card (DihedralGroup k) = 2 ^ s * Nat.card X := by
  obtain ⟨v, k', hk', hk⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne k)
  have hcard : Nat.card (Subgroup.zpowers (r (((2 ^ v : ℕ)) : ZMod k))) = k' := by
    rw [Nat.card_zpowers, orderOf_r_two_pow hk]
  refine ⟨Subgroup.zpowers (r (((2 ^ v : ℕ)) : ZMod k)), ⟨fun n hn g => ?_⟩, inferInstance,
    mem_zpowers_iff_odd hk' hk, hcard ▸ hk', v + 1, ?_⟩
  · rw [mem_zpowers_iff_odd hk' hk] at hn ⊢
    rwa [orderOf_conj_eq]
  · rw [hcard, nat_card, hk]
    ring

end OddPart

section Aut

variable {k : ℕ}

theorem exists_aut_form (hk : 3 ≤ k) (α : MulAut (DihedralGroup k)) :
    ∃ a b : ZMod k, (∀ i, α (r i) = r (a * i)) ∧ ∀ j, α (sr j) = sr (b + a * j) := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, α (r 1) = r a := by
    rcases h : α (r (1 : ZMod k)) with a | a
    · exact ⟨a, rfl⟩
    · exfalso
      have h1 := MulEquiv.orderOf_eq α (r (1 : ZMod k))
      rw [h, orderOf_sr, orderOf_r_one] at h1
      omega
  have hr : ∀ i : ZMod k, α (r i) = r (a * i) := by
    intro i
    have h1 : r i = (r (1 : ZMod k)) ^ i.val := by rw [r_one_pow, ZMod.natCast_zmod_val]
    rw [h1, map_pow, ha, r_pow, ZMod.natCast_zmod_val]
  obtain ⟨b, hb⟩ : ∃ b, α (sr 0) = sr b := by
    rcases h : α (sr (0 : ZMod k)) with c | b
    · exfalso
      have h1 : sr (0 : ZMod k) * r 1 = r 1 * sr 0 := by
        apply α.injective
        rw [map_mul, map_mul, h, ha]
        rw [r_mul_r, r_mul_r, add_comm]
      simp only [r_mul_sr, sr_mul_r, sr.injEq, zero_sub, zero_add] at h1
      have h2 : ((2 : ℕ) : ZMod k) = 0 := by
        push_cast
        calc (2 : ZMod k) = 1 + 1 := by norm_num
          _ = 0 := by nth_rewrite 1 [h1]; exact neg_add_cancel 1
      have h3 := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 k).mp h2)
      omega
    · exact ⟨b, rfl⟩
  refine ⟨a, b, hr, fun j => ?_⟩
  have h1 : sr j = r (-j) * sr 0 := by simp
  rw [h1, map_mul, hr, hb, r_mul_sr]
  congr 1
  ring

theorem aut_pow_apply (α : MulAut (DihedralGroup k)) (a b : ZMod k)
    (hr : ∀ i, α (r i) = r (a * i)) (hs : ∀ j, α (sr j) = sr (b + a * j)) (n : ℕ) :
    (∀ i, (α ^ n) (r i) = r (a ^ n * i)) ∧
      ∀ j, (α ^ n) (sr j) = sr (b * ∑ m ∈ Finset.range n, a ^ m + a ^ n * j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun i => ?_, fun j => ?_⟩
    · rw [pow_succ' α n, MulAut.mul_apply, ih1, hr]
      congr 1
      ring
    · rw [pow_succ' α n, MulAut.mul_apply, ih2, hs, geom_sum_succ]
      congr 1
      ring

theorem eq_one_of_pow_odd {v N : ℕ} (hN : Odd N) {x : ZMod (2 ^ v)} (hx : x ^ N = 1) :
    x = 1 := by
  obtain ⟨u, rfl⟩ : IsUnit x := IsUnit.of_pow_eq_one hx hN.pos.ne'
  have h1 : u ^ N = 1 := Units.ext (by simpa using hx)
  have h2 : u ^ Nat.totient (2 ^ v) = 1 := ZMod.pow_totient u
  have h3 : Nat.Coprime N (Nat.totient (2 ^ v)) := by
    cases v with
    | zero => simp
    | succ w =>
      rw [Nat.totient_prime_pow_succ Nat.prime_two]
      simpa using Nat.Coprime.pow_right w (Nat.coprime_two_right.mpr hN)
  have h4 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [h3.gcd_eq_one, pow_one] at h4
  simp [h4]

theorem odd_orderOf_r_of_map_eq_zero [NeZero k] {v k' : ℕ} (hk' : Odd k') (hk : k = 2 ^ v * k')
    {ζ : ZMod k} (h : ZMod.castHom (show 2 ^ v ∣ k from ⟨k', hk⟩) (ZMod (2 ^ v)) ζ = 0) :
    Odd (orderOf (r ζ)) := by
  rw [odd_orderOf_r_iff hk' hk]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

theorem odd_orderOf_aut_mul_inv (hk : 3 ≤ k) (α : MulAut (DihedralGroup k)) (hα : Odd (orderOf α))
    (g : DihedralGroup k) : Odd (orderOf (α g * g⁻¹)) := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨v, k', hk', hkk⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne k)
  obtain ⟨a, b, hr, hs⟩ := exists_aut_form hk α
  set N := orderOf α with hN
  obtain ⟨hr', hs'⟩ := aut_pow_apply α a b hr hs N
  have hα1 : α ^ N = 1 := pow_orderOf_eq_one α
  have ha : a ^ N = 1 := by
    have h1 := hr' 1
    rw [hα1, MulAut.one_apply, mul_one] at h1
    exact (r.inj h1).symm
  have hb : b * ∑ m ∈ Finset.range N, a ^ m = 0 := by
    have h1 := hs' 0
    rw [hα1, MulAut.one_apply, mul_zero, add_zero] at h1
    exact (sr.inj h1).symm
  obtain ⟨π, hπ⟩ : ∃ π : ZMod k →+* ZMod (2 ^ v),
      ∀ ζ : ZMod k, π ζ = 0 → Odd (orderOf (r ζ)) :=
    ⟨ZMod.castHom (show 2 ^ v ∣ k from ⟨k', hkk⟩) (ZMod (2 ^ v)),
      fun ζ h => odd_orderOf_r_of_map_eq_zero hk' hkk h⟩
  have hπa : π a = 1 := eq_one_of_pow_odd hα (by rw [← map_pow π a N, ha, map_one])
  have hπb : π b = 0 := by
    have h1 : π b * (N : ZMod (2 ^ v)) = 0 := by
      have h2 := congrArg π hb
      rw [map_mul, map_sum, map_zero] at h2
      simpa [map_pow, hπa] using h2
    have h2 : IsUnit (N : ZMod (2 ^ v)) :=
      (ZMod.isUnit_iff_coprime N (2 ^ v)).mpr
        (Nat.Coprime.pow_right v (Nat.coprime_two_right.mpr hα))
    exact h2.mul_left_eq_zero.mp h1
  rcases g with i | j
  · rw [hr, inv_r, r_mul_r]
    apply hπ
    rw [map_add, map_mul, map_neg, hπa, one_mul, add_neg_cancel]
  · rw [hs, inv_sr, sr_mul_sr]
    apply hπ
    rw [map_sub, map_add, map_mul, hπa, hπb, zero_add, one_mul, sub_self]

end Aut

end Lemma13dDih

theorem dihedral_odd_part {G : Type*} [Group G] [Finite G] {k : ℕ} (hk : 2 ≤ k)
    (φ : G ≃* DihedralGroup k) :
    ∃ X : Subgroup G, X.Normal ∧ IsCyclic X ∧ (∀ g : G, Odd (orderOf g) ↔ g ∈ X) ∧
      Odd (Nat.card X) ∧ ∃ s : ℕ, Nat.card G = 2 ^ s * Nat.card X := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨X₀, hn, hc, hmem, hodd, s, hs⟩ := Lemma13dDih.exists_odd_part (k := k)
  let e : X₀ ≃* Subgroup.map φ.symm.toMonoidHom X₀ := MulEquiv.subgroupMap φ.symm X₀
  have hcard : Nat.card (Subgroup.map φ.symm.toMonoidHom X₀) = Nat.card X₀ :=
    (Nat.card_congr e.toEquiv).symm
  refine ⟨Subgroup.map φ.symm.toMonoidHom X₀, hn.map _ φ.symm.surjective, e.isCyclic.mp hc, ?_,
    hcard ▸ hodd, s, ?_⟩
  · intro g
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, hmem, MulEquiv.orderOf_eq]
  · rw [hcard, ← hs]
    exact Nat.card_congr φ.toEquiv

theorem dihedral_odd_part_sub {A : Type*} [Group A] [Finite A] (D : Subgroup A) {k : ℕ} (hk : 2 ≤ k)
    (φ : ↥D ≃* DihedralGroup k) :
    ∃ X : Subgroup A, X ≤ D ∧ (∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ ∈ X) ∧ IsCyclic X ∧
      (∀ g ∈ D, (Odd (orderOf g) ↔ g ∈ X)) ∧ Odd (Nat.card X) ∧
        ∃ s : ℕ, Nat.card D = 2 ^ s * Nat.card X := by
  obtain ⟨X', hn, hc, hmem, hodd, s, hs⟩ := dihedral_odd_part hk φ
  have hmap : ∀ g : A, ∀ hg : g ∈ D, g ∈ X'.map D.subtype ↔ (⟨g, hg⟩ : D) ∈ X' := by
    intro g hg
    constructor
    · rintro ⟨x, hx, hxg⟩
      have : x = ⟨g, hg⟩ := Subtype.ext hxg
      rwa [← this]
    · intro h
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hcard : Nat.card (X'.map D.subtype) = Nat.card X' :=
    Subgroup.card_map_of_injective D.subtype_injective
  refine ⟨X'.map D.subtype, Subgroup.map_subtype_le X', ?_, ?_, ?_, hcard ▸ hodd, s, hcard ▸ hs⟩
  · intro d hd x hx
    obtain ⟨x', hx', rfl⟩ := hx
    exact ⟨⟨d, hd⟩ * x' * ⟨d, hd⟩⁻¹, hn.conj_mem x' hx' ⟨d, hd⟩, rfl⟩
  · exact (X'.equivMapOfInjective D.subtype D.subtype_injective).isCyclic.mp hc
  · intro g hg
    rw [hmap g hg, ← hmem, Subgroup.orderOf_mk]

theorem dihedral_odd_aut {G : Type*} [Group G] [Finite G] {k : ℕ} (hk : 3 ≤ k)
    (φ : G ≃* DihedralGroup k) (X : Subgroup G) (hX : ∀ g : G, Odd (orderOf g) → g ∈ X)
    (α : MulAut G) (hα : Odd (orderOf α)) (g : G) : α g * g⁻¹ ∈ X := by
  apply hX
  have h1 : Odd (orderOf (MulAut.congr φ α)) := by rwa [MulEquiv.orderOf_eq]
  have h2 := Lemma13dDih.odd_orderOf_aut_mul_inv hk (MulAut.congr φ α) h1 (φ g)
  have h3 : (MulAut.congr φ α) (φ g) = φ (α g) := by
    show φ (α (φ.symm (φ g))) = φ (α g)
    rw [MulEquiv.symm_apply_apply]
  rw [h3, ← map_inv φ g, ← map_mul φ, MulEquiv.orderOf_eq] at h2
  exact h2

theorem dihedral_normal_odd_comm {A : Type*} [Group A] [Finite A] (D : Subgroup A) {k : ℕ}
    (hk : 3 ≤ k) (φ : ↥D ≃* DihedralGroup k) (X : Subgroup A)
    (hX : ∀ g ∈ D, Odd (orderOf g) → g ∈ X) (c : A) (hcD : ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hcD' : ∀ d ∈ D, c⁻¹ * d * c ∈ D) (hc : Odd (orderOf c)) (d : A) (hd : d ∈ D) :
    c * d * c⁻¹ * d⁻¹ ∈ X := by
  let α : MulAut ↥D :=
    { toFun := fun x => ⟨c * x * c⁻¹, hcD x x.2⟩
      invFun := fun x => ⟨c⁻¹ * x * c, hcD' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hpow : ∀ n : ℕ, ∀ x : ↥D, ((α ^ n) x : A) = c ^ n * x * (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ' α n, MulAut.mul_apply]
      show c * ((α ^ n) x : A) * c⁻¹ = _
      rw [ih]
      group
  have hα : Odd (orderOf α) := by
    have h1 : α ^ orderOf c = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hpow]
      simp [pow_orderOf_eq_one]
    exact Odd.of_dvd_nat hc (orderOf_dvd_of_pow_eq_one h1)
  have h := dihedral_odd_aut hk φ (X.subgroupOf D) (fun g hg => by
    rw [Subgroup.mem_subgroupOf]
    exact hX g g.2 (by rwa [Subgroup.orderOf_coe])) α hα ⟨d, hd⟩
  exact h

end CFSG.GH74.GLS.IVK.Proofs2

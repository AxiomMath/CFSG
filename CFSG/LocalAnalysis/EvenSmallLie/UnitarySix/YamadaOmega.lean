module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNH
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Quasithin CFSG.Sporadic.Schreier
open SolomonWong (mul_comm_of_sq_eq_one)

section G

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def omegaSet (D : ToddParabolic L) (t : G) : Set G :=
  {e | ∃ n ∈ normalizer (toddE D t : Set G), n⁻¹ * t * n = e}

@[expose] def conjOrbit (X : Subgroup G) (e : G) : Set G := {y | ∃ n ∈ X, n⁻¹ * e * n = y}

theorem omegaSet_eq (D : ToddParabolic L) (t : G) :
    omegaSet D t = conjOrbit (normalizer (toddE D t : Set G)) t := rfl

theorem conj_mem_conjOrbit {X : Subgroup G} {e y x : G} (hx : x ∈ X) (hy : y ∈ conjOrbit X e) :
    x⁻¹ * y * x ∈ conjOrbit X e := by
  obtain ⟨n, hn, rfl⟩ := hy
  exact ⟨n * x, mul_mem hn hx, by group⟩

theorem conj_mem_conjOrbit' {X : Subgroup G} {e y x : G} (hx : x ∈ X) (hy : y ∈ conjOrbit X e) :
    x * y * x⁻¹ ∈ conjOrbit X e := by
  have := conj_mem_conjOrbit (inv_mem hx) hy
  rwa [inv_inv] at this

theorem self_mem_conjOrbit (X : Subgroup G) (e : G) : e ∈ conjOrbit X e :=
  ⟨1, one_mem X, by group⟩

theorem conjOrbit_eq_of_mem {X : Subgroup G} {e y : G} (hy : y ∈ conjOrbit X e) :
    conjOrbit X y = conjOrbit X e := by
  obtain ⟨n, hn, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨n * m, mul_mem hn hm, by group⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨n⁻¹ * m, mul_mem (inv_mem hn) hm, by group⟩

theorem ncard_conjOrbit_mul [Finite G] {X : Subgroup G} {e : G} (he : e ∈ X) :
    (conjOrbit X e).ncard * Nat.card (X ⊓ centralizer ({e} : Set G) : Subgroup G) =
      Nat.card X := by
  have := Fintype.ofFinite X
  set eX : X := ⟨e, he⟩
  have h1 := MulAction.card_conjClass_mul_card_centralizer eX
  rw [← Nat.card_eq_fintype_card] at h1
  rw [← h1]
  congr 1
  · rw [← Nat.card_coe_set_eq]
    refine (Nat.card_congr ?_).symm
    refine Equiv.ofBijective (fun y => ⟨(y : X), ?_⟩) ⟨?_, ?_⟩
    · obtain ⟨c, hc⟩ := y.2
      refine ⟨(((ConjAct.ofConjAct c)⁻¹ : X) : G), ((ConjAct.ofConjAct c)⁻¹ : X).2, ?_⟩
      rw [← hc]
      change _ = (((c • eX : X)) : G)
      rw [ConjAct.smul_def]
      simp [eX]
    · intro y₁ y₂ hy
      simp only [Subtype.mk.injEq] at hy
      exact Subtype.ext (Subtype.ext hy)
    · rintro ⟨z, n, hn, rfl⟩
      refine ⟨⟨⟨n⁻¹ * e * n, mul_mem (mul_mem (inv_mem hn) he) hn⟩,
        ⟨ConjAct.toConjAct (⟨n, hn⟩ : X)⁻¹, ?_⟩⟩, rfl⟩
      change ConjAct.toConjAct (⟨n, hn⟩ : X)⁻¹ • eX = _
      rw [ConjAct.smul_def]
      apply Subtype.ext
      simp [eX]
  · refine Nat.card_congr ?_
    refine Equiv.ofBijective (fun y => ⟨⟨y, (mem_inf.1 y.2).1⟩, ?_⟩) ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2)
    · intro y₁ y₂ hy
      apply Subtype.ext
      exact congrArg (fun z : centralizer ({eX} : Set X) => ((z : X) : G)) hy
    · rintro ⟨⟨z, hzX⟩, hz⟩
      refine ⟨⟨z, mem_inf.2 ⟨hzX, ?_⟩⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hz)

theorem mem_commutator_centralizer_G {a : L}
    (ha : a ∈ ⁅centralizer ({a} : Set L), centralizer ({a} : Set L)⁆) :
    (a : G) ∈ ⁅centralizer ({(a : G)} : Set G), centralizer ({(a : G)} : Set G)⁆ := by
  have h1 := mem_map_of_mem L.subtype ha
  rw [map_commutator] at h1
  have hle : (centralizer ({a} : Set L)).map L.subtype ≤ centralizer ({(a : G)} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hy
  exact commutator_mono hle hle h1

theorem conj_mem_commutator_centralizer {a x : G} (n : G)
    (hx : x ∈ ⁅centralizer ({a} : Set G), centralizer ({a} : Set G)⁆) :
    n * x * n⁻¹ ∈ ⁅centralizer ({n * a * n⁻¹} : Set G), centralizer ({n * a * n⁻¹} : Set G)⁆ := by
  have h1 := mem_map_of_mem (MulAut.conj n).toMonoidHom hx
  rw [map_commutator] at h1
  have hle : (centralizer ({a} : Set G)).map (MulAut.conj n).toMonoidHom ≤
      centralizer ({n * a * n⁻¹} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * y * n⁻¹ * (n * a * n⁻¹) = n * (y * a) * n⁻¹ := by group
      _ = n * (a * y) * n⁻¹ := by rw [hy]
      _ = n * a * n⁻¹ * (n * y * n⁻¹) := by group
  have h2 := commutator_mono hle hle h1
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h2

end G

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

omit [Finite G] in
theorem t_mem_X : t ∈ normalizer (toddE D t : Set G) := le_normalizer (t_mem_toddE D t)

theorem toddK_le_X (h : Setting G L D t) : toddK D ≤ normalizer (toddE D t : Set G) := by
  intro k hk
  have hk' : k ∈ normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) :=
    mem_inf.2 ⟨toddK_le_normalizer D hk, h.toddK_le_H hk⟩
  rw [← h.normalizer_toddE_inf] at hk'
  exact (mem_inf.1 hk').1

omit [Finite G] in
theorem omegaSet_subset : omegaSet D t ⊆ toddE D t := by
  rintro _ ⟨n, hn, rfl⟩
  have := (mem_normalizer_iff.1 (inv_mem hn) t).1 (t_mem_toddE D t)
  rwa [inv_inv] at this

omit [Finite G] in
theorem t_mem_omega : t ∈ omegaSet D t := self_mem_conjOrbit _ _

theorem one_not_mem_omega (h : Setting G L D t) : (1 : G) ∉ omegaSet D t := by
  rintro ⟨n, -, hn⟩
  apply h.t_ne_one
  calc t = n * (n⁻¹ * t * n) * n⁻¹ := by group
    _ = 1 := by rw [hn]; group

theorem omega_invariant (h : Setting G L D t) :
    ∀ c ∈ toddK D, ∀ y ∈ omegaSet D t, c * y * c⁻¹ ∈ omegaSet D t :=
  fun _ hc _ hy => conj_mem_conjOrbit' (h.toddK_le_X hc) hy

theorem ncard_omega_mul (h : Setting G L D t) :
    (omegaSet D t).ncard * Nat.card (normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) :
      Subgroup G) = Nat.card (normalizer (toddE D t : Set G)) := by
  rw [← h.normalizer_toddE_inf]
  exact ncard_conjOrbit_mul t_mem_X

theorem not_mem_omega_of_comm (h : Setting G L D t) {a : G}
    (ha : a ∈ ⁅centralizer ({a} : Set G), centralizer ({a} : Set G)⁆) : a ∉ omegaSet D t := by
  rintro ⟨n, -, hn⟩
  apply h.t_not_mem_commutator
  have h1 := conj_mem_commutator_centralizer n ha
  rw [← hn, show n * (n⁻¹ * t * n) * n⁻¹ = t by group] at h1
  exact h1

theorem a₁_not_mem_omega (h : Setting G L D t) : (D.a₁ : G) ∉ omegaSet D t :=
  h.not_mem_omega_of_comm (mem_commutator_centralizer_G h.facts.comm_a₁)

theorem a₂_not_mem_omega (h : Setting G L D t) : (D.a₂ : G) ∉ omegaSet D t :=
  h.not_mem_omega_of_comm (mem_commutator_centralizer_G h.facts.comm_a₂)

theorem exists_mem_omega_ne (h : Setting G L D t) : ∃ e ∈ omegaSet D t, e ≠ t := by
  obtain ⟨g, hgE, hgt⟩ := h.exists_conj_mem_toddE_ne
  obtain ⟨n, hn, hgn⟩ := h.fusion hgE
  exact ⟨g⁻¹ * t * g, ⟨n, hn, hgn.symm⟩, hgt⟩

theorem mem_toddE_of_comm (h : Setting G L D t) {x : G} (hxA : ∀ a ∈ toddA D, x * a * x⁻¹ = a)
    (hxt : x * t * x⁻¹ = t) : x ∈ toddE D t := by
  rw [← h.centralizer_toddE_eq, mem_centralizer_iff]
  intro e he
  have hc : ∀ y : G, x * y * x⁻¹ = y → y * x = x * y := fun y hy => by
    calc y * x = x * y * x⁻¹ * x := by rw [hy]
      _ = x * y := by group
  obtain ⟨a, ha, hea | hea⟩ := h.eq_or_eq_mul_of_mem_toddE he <;> rw [hea]
  · exact hc a (hxA a ha)
  · refine hc _ ?_
    rw [show x * (a * t) * x⁻¹ = (x * a * x⁻¹) * (x * t * x⁻¹) by group, hxA a ha, hxt]

theorem not_mem_toddE_of_orderOf (h : Setting G L D t) {x : G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hxp : orderOf x = p) : x ∉ toddE D t := fun hxE => by
  have hd : p ∣ 2 := hxp ▸ orderOf_dvd_of_pow_eq_one (h.toddE_sq x hxE)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)

theorem exists_dvd_two_pow_sub_one (h : Setting G L D t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpX : p ∣ Nat.card (normalizer (toddE D t : Set G))) :
    ∃ j, 1 ≤ j ∧ j ≤ 10 ∧ p ∣ 2 ^ j - 1 := by
  by_contra hcon
  push Not at hcon
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpX
  have hx' : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  have hxp : (x : G) ^ p = 1 := by rw [← hx']; exact pow_orderOf_eq_one _
  have hcent := conj_eq_self_of_prime_of_not_dvd h.card_toddE x.2 hp hp2 hxp
    (fun j hj1 hj2 => hcon j hj1 hj2)
  refine h.not_mem_toddE_of_orderOf hp hp2 hx' (h.mem_toddE_of_comm (fun a ha => hcent a
    (toddA_le_toddE D t ha)) (hcent t (t_mem_toddE D t)))

theorem false_of_mem_normalizer_toddA (h : Setting G L D t) {x : G}
    (hxX : x ∈ normalizer (toddE D t : Set G)) (hxA : x ∈ normalizer (toddA D : Set G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hxp : orderOf x = p)
    (hnot : ∀ j, 1 ≤ j → j ≤ 9 → ¬ p ∣ 2 ^ j - 1) : False := by
  have hxp' : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  have hcA := conj_eq_self_of_prime_of_not_dvd (card_toddA D) hxA hp hp2 hxp' hnot
  have hxt : x * t * x⁻¹ ∈ toddE D t := (mem_normalizer_iff.1 hxX t).1 (t_mem_toddE D t)
  obtain ⟨b, hb, hbe | hbe⟩ := h.eq_or_eq_mul_of_mem_toddE hxt
  · apply h.t_not_mem
    have e : t = x⁻¹ * b * x := by rw [← hbe]; group
    have hb' : x⁻¹ * b * x⁻¹⁻¹ ∈ toddA D := (mem_normalizer_iff.1 (inv_mem hxA) b).1 hb
    rw [inv_inv] at hb'
    rw [e]
    exact toddA_le D hb'
  · have hcb : ∀ k : ℕ, x * b ^ k * x⁻¹ = b ^ k := fun k => by
      rw [← conj_pow, hcA b hb]
    have hk : ∀ k : ℕ, x ^ k * t * (x ^ k)⁻¹ = b ^ k * t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc x ^ (k + 1) * t * (x ^ (k + 1))⁻¹ = x * (x ^ k * t * (x ^ k)⁻¹) * x⁻¹ := by
              rw [pow_succ', mul_inv_rev]
              group
          _ = (x * b ^ k * x⁻¹) * (x * t * x⁻¹) := by rw [ih]; group
          _ = b ^ (k + 1) * t := by rw [hcb, hbe, pow_succ, mul_assoc]
    have hbp : b ^ p = 1 := by
      have := hk p
      rw [hxp', one_mul, inv_one, mul_one] at this
      exact (mul_eq_right.1 this.symm)
    have hb1 : b = 1 := by
      obtain ⟨k, hk'⟩ := hp.odd_of_ne_two hp2
      rw [hk', pow_succ, pow_mul, toddA_sq D b hb, one_pow, one_mul] at hbp
      exact hbp
    rw [hb1, one_mul] at hbe
    exact h.not_mem_toddE_of_orderOf hp hp2 hxp (h.mem_toddE_of_comm (fun a ha => hcA a ha) hbe)

omit [Finite G] in
theorem normalizer_le_of_omega
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t}) :
    normalizer (toddE D t : Set G) ≤ normalizer (toddA D : Set G) := by
  have key : ∀ x ∈ normalizer (toddE D t : Set G), ∀ a ∈ toddA D, x * a * x⁻¹ ∈ toddA D := by
    intro x hx a ha
    have hat : a * t ∈ omegaSet D t := by rw [hΩ]; exact ⟨a, ha, rfl⟩
    have h1 : x * (a * t) * x⁻¹ ∈ omegaSet D t := conj_mem_conjOrbit' hx hat
    have h2 : x * t * x⁻¹ ∈ omegaSet D t := conj_mem_conjOrbit' hx t_mem_omega
    rw [hΩ] at h1 h2
    obtain ⟨b, hb, hb'⟩ := h1
    obtain ⟨c, hc, hc'⟩ := h2
    have e : x * a * x⁻¹ = (x * (a * t) * x⁻¹) * (x * t * x⁻¹)⁻¹ := by
      rw [show (x * t * x⁻¹)⁻¹ = x * t⁻¹ * x⁻¹ by group]
      group
    rw [e, hb', hc', mul_inv_rev, ← mul_assoc, mul_assoc b, mul_inv_cancel, mul_one]
    exact mul_mem hb (inv_mem hc)
  intro x hx
  exact mem_normalizer_of_conj (key x hx) (fun a ha => by
    have := key x⁻¹ (inv_mem hx) a ha
    rwa [inv_inv] at this)

omit [Finite G] in
theorem ncard_toddA_mul_t (D : ToddParabolic L) (t : G) :
    ({e | ∃ a ∈ toddA D, e = a * t} : Set G).ncard = 2 ^ 9 := by
  have e : ({e | ∃ a ∈ toddA D, e = a * t} : Set G) = (· * t) '' (toddA D : Set G) := by
    ext e
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [e, Set.ncard_image_of_injective _ (mul_left_injective t), ← card_eq_ncard, card_toddA]

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada

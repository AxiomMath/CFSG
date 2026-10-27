
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7Inputs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace CFSG.QuasithinUnique.L246.C123

open Equiv

abbrev A7 : Type := ↥(alternatingGroup (Fin 7))

theorem card_A7 : Nat.card A7 = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide

theorem isSimple_A7 : IsSimpleGroup A7 :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

theorem index_ge_seven {H : Subgroup A7} (hH : H ≠ ⊤) : 7 ≤ H.index := by
  classical
  by_contra hlt
  push Not at hlt
  have hsimple := isSimple_A7
  have hfin : Finite (A7 ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  let φ : A7 →* Equiv.Perm (A7 ⧸ H) := MulAction.toPermHom A7 (A7 ⧸ H)
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      apply hH
      rw [eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := h ▸ Subgroup.mem_top g
      have := congrArg (fun σ : Equiv.Perm (A7 ⧸ H) => σ (QuotientGroup.mk 1))
        (MonoidHom.mem_ker.1 hg)
      simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one,
        id_eq] at this
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at this
      have h3 := QuotientGroup.eq.1 this
      rw [mul_one] at h3
      exact H.inv_mem_iff.1 h3
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  have hcard := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_perm] at hcard
  have : Nat.card (A7 ⧸ H) = H.index := rfl
  rw [card_A7, this] at hcard
  interval_cases h : H.index <;> simp [Nat.factorial] at hcard

theorem eq_top_of_dvd {H : Subgroup A7} (h7 : 7 ∣ Nat.card H) (h72 : 72 ∣ Nat.card H) :
    H = ⊤ := by
  by_contra hne
  have h1 := index_ge_seven hne
  have h2 := H.index_mul_card
  rw [card_A7] at h2
  have h504 : 504 ∣ Nat.card H := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 72) h7 h72
    simpa using this
  obtain ⟨k, hk⟩ := h504
  rw [hk] at h2
  have h3 : H.index * k * 504 = 2520 := by rw [← h2]; ring
  have h5 : H.index * k = 5 := by omega
  have : H.index ≤ 5 := Nat.le_of_dvd (by norm_num) ⟨k, h5.symm⟩
  omega

section Conj

def conjSub (c : A7) (H : Subgroup A7) : Subgroup A7 where
  carrier := {x | c⁻¹ * x * c ∈ H}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show c⁻¹ * (a * b) * c ∈ H
    have : c⁻¹ * (a * b) * c = (c⁻¹ * a * c) * (c⁻¹ * b * c) := by group
    rw [this]; exact H.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    show c⁻¹ * a⁻¹ * c ∈ H
    have : c⁻¹ * a⁻¹ * c = (c⁻¹ * a * c)⁻¹ := by group
    rw [this]; exact H.inv_mem ha

theorem mem_conjSub {c : A7} {H : Subgroup A7} {x : A7} : x ∈ conjSub c H ↔ c⁻¹ * x * c ∈ H :=
  Iff.rfl

theorem card_conjSub (c : A7) (H : Subgroup A7) : Nat.card (conjSub c H) = Nat.card H :=
  Nat.card_congr
    { toFun := fun x => ⟨c⁻¹ * x * c, x.2⟩
      invFun := fun y => ⟨c * y * c⁻¹, by
        show c⁻¹ * (c * y * c⁻¹) * c ∈ H
        have : c⁻¹ * (c * (y : A7) * c⁻¹) * c = y := by group
        rw [this]; exact y.2⟩
      left_inv := fun x => by apply Subtype.ext; show c * (c⁻¹ * (x : A7) * c) * c⁻¹ = x; group
      right_inv := fun y => by apply Subtype.ext; show c⁻¹ * (c * (y : A7) * c⁻¹) * c = y; group }

theorem normalizer_conjSub (c : A7) (H : Subgroup A7) (x : A7) :
    x ∈ Subgroup.normalizer (conjSub c H : Set A7) ↔
      c⁻¹ * x * c ∈ Subgroup.normalizer (H : Set A7) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h k
    have := h (c * k * c⁻¹)
    simp only [mem_conjSub] at this
    have e1 : c⁻¹ * (c * k * c⁻¹) * c = k := by group
    have e2 : c⁻¹ * (x * (c * k * c⁻¹) * x⁻¹) * c = c⁻¹ * x * c * k * (c⁻¹ * x * c)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  · intro h k
    have := h (c⁻¹ * k * c)
    simp only [mem_conjSub]
    have e2 : c⁻¹ * (x * k * x⁻¹) * c = c⁻¹ * x * c * (c⁻¹ * k * c) * (c⁻¹ * x * c)⁻¹ := by group
    rw [e2]
    exact this

theorem card_normalizer_conjSub (c : A7) (H : Subgroup A7) :
    Nat.card (Subgroup.normalizer (conjSub c H : Set A7)) =
      Nat.card (Subgroup.normalizer (H : Set A7)) :=
  Nat.card_congr
    { toFun := fun n => ⟨c⁻¹ * n * c, (normalizer_conjSub c H n).1 n.2⟩
      invFun := fun m => ⟨c * m * c⁻¹, (normalizer_conjSub c H _).2 (by
        have : c⁻¹ * (c * (m : A7) * c⁻¹) * c = m := by group
        rw [this]; exact m.2)⟩
      left_inv := fun n => by apply Subtype.ext; show c * (c⁻¹ * (n : A7) * c) * c⁻¹ = n; group
      right_inv := fun m => by
        apply Subtype.ext; show c⁻¹ * (c * (m : A7) * c⁻¹) * c = m; group }

theorem exists_conj_of_card_sylow {G : Type} [Group G] [Finite G] {P Q : Subgroup G}
    (hP : Nat.card P = 2 ^ (Nat.card G).factorization 2)
    (hQ : Nat.card Q = 2 ^ (Nat.card G).factorization 2) :
    ∃ g : G, ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SP : Sylow 2 G := Sylow.ofCard P hP
  let SQ : Sylow 2 G := Sylow.ofCard Q hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SP SQ
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • SP : Sylow 2 G) : Subgroup G) = (SQ : Subgroup G) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h1
  have h2 : (SQ : Subgroup G) = Q := rfl
  have h3 : (SP : Subgroup G) = P := rfl
  rw [h2, h3] at h1
  rw [← h1, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have : g⁻¹ * (MulAut.conj g • s) * g = s := by
      simp only [MulAut.smul_def, MulAut.conj_apply]; group
    rw [this]; exact hs
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp only [MulAut.smul_def, MulAut.conj_apply]; group⟩

theorem fac_card_A7 : (Nat.card A7).factorization 2 = 3 := by
  rw [card_A7, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]

theorem fac_168 : (168 : ℕ).factorization 2 = 3 := by
  rw [show (168 : ℕ) = 2 ^ 3 * 21 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21)]

end Conj

section Explicit

theorem card_eq_of_mem_iff {G : Type} [Group G] (H : Subgroup G) (s : Finset G)
    (h : ∀ g, g ∈ H ↔ g ∈ s) : Nat.card H = s.card := by
  have h1 : (H : Set G) = (s : Set G) := by ext g; simpa using h g
  rw [← Set.ncard_coe_finset, ← h1, ← Nat.card_coe_set_eq]
  rfl

end Explicit

section Klein

theorem mem_normalizer_of_conj_le {K : Subgroup A7} {n : A7} (h : ∀ k ∈ K, n * k * n⁻¹ ∈ K) :
    n ∈ Subgroup.normalizer (K : Set A7) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h k, fun hk => ?_⟩
  have hle : K ≤ conjSub n⁻¹ K := fun x hx => by
    rw [mem_conjSub, inv_inv]; exact h x hx
  have heq : K = conjSub n⁻¹ K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  have hk' : k ∈ conjSub n⁻¹ K := by rw [mem_conjSub, inv_inv]; exact hk
  rw [← heq] at hk'
  exact hk'

end Klein

section Module

variable {U : Type} [CommGroup U]

def actOf (ρ : A7 →* MulAut U) : A7 →* Equiv.Perm U := (MulAut.toPerm U).comp ρ

def fixU (ρ : A7 →* MulAut U) (H : Subgroup A7) : Subgroup U where
  carrier := {u | ∀ h ∈ H, ρ h u = u}
  one_mem' := fun h _ => map_one (ρ h)
  mul_mem' := fun {a b} ha hb h hh => by rw [map_mul, ha h hh, hb h hh]
  inv_mem' := fun {a} ha h hh => by rw [map_inv, ha h hh]

theorem mem_fixU {ρ : A7 →* MulAut U} {H : Subgroup A7} {u : U} :
    u ∈ fixU ρ H ↔ ∀ h ∈ H, ρ h u = u := Iff.rfl

def stabU (ρ : A7 →* MulAut U) (u : U) : Subgroup A7 where
  carrier := {g | ρ g u = u}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have ha' : ρ a u = u := ha
    have hb' : ρ b u = u := hb
    show ρ (a * b) u = u
    rw [map_mul, MulAut.mul_apply, hb', ha']
  inv_mem' := fun {a} ha => by
    have ha' : ρ a u = u := ha
    show ρ a⁻¹ u = u
    calc ρ a⁻¹ u = ρ a⁻¹ (ρ a u) := by rw [ha']
      _ = u := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem mem_stabU {ρ : A7 →* MulAut U} {u : U} {g : A7} : g ∈ stabU ρ u ↔ ρ g u = u := Iff.rfl

def orbU (ρ : A7 →* MulAut U) (u : U) : Set U := {v | ∃ g : A7, ρ g u = v}

theorem index_stabU (ρ : A7 →* MulAut U) (u : U) :
    (stabU ρ u).index = (orbU ρ u).ncard := by
  let _ : MulAction A7 U := MulAction.compHom U (actOf ρ)
  have h1 := MulAction.index_stabilizer A7 u
  have h2 : MulAction.stabilizer A7 u = stabU ρ u := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    rfl
  have h3 : MulAction.orbit A7 u = orbU ρ u := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
  rw [h2, h3] at h1
  exact h1

theorem orbit_card_mul (ρ : A7 →* MulAut U) (u : U) :
    (orbU ρ u).ncard * Nat.card (stabU ρ u) = 2520 := by
  rw [← index_stabU, ← card_A7]
  exact (stabU ρ u).index_mul_card

theorem orbU_subset (ρ : A7 →* MulAut U) {u : U} (hu : u ≠ 1) : orbU ρ u ⊆ {v | v ≠ 1} := by
  rintro _ ⟨g, rfl⟩ h
  apply hu
  have : ρ g u = ρ g 1 := by rw [h, map_one]
  exact (ρ g).injective this

theorem ncard_orbU_le (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16) {u : U} (hu : u ≠ 1) :
    (orbU ρ u).ncard ≤ 15 := by
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h1 := Set.ncard_le_ncard (orbU_subset ρ hu) (Set.toFinite _)
  have h2 : ({v : U | v ≠ 1} : Set U).ncard = 15 := by
    have : ({v : U | v ≠ 1} : Set U) = Set.univ \ {1} := by ext; simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hcard]
  omega

theorem card_dvd_of_card_U (hcard : Nat.card U = 16) (W : Subgroup U) : Nat.card W ∣ 16 := by
  rw [← hcard]; exact Subgroup.card_subgroup_dvd_card W

theorem fixU_zpowers_order_five (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) (g : A7) (hg : orderOf g = 5) :
    fixU ρ (Subgroup.zpowers g) = ⊥ := by
  classical
  let _ : MulAction (Subgroup.zpowers g) U :=
    MulAction.compHom U ((actOf ρ).comp (Subgroup.zpowers g).subtype)
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.zpowers g) := by
    have : Nat.card (Subgroup.zpowers g) = 5 ^ 1 := by rw [Nat.card_zpowers, hg]; norm_num
    exact IsPGroup.of_card this
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hmod := hP.card_modEq_card_fixedPoints U
  have hfp : MulAction.fixedPoints (Subgroup.zpowers g) U =
      (fixU ρ (Subgroup.zpowers g) : Set U) := by
    ext u
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_fixU]
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  have hc : Nat.card ↥(MulAction.fixedPoints (Subgroup.zpowers g) U) =
      Nat.card (fixU ρ (Subgroup.zpowers g)) := by
    rw [hfp]; rfl
  rw [hc, hcard] at hmod
  have hdvd := card_dvd_of_card_U hcard (fixU ρ (Subgroup.zpowers g))
  have hcases : Nat.card (fixU ρ (Subgroup.zpowers g)) = 1 ∨
      Nat.card (fixU ρ (Subgroup.zpowers g)) = 16 := by
    have h16 : Nat.card (fixU ρ (Subgroup.zpowers g)) ∈ Nat.divisors 16 := by
      simpa using hdvd
    have : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
    rw [this] at h16
    simp only [Finset.mem_insert, Finset.mem_singleton] at h16
    rcases h16 with h | h | h | h | h
    · exact Or.inl h
    · rw [h] at hmod; simp [Nat.ModEq] at hmod
    · rw [h] at hmod; simp [Nat.ModEq] at hmod
    · rw [h] at hmod; simp [Nat.ModEq] at hmod
    · exact Or.inr h
  rcases hcases with h1 | h16
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have htop : fixU ρ (Subgroup.zpowers g) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [h16, hcard]
    have hg1 : ρ g = 1 := by
      ext u
      have hu : u ∈ fixU ρ (Subgroup.zpowers g) := by rw [htop]; trivial
      exact hu g (Subgroup.mem_zpowers g)
    have : g = 1 := hinj (by rw [hg1, map_one])
    rw [this, orderOf_one] at hg
    omega

theorem not_dvd_five_card_stabU (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) {u : U} (hu : u ≠ 1) : ¬ 5 ∣ Nat.card (stabU ρ u) := by
  intro h5
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(stabU ρ u)) 5 h5
  have hx' : orderOf (x : A7) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hfix := fixU_zpowers_order_five ρ hcard hinj (x : A7) hx'
  apply hu
  have hmem : u ∈ fixU ρ (Subgroup.zpowers (x : A7)) := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hxs : ∀ k : ℤ, ρ ((x : A7) ^ k) u = u := by
      intro k
      have hmem : (x : A7) ^ k ∈ stabU ρ u := (stabU ρ u).zpow_mem x.2 k
      exact hmem
    exact hxs k
  rw [hfix] at hmem
  exact Subgroup.mem_bot.1 hmem

end Module

section SylowIn

theorem exists_conj_in_of_card_sylow {H P Q : Subgroup A7} (hP : P ≤ H) (hQ : Q ≤ H)
    (hH : Nat.card H = 168) (hPc : Nat.card P = 8) (hQc : Nat.card Q = 8) :
    ∃ h ∈ H, ∀ x : A7, x ∈ Q ↔ h⁻¹ * x * h ∈ P := by
  have hP' : Nat.card (P.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    have : Nat.card (P.subgroupOf H) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
    rw [this, hPc, hH, fac_168]; norm_num
  have hQ' : Nat.card (Q.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    have : Nat.card (Q.subgroupOf H) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
    rw [this, hQc, hH, fac_168]; norm_num
  obtain ⟨h, hh⟩ := exists_conj_of_card_sylow hP' hQ'
  refine ⟨h, h.2, fun x => ?_⟩
  by_cases hx : x ∈ H
  · have := hh ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
    exact this
  · constructor
    · intro hxQ; exact absurd (hQ hxQ) hx
    · intro hxP
      exfalso
      apply hx
      have h1 : (h : A7)⁻¹ * x * (h : A7) ∈ H := hP hxP
      have h2 : (h : A7) * ((h : A7)⁻¹ * x * (h : A7)) * (h : A7)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem h.2 h1) (H.inv_mem h.2)
      have e : (h : A7) * ((h : A7)⁻¹ * x * h) * (h : A7)⁻¹ = x := by group
      rwa [e] at h2

end SylowIn

section Module3

variable {U : Type} [CommGroup U]

theorem exists_fixed_ne_one (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16) {T : Subgroup A7}
    (hT : Nat.card T = 8) : ∃ u ∈ fixU ρ T, u ≠ 1 := by
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥T U := MulAction.compHom U (ρ.comp T.subtype)
  have hp : IsPGroup 2 ↥T := by
    apply IsPGroup.of_card (n := 3)
    rw [hT]; norm_num
  have hmod := hp.card_modEq_card_fixedPoints (α := U)
  rw [hcard] at hmod
  have hfix : Nat.card (MulAction.fixedPoints ↥T U) = Nat.card (fixU ρ T) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun u => ?_
    rw [MulAction.mem_fixedPoints, mem_fixU]
    constructor
    · intro h t ht; exact h ⟨t, ht⟩
    · intro h t; exact h t t.2
  rw [hfix] at hmod
  by_contra hno
  push Not at hno
  have h1 : fixU ρ T = ⊥ := by
    ext u
    rw [Subgroup.mem_bot]
    exact ⟨fun hu => hno u hu, fun h => h ▸ (fixU ρ T).one_mem⟩
  rw [h1, Subgroup.card_bot] at hmod
  have := hmod
  unfold Nat.ModEq at this
  omega

end Module3

section Sq

variable {U : Type} [CommGroup U]

def fixedBy (τ : MulAut U) : Subgroup U where
  carrier := {u | τ u = u}
  one_mem' := map_one τ
  mul_mem' := fun {a b} ha hb => by
    show τ (a * b) = a * b
    rw [map_mul, show τ a = a from ha, show τ b = b from hb]
  inv_mem' := fun {a} ha => by
    show τ a⁻¹ = a⁻¹
    rw [map_inv, show τ a = a from ha]

theorem mem_fixedBy {τ : MulAut U} {u : U} : u ∈ fixedBy τ ↔ τ u = u := Iff.rfl

theorem card_le_sq [Finite U] (hU2 : ∀ u : U, u ^ 2 = 1) (τ : MulAut U) (C : Subgroup U)
    (hC : ∀ c ∈ C, τ c ∈ C) (hτ : ∀ c ∈ C, τ (τ c) = c) :
    Nat.card C ≤ Nat.card ↥(C ⊓ fixedBy τ) ^ 2 := by
  have hinv : ∀ u : U, u⁻¹ = u := fun u => by
    have := hU2 u
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  let φ : ↥C →* U :=
    { toFun := fun c => τ (c : U) * (c : U)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        ac_rfl }
  have hker : φ.ker = (C ⊓ fixedBy τ).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨c.2, ?_⟩
      have h' : τ (c : U) * (c : U)⁻¹ = 1 := h
      exact mul_inv_eq_one.1 h'
    · intro h
      have h' : τ (c : U) = c := h.2
      show τ (c : U) * (c : U)⁻¹ = 1
      rw [h', mul_inv_cancel]
  have hrange : (φ.range : Subgroup U) ≤ C ⊓ fixedBy τ := by
    rintro _ ⟨c, rfl⟩
    refine ⟨C.mul_mem (hC _ c.2) (C.inv_mem c.2), ?_⟩
    show τ (τ (c : U) * (c : U)⁻¹) = τ (c : U) * (c : U)⁻¹
    rw [map_mul, map_inv, hτ _ c.2]
    calc (c : U) * (τ (c : U))⁻¹ = (τ (c : U) * (c : U)⁻¹)⁻¹ := by
          rw [mul_inv_rev, inv_inv, mul_comm]
      _ = τ (c : U) * (c : U)⁻¹ := hinv _
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ⊓ fixedBy τ ≤ C)).toEquiv] at h1
  have h2 : Nat.card φ.range ≤ Nat.card ↥(C ⊓ fixedBy τ) := Subgroup.card_le_of_le hrange
  rw [← h1, sq]
  exact Nat.mul_le_mul_left _ h2

end Sq

end CFSG.QuasithinUnique.L246.C123

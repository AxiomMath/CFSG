module

public import CFSG.GH74.GLS.C3.Layer1.Thm1A7T
public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Aux
public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Rec
public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Core

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1G33 CFSG.GH74.GLS.C3.Layer1.Thm1G35
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1A7

section Helpers

variable {G : Type} [Group G]

theorem exists_involution_pow [Finite G] {g : G} (hg2 : ∃ k : ℕ, g ^ (2 ^ k) = 1) (hg1 : g ≠ 1) :
    ∃ m : ℕ, orderOf (g ^ m) = 2 := by
  obtain ⟨k, hk⟩ := hg2
  have hdvd : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hjo
    exact hg1 (orderOf_eq_one_iff.1 hjo)
  refine ⟨orderOf g / 2, ?_⟩
  have h2 : 2 ∣ orderOf g := by
    rw [hjo]
    exact dvd_pow_self 2 hj0
  have hpos : 0 < orderOf g / 2 := by
    have := orderOf_pos g
    have := Nat.le_of_dvd this h2
    omega
  rw [orderOf_pow_of_dvd hpos.ne' (Nat.div_dvd_of_dvd h2)]
  exact Nat.div_div_self h2 (orderOf_pos g).ne'

theorem mem_map_conj_iff {H : Subgroup G} {g w : G} :
    w ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * w * g ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom h) * g = h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hh
  · intro hw
    refine ⟨g⁻¹ * w * g, hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem z_mem_of_normal [Finite G] {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) {z : G}
    (hzu : ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z) {N : Subgroup G} (hNP : N ≤ P)
    (hNn : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) (hN1 : ∃ n ∈ N, n ≠ 1) : z ∈ N := by
  have : Group.IsNilpotent ↥P := hP2.isNilpotent
  set N' : Subgroup ↥P := N.subgroupOf P with hN'
  have : N'.Normal := ⟨fun n hn g => hNn g g.2 n hn⟩
  have hne : N' ≠ ⊥ := by
    obtain ⟨n, hn, hn1⟩ := hN1
    intro h
    have : (⟨n, hNP hn⟩ : ↥P) ∈ N' := hn
    rw [h, Subgroup.mem_bot] at this
    exact hn1 (congrArg Subtype.val this)
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hinf
  have hcN : (c : ↥P) ∈ N' := (c.2).1
  have hcZ : (c : ↥P) ∈ Subgroup.center ↥P := (c.2).2
  have hcG : (c : P).1 ∈ N := hcN
  have hcc : ∀ p ∈ P, (c : P).1 * p = p * (c : P).1 := by
    intro p hp
    have := Subgroup.mem_center_iff.1 hcZ ⟨p, hp⟩
    exact congrArg Subtype.val this.symm
  rcases hzu _ (c : P).2 hcc with h | h
  · exfalso
    apply hc1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · rw [← h]
    exact hcG

end Helpers

section D8Facts

theorem d8_pow_four : ∀ u : D8, u ^ 4 = 1 := by decide

theorem d8_center : ∀ u : D8, (∀ v : D8, u * v = v * u) → u = 1 ∨ u = DihedralGroup.r 2 := by decide

end D8Facts

section ArgA

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem A7Env.exists_eP (E : A7Env x y K T f z) : Nonempty (↥(T ⊓ K) ≃* D8) := by
  obtain ⟨n, hn3, hn⟩ := E.hdih
  obtain ⟨-, k, hk, -, ⟨e⟩⟩ := hn
  have hcard := E.card_P
  have h2k : Nat.card ↥(T ⊓ K) = 2 * k := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hk4 : k = 4 := by omega
  subst hk4
  exact ⟨e⟩

theorem A7Env.hzT (E : A7Env x y K T f z) : ∀ t ∈ T, z * t = t * z := by
  intro t ht
  rcases E.T_decomp t ht with ⟨p, hp, q, hq, rfl⟩ | ⟨p, hp, q, hq, rfl⟩
  · have h1 : z * p = p * z := E.hzc p hp
    have h2 : q * z = z * q := E.hQcentP q hq z E.hzP
    calc z * (p * q) = (z * p) * q := by group
      _ = (p * z) * q := by rw [h1]
      _ = p * (z * q) := by group
      _ = p * (q * z) := by rw [h2]
      _ = p * q * z := by group
  · have h1 : z * p = p * z := E.hzc p hp
    have h2 : q * z = z * q := E.hQcentP q hq z E.hzP
    have h3 : f * z = z * f := E.hfc z E.hzP
    calc z * (p * q * f) = (z * p) * q * f := by group
      _ = (p * z) * q * f := by rw [h1]
      _ = p * (z * q) * f := by group
      _ = p * (q * z) * f := by rw [h2]
      _ = p * q * (z * f) := by group
      _ = p * q * (f * z) := by rw [h3]
      _ = p * q * f * z := by group

theorem A7Env.hfQ (E : A7Env x y K T f z) :
    ∀ q ∈ T ⊓ CxK x K, f * q * f ∈ T ⊓ CxK x K := by
  intro q hq
  have := E.hQnorm f E.hfT q hq
  have e1 : f⁻¹ = f := inv_eq_of_mul_eq_one_right E.hf2'
  rwa [e1] at this

def A7Env.InC (E : A7Env x y K T f z) (c : G) : Prop :=
  c ∈ T ⊓ CxK x K ∨ ∃ q ∈ T ⊓ CxK x K, c = q * f

theorem A7Env.InC_mul (E : A7Env x y K T f z) {c c' : G} (hc : E.InC c) (hc' : E.InC c') :
    E.InC (c * c') := by
  have hff := E.hf2'
  rcases hc with hc | ⟨q, hq, rfl⟩ <;> rcases hc' with hc' | ⟨q', hq', rfl⟩
  · exact Or.inl ((T ⊓ CxK x K).mul_mem hc hc')
  · exact Or.inr ⟨c * q', (T ⊓ CxK x K).mul_mem hc hq', by group⟩
  · refine Or.inr ⟨q * (f * c' * f), (T ⊓ CxK x K).mul_mem hq (E.hfQ c' hc'), ?_⟩
    calc q * f * c' = q * f * c' * (f * f) := by rw [hff, mul_one]
      _ = q * (f * c' * f) * f := by group
  · refine Or.inl ?_
    have h1 : q * f * (q' * f) = q * (f * q' * f) := by group
    rw [h1]
    exact (T ⊓ CxK x K).mul_mem hq (E.hfQ q' hq')

theorem A7Env.InC_inv (E : A7Env x y K T f z) {c : G} (hc : E.InC c) : E.InC c⁻¹ := by
  have hff := E.hf2'
  rcases hc with hc | ⟨q, hq, rfl⟩
  · exact Or.inl ((T ⊓ CxK x K).inv_mem hc)
  · refine Or.inr ⟨f * q⁻¹ * f, E.hfQ q⁻¹ ((T ⊓ CxK x K).inv_mem hq), ?_⟩
    have e1 : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
    calc (q * f)⁻¹ = f⁻¹ * q⁻¹ := by group
      _ = f * q⁻¹ := by rw [e1]
      _ = f * q⁻¹ * (f * f) := by rw [hff, mul_one]
      _ = f * q⁻¹ * f * f := by group

theorem A7Env.InC_T (E : A7Env x y K T f z) {c : G} (hc : E.InC c) : c ∈ T := by
  rcases hc with hc | ⟨q, hq, rfl⟩
  · exact hc.1
  · exact T.mul_mem hq.1 E.hfT

theorem A7Env.InC_cent (E : A7Env x y K T f z) {c : G} (hc : E.InC c) :
    ∀ p ∈ T ⊓ K, c * p = p * c := by
  intro p hp
  rcases hc with hc | ⟨q, hq, rfl⟩
  · exact E.hQcentP c hc p hp
  · have h1 : q * p = p * q := E.hQcentP q hq p hp
    have h2 : f * p = p * f := E.hfc p hp
    calc q * f * p = q * (f * p) := by group
      _ = q * (p * f) := by rw [h2]
      _ = (q * p) * f := by group
      _ = (p * q) * f := by rw [h1]
      _ = p * (q * f) := by group

theorem A7Env.hPC (E : A7Env x y K T f z) : ∀ p ∈ T ⊓ K, E.InC p → p = 1 := by
  intro p hp hc
  rcases hc with hc | ⟨q, hq, hpq⟩
  · have : p ∈ (T ⊓ K) ⊓ (T ⊓ CxK x K) := ⟨hp, hc⟩
    rw [E.hPQ, Subgroup.mem_bot] at this
    exact this
  · exfalso
    apply E.hfout
    have hf : f = q⁻¹ * p := by rw [hpq]; group
    have hpC : p ∈ centralizer ({x} : Set G) := E.hTC hp.1
    have hqC : q ∈ centralizer ({x} : Set G) := E.hTC hq.1
    have hφq : Back.actHom E.hKN ⟨q, hqC⟩ = 1 := by
      have : (⟨q, hqC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := by
        rw [Back.actHom_ker E.hKN]
        exact hq.2
      exact this
    have h1 : (⟨f, E.hsetup.sylowT.le E.hfT⟩ : ↥(centralizer ({x} : Set G))) =
        (⟨q, hqC⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨p, hpC⟩ := Subtype.ext hf
    rw [h1, map_mul, map_inv, hφq, inv_one, one_mul,
      Back.actHom_of_mem E.hKN hp.2 hpC]
    exact ⟨_, rfl⟩

theorem A7Env.T_PC (E : A7Env x y K T f z) :
    ∀ t ∈ T, ∃ p ∈ T ⊓ K, ∃ c, E.InC c ∧ t = p * c := by
  intro t ht
  rcases E.T_decomp t ht with ⟨p, hp, q, hq, rfl⟩ | ⟨p, hp, q, hq, rfl⟩
  · exact ⟨p, hp, q, Or.inl hq, rfl⟩
  · exact ⟨p, hp, q * f, Or.inr ⟨q, hq, rfl⟩, mul_assoc p q f⟩

theorem A7Env.InC_sq (E : A7Env x y K T f z) {c : G} (hc : E.InC c) : c * c ∈ T ⊓ CxK x K := by
  rcases hc with hc | ⟨q, hq, rfl⟩
  · exact (T ⊓ CxK x K).mul_mem hc hc
  · have hff := E.hf2'
    have : q * f * (q * f) = q * (f * q * f) := by group
    rw [this]
    exact (T ⊓ CxK x K).mul_mem hq (E.hfQ q hq)

theorem A7Env.hT4 (E : A7Env x y K T f z) : ∀ t ∈ T, t ^ 4 ∈ T ⊓ CxK x K := by
  intro t ht
  obtain ⟨p, hp, c, hc, rfl⟩ := E.T_PC t ht
  have hpc : c * p = p * c := E.InC_cent hc p hp
  have hP4 : p ^ 4 = 1 := by
    obtain ⟨e⟩ := E.exists_eP
    have h1 : e ⟨p, hp⟩ ^ 4 = 1 := d8_pow_four _
    have h2 : (⟨p, hp⟩ : ↥(T ⊓ K)) ^ 4 = 1 := e.injective (by rw [map_pow, h1, map_one])
    exact congrArg Subtype.val h2
  have : (p * c) ^ 4 = p ^ 4 * c ^ 4 := (Commute.mul_pow (show Commute p c from hpc.symm) 4)
  rw [this, hP4, one_mul]
  have h4 : c ^ 4 = (c * c) * (c * c) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [h4]
  exact (T ⊓ CxK x K).mul_mem (E.InC_sq hc) (E.InC_sq hc)

end ArgA

section ArgB

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem A7Env.hsqCTP (E : A7Env x y K T f z) :
    ∀ t ∈ T, (∀ p ∈ T ⊓ K, t * p = p * t) → t * t ∈ T ⊓ CxK x K := by
  intro t ht hc
  obtain ⟨p, hp, c, hcC, rfl⟩ := E.T_PC t ht
  have hpcentral : ∀ p' ∈ T ⊓ K, p * p' = p' * p := by
    intro p' hp'
    have h1 := hc p' hp'
    have h2 : c * p' = p' * c := E.InC_cent hcC p' hp'
    have : p * p' * c = p' * p * c := by
      calc p * p' * c = p * (p' * c) := by group
        _ = p * (c * p') := by rw [h2]
        _ = p * c * p' := by group
        _ = p' * (p * c) := h1
        _ = p' * p * c := by group
    exact mul_right_cancel this
  rcases E.hzu p hp hpcentral with h | h
  · rw [h, one_mul]
    exact E.InC_sq hcC
  · rw [h]
    have hzc : z * c = c * z := E.hzT c (E.InC_T hcC)
    have h3 : z * c * (z * c) = c * c := by
      calc z * c * (z * c) = z * (c * z) * c := by group
        _ = z * (z * c) * c := by rw [hzc]
        _ = (z * z) * (c * c) := by group
        _ = c * c := by rw [E.hz2', one_mul]
    rw [h3]
    exact E.InC_sq hcC

theorem A7Env.hQcapQa (E : A7Env x y K T f z) {a : G} (hxa : a * x * a⁻¹ ≠ x) :
    ∀ w ∈ T ⊓ CxK x K, a⁻¹ * w * a ∈ T ⊓ CxK x K → w = 1 := by
  intro w hw hwa
  by_contra hw1
  have hw2 : ∃ k : ℕ, w ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.hsetup.sylowT.isPGroup ⟨w, hw.1⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨m, hm⟩ := exists_involution_pow hw2 hw1
  have hwm : w ^ m ∈ T ⊓ CxK x K := Subgroup.pow_mem _ hw m
  have hconj : a⁻¹ * w ^ m * a = (a⁻¹ * w * a) ^ m := by
    have := conj_pow (a := a⁻¹) (b := w) (i := m)
    simpa using this.symm
  have hwma : a⁻¹ * w ^ m * a ∈ T ⊓ CxK x K := by
    rw [hconj]
    exact Subgroup.pow_mem _ hwa m
  have hsq : w ^ m * w ^ m = 1 := by
    have := pow_orderOf_eq_one (w ^ m)
    rwa [hm, sq] at this
  have hne1 : w ^ m ≠ 1 := fun h => by rw [h, orderOf_one] at hm; omega
  have hwx : w ^ m = x := (E.hQ_unique (w ^ m) hwm hsq).resolve_left hne1
  have hsq' : (a⁻¹ * w ^ m * a) * (a⁻¹ * w ^ m * a) = 1 := by
    calc (a⁻¹ * w ^ m * a) * (a⁻¹ * w ^ m * a) = a⁻¹ * (w ^ m * w ^ m) * a := by group
      _ = 1 := by rw [hsq]; group
  rcases E.hQ_unique _ hwma hsq' with h | h
  · apply E.hx1
    rw [hwx] at h
    calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rw [hwx] at h
    apply hxa
    have h' : a * x = x * a := by
      calc a * x = a * (a⁻¹ * x * a) := by rw [h]
        _ = x * a := by group
    calc a * x * a⁻¹ = x * a * a⁻¹ := by rw [h']
      _ = x := by group

theorem A7Env.hQa_unique (E : A7Env x y K T f z) {a : G} :
    ∀ w, a⁻¹ * w * a ∈ T ⊓ CxK x K → w * w = 1 → w = 1 ∨ w = a * x * a⁻¹ := by
  intro w hw hww
  have hsq' : (a⁻¹ * w * a) * (a⁻¹ * w * a) = 1 := by
    calc (a⁻¹ * w * a) * (a⁻¹ * w * a) = a⁻¹ * (w * w) * a := by group
      _ = 1 := by rw [hww]; group
  rcases E.hQ_unique _ hw hsq' with h | h
  · left
    calc w = a * (a⁻¹ * w * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc w = a * (a⁻¹ * w * a) * a⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [h]

theorem A7Env.hQa_norm (E : A7Env x y K T f z) {a : G} (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) :
    ∀ t ∈ T, ∀ w, a⁻¹ * w * a ∈ T ⊓ CxK x K →
      a⁻¹ * (t * w * t⁻¹) * a ∈ T ⊓ CxK x K := by
  intro t ht w hw
  have : a⁻¹ * (t * w * t⁻¹) * a = (a⁻¹ * t * a) * (a⁻¹ * w * a) * (a⁻¹ * t * a)⁻¹ := by group
  rw [this]
  exact E.hQnorm _ (haN2 t ht) _ hw

theorem A7Env.hPa_norm (E : A7Env x y K T f z) {a : G} (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) :
    ∀ t ∈ T, ∀ w, a⁻¹ * w * a ∈ T ⊓ K → a⁻¹ * (t * w * t⁻¹) * a ∈ T ⊓ K := by
  intro t ht w hw
  have : a⁻¹ * (t * w * t⁻¹) * a = (a⁻¹ * t * a) * (a⁻¹ * w * a) * (a⁻¹ * t * a)⁻¹ := by group
  rw [this]
  exact E.hPnorm _ (haN2 t ht) _ hw

theorem A7Env.hQa_T {a : G} (E : A7Env x y K T f z) (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T) {w : G}
    (hw : a⁻¹ * w * a ∈ T ⊓ CxK x K) : w ∈ T := by
  have := haN1 _ hw.1
  have e1 : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
  rwa [e1] at this

theorem A7Env.hPa_T {a : G} (E : A7Env x y K T f z) (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T) {w : G}
    (hw : a⁻¹ * w * a ∈ T ⊓ K) : w ∈ T := by
  have := haN1 _ hw.1
  have e1 : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
  rwa [e1] at this

end ArgB

section ArgC

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem A7Env.hz_Qa (E : A7Env x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) : a⁻¹ * z * a ∈ T ⊓ CxK x K := by
  classical
  by_contra hzQa
  have hP2 : IsPGroup 2 ↥(T ⊓ K) := E.hPK.isPGroup
  have hcap : ∀ w ∈ T ⊓ K, a⁻¹ * w * a ∈ T ⊓ CxK x K → w = 1 := by
    intro w hw hwa
    by_contra hw1
    set N : Subgroup G := (T ⊓ K) ⊓ (T ⊓ CxK x K).map (MulAut.conj a).toMonoidHom with hN
    have hNP : N ≤ T ⊓ K := inf_le_left
    have hNn : ∀ p ∈ T ⊓ K, ∀ n ∈ N, p * n * p⁻¹ ∈ N := by
      intro p hp n hn
      have hn' := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨E.hPnorm p hp.1 n hn'.1, ?_⟩
      exact mem_map_conj_iff.2 (E.hQa_norm haN2 p hp.1 n (mem_map_conj_iff.1 hn'.2))
    have hzN : z ∈ N := z_mem_of_normal hP2 E.hzu hNP hNn
      ⟨w, Subgroup.mem_inf.2 ⟨hw, mem_map_conj_iff.2 hwa⟩, hw1⟩
    exact hzQa (mem_map_conj_iff.1 (Subgroup.mem_inf.1 hzN).2)
  have hcomm : ∀ w, a⁻¹ * w * a ∈ T ⊓ CxK x K → ∀ p ∈ T ⊓ K, w * p = p * w := by
    intro w hw p hp
    have hwT : w ∈ T := E.hQa_T haN1 hw
    have hwinv : a⁻¹ * w⁻¹ * a ∈ T ⊓ CxK x K := by
      have : a⁻¹ * w⁻¹ * a = (a⁻¹ * w * a)⁻¹ := by group
      rw [this]
      exact (T ⊓ CxK x K).inv_mem hw
    have h1 : a⁻¹ * (p * w⁻¹ * p⁻¹) * a ∈ T ⊓ CxK x K := E.hQa_norm haN2 p hp.1 w⁻¹ hwinv
    have hcQa : a⁻¹ * (w * p * w⁻¹ * p⁻¹) * a ∈ T ⊓ CxK x K := by
      have : a⁻¹ * (w * p * w⁻¹ * p⁻¹) * a =
          (a⁻¹ * w * a) * (a⁻¹ * (p * w⁻¹ * p⁻¹) * a) := by group
      rw [this]
      exact (T ⊓ CxK x K).mul_mem hw h1
    have hcP : w * p * w⁻¹ * p⁻¹ ∈ T ⊓ K := by
      have := (T ⊓ K).mul_mem (E.hPnorm w hwT p hp) ((T ⊓ K).inv_mem hp)
      simpa [mul_assoc] using this
    have := hcap _ hcP hcQa
    calc w * p = (w * p * w⁻¹ * p⁻¹) * (p * w) := by group
      _ = p * w := by rw [this, one_mul]
  have hsq : ∀ w, a⁻¹ * w * a ∈ T ⊓ CxK x K → w * w = 1 := by
    intro w hw
    have hwT : w ∈ T := E.hQa_T haN1 hw
    have hsqQ : w * w ∈ T ⊓ CxK x K := E.hsqCTP w hwT (hcomm w hw)
    have hsqQa : a⁻¹ * (w * w) * a ∈ T ⊓ CxK x K := by
      have : a⁻¹ * (w * w) * a = (a⁻¹ * w * a) * (a⁻¹ * w * a) := by group
      rw [this]
      exact (T ⊓ CxK x K).mul_mem hw hw
    exact E.hQcapQa hxa _ hsqQ hsqQa
  have hQ2 : Nat.card ↥(T ⊓ CxK x K) ≤ 2 := by
    have hle : T ⊓ CxK x K ≤ zpowers x := by
      intro q hq
      have hw : a⁻¹ * (a * q * a⁻¹) * a ∈ T ⊓ CxK x K := by
        have : a⁻¹ * (a * q * a⁻¹) * a = q := by group
        rw [this]
        exact hq
      rcases E.hQa_unique (a := a) _ hw (hsq _ hw) with h | h
      · have : q = 1 := by
          calc q = a⁻¹ * (a * q * a⁻¹) * a := by group
            _ = 1 := by rw [h]; group
        rw [this]
        exact (zpowers x).one_mem
      · have : q = x := by
          calc q = a⁻¹ * (a * q * a⁻¹) * a := by group
            _ = a⁻¹ * (a * x * a⁻¹) * a := by rw [h]
            _ = x := by group
        rw [this]
        exact mem_zpowers x
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, E.hu2.1.1.1] at this
  omega

theorem A7Env.hza (E : A7Env x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) : a * x * a⁻¹ = z := by
  have hz := E.hz_Qa haN1 haN2 hxa hQ3
  have hsq' : (a⁻¹ * z * a) * (a⁻¹ * z * a) = 1 := by
    calc (a⁻¹ * z * a) * (a⁻¹ * z * a) = a⁻¹ * (z * z) * a := by group
      _ = 1 := by rw [E.hz2']; group
  rcases E.hQ_unique _ hz hsq' with h | h
  · exfalso
    apply E.hz1
    calc z = a * (a⁻¹ * z * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  · calc a * x * a⁻¹ = a * (a⁻¹ * z * a) * a⁻¹ := by rw [h]
      _ = z := by group

theorem A7Env.haz (E : A7Env x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) (ha2 : a * a ∈ T) : a * z * a⁻¹ = x := by
  rw [← E.hza haN1 haN2 hxa hQ3]
  have h1 : (a * a) * x = x * (a * a) := mem_centralizer_singleton_iff.1 (E.hTC ha2)
  calc a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
    _ = x * (a * a) * (a * a)⁻¹ := by rw [h1]
    _ = x := by group

theorem A7Env.hPPa (E : A7Env x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) :
    ∀ w ∈ T ⊓ K, a⁻¹ * w * a ∈ T ⊓ K → w = 1 := by
  classical
  intro w hw hwa
  by_contra hw1
  have hP2 : IsPGroup 2 ↥(T ⊓ K) := E.hPK.isPGroup
  set N : Subgroup G := (T ⊓ K) ⊓ (T ⊓ K).map (MulAut.conj a).toMonoidHom with hN
  have hNP : N ≤ T ⊓ K := inf_le_left
  have hNn : ∀ p ∈ T ⊓ K, ∀ n ∈ N, p * n * p⁻¹ ∈ N := by
    intro p hp n hn
    have hn' := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨E.hPnorm p hp.1 n hn'.1, ?_⟩
    exact mem_map_conj_iff.2 (E.hPa_norm haN2 p hp.1 n (mem_map_conj_iff.1 hn'.2))
  have hzN : z ∈ N := z_mem_of_normal hP2 E.hzu hNP hNn
    ⟨w, Subgroup.mem_inf.2 ⟨hw, mem_map_conj_iff.2 hwa⟩, hw1⟩
  have hzP : a⁻¹ * z * a ∈ T ⊓ K := mem_map_conj_iff.1 (Subgroup.mem_inf.1 hzN).2
  have hzQ : a⁻¹ * z * a ∈ T ⊓ CxK x K := E.hz_Qa haN1 haN2 hxa hQ3
  have : a⁻¹ * z * a ∈ (T ⊓ K) ⊓ (T ⊓ CxK x K) := ⟨hzP, hzQ⟩
  rw [E.hPQ, Subgroup.mem_bot] at this
  apply E.hz1
  calc z = a * (a⁻¹ * z * a) * a⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem A7Env.hcommPPa (E : A7Env x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) :
    ∀ p ∈ T ⊓ K, ∀ w, a⁻¹ * w * a ∈ T ⊓ K → p * w = w * p := by
  intro p hp w hw
  have hwT : w ∈ T := E.hPa_T haN1 hw
  have hwinv : a⁻¹ * w⁻¹ * a ∈ T ⊓ K := by
    have : a⁻¹ * w⁻¹ * a = (a⁻¹ * w * a)⁻¹ := by group
    rw [this]
    exact (T ⊓ K).inv_mem hw
  have h1 : a⁻¹ * (p * w⁻¹ * p⁻¹) * a ∈ T ⊓ K := E.hPa_norm haN2 p hp.1 w⁻¹ hwinv
  have hcPa : a⁻¹ * (p * w * p⁻¹ * w⁻¹) * a ∈ T ⊓ K := by
    have : a⁻¹ * (p * w * p⁻¹ * w⁻¹) * a =
        (a⁻¹ * (p * w * p⁻¹) * a) * (a⁻¹ * w * a)⁻¹ := by group
    rw [this]
    exact (T ⊓ K).mul_mem (E.hPa_norm haN2 p hp.1 w hw) ((T ⊓ K).inv_mem hw)
  have hcP : p * w * p⁻¹ * w⁻¹ ∈ T ⊓ K := by
    have h2 := (T ⊓ K).mul_mem hp (E.hPnorm w hwT p⁻¹ ((T ⊓ K).inv_mem hp))
    have e1 : p * (w * p⁻¹ * w⁻¹) = p * w * p⁻¹ * w⁻¹ := by group
    rwa [e1] at h2
  have := E.hPPa haN1 haN2 hxa hQ3 _ hcP hcPa
  calc p * w = (p * w * p⁻¹ * w⁻¹) * (w * p) := by group
    _ = w * p := by rw [this, one_mul]

end ArgC

section ArgD

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem A7Env.hz_e (E : A7Env x y K T f z) (e : ↥(T ⊓ K) ≃* D8) :
    e ⟨z, E.hzP⟩ = DihedralGroup.r 2 := by
  have hcent : ∀ v : D8, e ⟨z, E.hzP⟩ * v = v * e ⟨z, E.hzP⟩ := by
    intro v
    obtain ⟨p, rfl⟩ := e.surjective v
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (E.hzc p.1 p.2)
  rcases d8_center _ hcent with h | h
  · exfalso
    have : (⟨z, E.hzP⟩ : ↥(T ⊓ K)) = 1 := e.injective (by rw [h, map_one])
    exact E.hz1 (congrArg Subtype.val this)
  · exact h

theorem A7Env.hQcard4 (E : A7Env x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) : Nat.card ↥(T ⊓ CxK x K) = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := E.exists_eP
  have hz_e := E.hz_e e
  have hza := E.hza haN1 haN2 hxa hQ3
  set Qa : Subgroup G := (T ⊓ CxK x K).map (MulAut.conj a).toMonoidHom with hQa
  have hQacard : Nat.card ↥Qa = Nat.card ↥(T ⊓ CxK x K) :=
    Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hQaT : ∀ w ∈ Qa, w ∈ T := fun w hw => E.hQa_T haN1 (mem_map_conj_iff.1 hw)
  have hproj : ∀ w ∈ Qa, ∃ p ∈ T ⊓ K, ∃ c, E.InC c ∧ w = p * c := fun w hw =>
    E.T_PC w (hQaT w hw)
  choose! π hπP c hcC hwπ using hproj
  have hexp : ∀ w ∈ Qa, w ^ 4 = 1 := by
    intro w hw
    have h1 : w ^ 4 ∈ T ⊓ CxK x K := E.hT4 w (hQaT w hw)
    have h2 : w ^ 4 ∈ Qa := Subgroup.pow_mem _ hw 4
    exact E.hQcapQa hxa _ h1 (mem_map_conj_iff.1 h2)
  have hinv : ∀ w ∈ Qa, w * w = 1 → w = 1 ∨ w = z := by
    intro w hw hww
    rcases E.hQa_unique (a := a) w (mem_map_conj_iff.1 hw) hww with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hza)
  have hπmem : ∀ w ∈ Qa, π w = 1 ∨ π w = z ∨ π w * π w = z := by
    intro w hw
    obtain ⟨p, c', hpP', hcC', hwpc, hpdef⟩ : ∃ p c', p ∈ T ⊓ K ∧ E.InC c' ∧ w = p * c' ∧ π w = p :=
      ⟨π w, c w, hπP w hw, hcC w hw, hwπ w hw, rfl⟩
    rw [hpdef]
    have hpc : c' * p = p * c' := E.InC_cent hcC' p hpP'
    by_cases hww : w * w = 1
    · rcases hinv w hw hww with h | h
      · left
        have hp1 : p = c'⁻¹ := by
          have : p * c' = 1 := by rw [← hwpc]; exact h
          exact eq_inv_of_mul_eq_one_left this
        exact E.hPC _ hpP' (by rw [hp1]; exact E.InC_inv hcC')
      · right; left
        have hcPc : c' = p⁻¹ * z := by
          calc c' = p⁻¹ * (p * c') := by group
            _ = p⁻¹ * z := by rw [← hwpc, h]
        have hcP : c' ∈ T ⊓ K := by
          rw [hcPc]
          exact (T ⊓ K).mul_mem ((T ⊓ K).inv_mem hpP') E.hzP
        have hc1 : c' = 1 := E.hPC _ hcP hcC'
        rw [hc1, mul_one] at hwpc
        rw [← hwpc, h]
    · right; right
      have hw2 : w * w ∈ Qa := (Qa).mul_mem hw hw
      have hw4 : (w * w) * (w * w) = 1 := by
        have := hexp w hw
        calc (w * w) * (w * w) = w ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = 1 := this
      have hwwz : w * w = z := by
        rcases hinv _ hw2 hw4 with h | h
        · exact absurd h hww
        · exact h
      have hsq : p * p * (c' * c') = z := by
        calc p * p * (c' * c') = (p * c') * (p * c') := by
              calc p * p * (c' * c') = p * (p * c') * c' := by group
                _ = p * (c' * p) * c' := by rw [hpc]
                _ = (p * c') * (p * c') := by group
          _ = w * w := by rw [← hwpc]
          _ = z := hwwz
      have hcc : c' * c' ∈ T ⊓ K := by
        have : c' * c' = (p * p)⁻¹ * z := by
          calc c' * c' = (p * p)⁻¹ * (p * p * (c' * c')) := by group
            _ = (p * p)⁻¹ * z := by rw [hsq]
        rw [this]
        exact (T ⊓ K).mul_mem ((T ⊓ K).inv_mem ((T ⊓ K).mul_mem hpP' hpP')) E.hzP
      have hcc1 : c' * c' = 1 := E.hPC _ hcc (E.InC_mul hcC' hcC')
      rw [hcc1, mul_one] at hsq
      exact hsq
  have hπinj : ∀ w ∈ Qa, ∀ w' ∈ Qa, π w = π w' → w = w' := by
    intro w hw w' hw' hpp
    have hwc := hwπ w hw
    have hwc' := hwπ w' hw'
    have hu : w⁻¹ * w' = (c w)⁻¹ * c w' := by
      calc w⁻¹ * w' = (π w * c w)⁻¹ * (π w' * c w') := by rw [← hwc, ← hwc']
        _ = (c w)⁻¹ * (π w)⁻¹ * (π w' * c w') := by group
        _ = (c w)⁻¹ * c w' := by rw [← hpp]; group
    have hInC : E.InC (w⁻¹ * w') := by
      rw [hu]
      exact E.InC_mul (E.InC_inv (hcC w hw)) (hcC w' hw')
    have hQu : w⁻¹ * w' ∈ Qa := (Qa).mul_mem ((Qa).inv_mem hw) hw'
    by_contra hne
    have hne1 : w⁻¹ * w' ≠ 1 := fun h => hne (by
      calc w = w * (w⁻¹ * w') := by rw [h, mul_one]
        _ = w' := by group)
    by_cases hu2 : (w⁻¹ * w') * (w⁻¹ * w') = 1
    · have := hinv _ hQu hu2
      rcases this with h | h
      · exact hne1 h
      · rw [h] at hInC
        exact E.hz1 (E.hPC _ E.hzP hInC)
    · have hu4 := hexp _ hQu
      have hQu2 : (w⁻¹ * w') * (w⁻¹ * w') ∈ Qa := (Qa).mul_mem hQu hQu
      have hu44 : ((w⁻¹ * w') * (w⁻¹ * w')) * ((w⁻¹ * w') * (w⁻¹ * w')) = 1 := by
        calc ((w⁻¹ * w') * (w⁻¹ * w')) * ((w⁻¹ * w') * (w⁻¹ * w')) = (w⁻¹ * w') ^ 4 := by
              simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = 1 := hu4
      rcases hinv _ hQu2 hu44 with h | h
      · exact hu2 h
      · have := E.InC_mul hInC hInC
        rw [h] at this
        exact E.hz1 (E.hPC _ E.hzP this)
  set F : Finset D8 := Finset.univ.filter
    (fun u : D8 => u = 1 ∨ u = DihedralGroup.r 2 ∨ u * u = DihedralGroup.r 2) with hFdef
  have hF : F.card = 4 := by decide
  have hΦmem : ∀ w (hw : w ∈ Qa), e ⟨π w, hπP w hw⟩ ∈ F := by
    intro w hw
    rw [hFdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hπmem w hw with h | h | h
    · left
      have : (⟨π w, hπP w hw⟩ : ↥(T ⊓ K)) = 1 := Subtype.ext h
      rw [this, map_one]
    · right; left
      have : (⟨π w, hπP w hw⟩ : ↥(T ⊓ K)) = ⟨z, E.hzP⟩ := Subtype.ext h
      rw [this, hz_e]
    · right; right
      have : (⟨π w, hπP w hw⟩ : ↥(T ⊓ K)) * ⟨π w, hπP w hw⟩ = ⟨z, E.hzP⟩ := Subtype.ext h
      rw [← map_mul, this, hz_e]
  let Φ : ↥Qa → ↥F := fun w => ⟨e ⟨π w.1, hπP w.1 w.2⟩, hΦmem w.1 w.2⟩
  have hΦ : Function.Injective Φ := by
    intro w w' h
    have h1 : e ⟨π w.1, hπP w.1 w.2⟩ = e ⟨π w'.1, hπP w'.1 w'.2⟩ := congrArg Subtype.val h
    have h2 := e.injective h1
    exact Subtype.ext (hπinj w.1 w.2 w'.1 w'.2 (congrArg Subtype.val h2))
  have hcardle : Nat.card ↥Qa ≤ 4 := by
    have := Nat.card_le_card_of_injective Φ hΦ
    rwa [Nat.card_eq_fintype_card (α := ↥F), Fintype.card_coe, hF] at this
  rw [hQacard] at hcardle
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (E.hsetup.sylowT.isPGroup.to_le (inf_le_left : T ⊓ CxK x K ≤ T))
  rw [hn] at hQ3 hcardle ⊢
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn3 : n ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : n = 2 := by omega
  rw [this]
  norm_num

end ArgD

section ArgE

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem A7Env.hQcyc (E : A7Env x y K T f z) (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) :
    Nonempty (↥(T ⊓ CxK x K) ≃* Multiplicative (ZMod 4)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hex : ∃ g ∈ T ⊓ CxK x K, g ≠ 1 ∧ g ≠ x := by
    by_contra hcon
    push Not at hcon
    have hle : T ⊓ CxK x K ≤ zpowers x := by
      intro q hq
      by_cases hq1 : q = 1
      · rw [hq1]; exact (zpowers x).one_mem
      · rw [hcon q hq hq1]; exact mem_zpowers x
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, E.hu2.1.1.1] at this
    omega
  obtain ⟨g, hg, hg1, hgx⟩ := hex
  have hord : orderOf (⟨g, hg⟩ : ↥(T ⊓ CxK x K)) = 4 := by
    have hdvd : orderOf (⟨g, hg⟩ : ↥(T ⊓ CxK x K)) ∣ 4 := by
      rw [← hQ4]
      exact orderOf_dvd_natCard _
    have hne1 : orderOf (⟨g, hg⟩ : ↥(T ⊓ CxK x K)) ≠ 1 := by
      intro h
      apply hg1
      have := orderOf_eq_one_iff.1 h
      exact congrArg Subtype.val this
    have hne2 : orderOf (⟨g, hg⟩ : ↥(T ⊓ CxK x K)) ≠ 2 := by
      intro h2
      have hgg : g * g = 1 := by
        have := pow_orderOf_eq_one (⟨g, hg⟩ : ↥(T ⊓ CxK x K))
        rw [h2, sq] at this
        exact congrArg Subtype.val this
      rcases E.hQ_unique g hg hgg with h | h
      · exact hg1 h
      · exact hgx h
    have : orderOf (⟨g, hg⟩ : ↥(T ⊓ CxK x K)) ∈ Nat.divisors 4 :=
      Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have : IsCyclic ↥(T ⊓ CxK x K) := isCyclic_of_orderOf_eq_card _ (by rw [hord, hQ4])
  have hcardZ : Nat.card ↥(T ⊓ CxK x K) = Nat.card (Multiplicative (ZMod 4)) := by
    rw [hQ4, Nat.card_eq_fintype_card]
    decide
  exact ⟨mulEquivOfCyclicCardEq hcardZ⟩

theorem A7Env.card_T_le (E : A7Env x y K T f z) (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) :
    Nat.card ↥T ≤ 64 := by
  classical
  let φ : ↥(T ⊓ K) × ↥(T ⊓ CxK x K) × Bool → ↥T := fun pqb =>
    ⟨(pqb.1 : G) * (pqb.2.1 : G) * (if pqb.2.2 then f else 1),
      T.mul_mem (T.mul_mem pqb.1.2.1 pqb.2.1.2.1) (by split_ifs; exact E.hfT; exact T.one_mem)⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    rcases E.T_decomp t ht with ⟨p, hp, q, hq, rfl⟩ | ⟨p, hp, q, hq, rfl⟩
    · exact ⟨(⟨p, hp⟩, ⟨q, hq⟩, false), by simp [φ]⟩
    · exact ⟨(⟨p, hp⟩, ⟨q, hq⟩, true), by simp [φ]⟩
  have := Nat.card_le_card_of_surjective φ hsurj
  rw [Nat.card_prod, Nat.card_prod, E.card_P, hQ4, Nat.card_eq_fintype_card (α := Bool)] at this
  simpa using this

end ArgE

section ArgF

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem A7Env.exceptional_of (E : A7Env x y K T f z) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hTS : T < S) {a : G} (haS : a ∈ S) (haN : a ∈ normalizer (T : Set G)) (haT : a ∉ T)
    (ha2 : a ^ 2 ∈ T) (hxa : a * x * a⁻¹ ≠ x) (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) :
    IsExceptionalA7Triple x y K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨haN1, haN2⟩ := normalizer_conj_mem haN
  have haa : a * a ∈ T := by rw [← sq]; exact ha2
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  have hQ4 := E.hQcard4 haN1 haN2 hxa hQ3
  have hza := E.hza haN1 haN2 hxa hQ3
  have haz := E.haz haN1 haN2 hxa hQ3 haa
  set P : Subgroup G := T ⊓ K with hPdef
  set Pa : Subgroup G := P.map (MulAut.conj a).toMonoidHom with hPa
  obtain ⟨eP⟩ := E.exists_eP
  have hz_e := E.hz_e eP
  have hPaT : ∀ w ∈ Pa, w ∈ T := fun w hw => E.hPa_T haN1 (mem_map_conj_iff.1 hw)
  have hPacard : Nat.card ↥Pa = 8 := by
    rw [hPa, Subgroup.card_map_of_injective (MulAut.conj a).injective, E.card_P]
  have hinf : Pa ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact E.hPPa haN1 haN2 hxa hQ3 w hw.2 (mem_map_conj_iff.1 hw.1)
  have hcomm : ∀ d ∈ Pa, ∀ e ∈ P, d * e = e * d := fun d hd e he =>
    (E.hcommPPa haN1 haN2 hxa hQ3 e he d (mem_map_conj_iff.1 hd)).symm
  have hdec : ∀ v ∈ T, ∃ d ∈ Pa, ∃ e ∈ P, v = d * e := by
    let ψ : ↥Pa × ↥P → ↥T := fun de => ⟨(de.1 : G) * (de.2 : G), T.mul_mem (hPaT _ de.1.2) de.2.2.1⟩
    have hinj : Function.Injective ψ := by
      rintro ⟨⟨d, hd⟩, ⟨e, he⟩⟩ ⟨⟨d', hd'⟩, ⟨e', he'⟩⟩ h
      have h1 : d * e = d' * e' := congrArg Subtype.val h
      have h2 : d'⁻¹ * d = e' * e⁻¹ := by
        calc d'⁻¹ * d = d'⁻¹ * (d * e) * e⁻¹ := by group
          _ = d'⁻¹ * (d' * e') * e⁻¹ := by rw [h1]
          _ = e' * e⁻¹ := by group
      have h3 : d'⁻¹ * d ∈ Pa ⊓ P :=
        Subgroup.mem_inf.2 ⟨Pa.mul_mem (Pa.inv_mem hd') hd, h2 ▸ P.mul_mem he' (P.inv_mem he)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have hdd : d = d' := by
        have := congrArg (fun w : G => d' * w) h3
        simpa using this
      subst hdd
      have hee : e = e' := mul_left_cancel h1
      subst hee
      rfl
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [Nat.card_prod, hPacard, E.card_P]
      exact E.card_T_le hQ4)
    intro v hv
    obtain ⟨⟨d, e⟩, h⟩ := hbij.2 ⟨v, hv⟩
    exact ⟨d, d.2, e, e.2, (congrArg Subtype.val h).symm⟩
  have hD' : P = Pa.map (MulAut.conj a).toMonoidHom := by
    ext w
    rw [mem_map_conj_iff, mem_map_conj_iff]
    constructor
    · intro hw
      have h1 := E.hPnorm (a * a)⁻¹ (T.inv_mem haa) w hw
      have e1 : (a * a)⁻¹ * w * (a * a)⁻¹⁻¹ = a⁻¹ * (a⁻¹ * w * a) * a := by
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      rwa [e1] at h1
    · intro hw
      have h1 := E.hPnorm (a * a) haa _ hw
      have e1 : (a * a) * (a⁻¹ * (a⁻¹ * w * a) * a) * (a * a)⁻¹ = w := by
        simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
      rwa [e1] at h1
  have hDn : ∀ v ∈ T, ∀ d ∈ Pa, v * d * v⁻¹ ∈ Pa := by
    intro v hv d hd
    rw [mem_map_conj_iff]
    have h1 := E.hPnorm _ (haN2 v hv) _ (mem_map_conj_iff.1 hd)
    have e1 : a⁻¹ * (v * d * v⁻¹) * a = (a⁻¹ * v * a) * (a⁻¹ * d * a) * (a⁻¹ * v * a)⁻¹ := by group
    rw [e1]
    exact h1
  obtain ⟨w', hw', hbsq⟩ := exists_involution_coset (D := Pa) (D' := P) (V := T) (b₁ := a) hD' hDn
    haa hinf hcomm hdec
  set b : G := a * w'⁻¹ with hb
  have hw'T : w' ∈ T := hw'.1
  have hbT : b ∉ T := by
    intro h
    apply haT
    have := T.mul_mem h hw'T
    have e1 : b * w' = a := by rw [hb]; group
    rwa [e1] at this
  have hbS : b ∈ S := S.mul_mem haS (S.inv_mem (hTS.le hw'T))
  have hbconj : ∀ d ∈ Pa, b * d * b⁻¹ = a * d * a⁻¹ := by
    intro d hd
    have h1 := hcomm d hd w' hw'
    have hwd : w'⁻¹ * d * w' = d := by
      calc w'⁻¹ * d * w' = w'⁻¹ * (d * w') := by group
        _ = w'⁻¹ * (w' * d) := by rw [h1]
        _ = d := by group
    calc b * d * b⁻¹ = a * (w'⁻¹ * d * w') * a⁻¹ := by rw [hb]; group
      _ = a * d * a⁻¹ := by rw [hwd]
  let ι : D8 →* G := (MulAut.conj a).toMonoidHom.comp ((T ⊓ K).subtype.comp eP.symm.toMonoidHom)
  have hιu : ∀ u : D8, ι u = a * ((eP.symm u : ↥(T ⊓ K)) : G) * a⁻¹ := fun u => by
    simp [ι, MulAut.conj_apply]
  have hι : Function.Injective ι :=
    (MulAut.conj a).injective.comp ((T ⊓ K).subtype_injective.comp eP.symm.injective)
  have hmemPa : ∀ u : D8, ι u ∈ Pa := fun u => by
    rw [hιu]
    exact Subgroup.mem_map_of_mem _ (eP.symm u).2
  have hbP : ∀ v : D8, b * ι v * b⁻¹ ∈ P := by
    intro v
    rw [hbconj _ (hmemPa v), hD']
    exact Subgroup.mem_map_of_mem _ (hmemPa v)
  have hbmem : ∀ u v : D8, ι u * (b * ι v * b⁻¹) ∈ T := fun u v =>
    T.mul_mem (hPaT _ (hmemPa u)) (hbP v).1
  let d : WrData G := ⟨ι, b, hbsq, hι, fun u v => hcomm _ (hmemPa u) _ (hbP v), by
      intro u v h
      have h1 : ι u ∈ Pa ⊓ P := Subgroup.mem_inf.2 ⟨hmemPa u, h ▸ hbP v⟩
      rw [hinf, Subgroup.mem_bot] at h1
      exact hι (by rw [h1, map_one]),
    fun u v h => hbT (by rw [h]; exact hbmem u v)⟩
  have hΨ : Function.Injective d.Ψ := d.Ψ_injective
  have hΨS : ∀ m : M35, d.Ψ m ∈ S := by
    intro m
    rw [WrData.Ψ_apply]
    refine S.mul_mem ?_ ?_
    · rw [show m.left = (m.left.1, m.left.2) from rfl, WrData.fn_apply]
      exact hTS.le (hbmem _ _)
    · by_cases hq : m.right = 1
      · rw [hq, WrData.fg_one]
        exact S.one_mem
      · rw [WrData.fg_ne d hq]
        exact hbS
  have hVmap : Vsub.map d.Ψ = T := by
    have hle : Vsub.map d.Ψ ≤ T := by
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨u, v, rfl⟩ := exists_inl'_of_mem_Vsub hm
      rw [WrData.Ψ_inl']
      exact hbmem u v
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective hΨ, card_Vsub]
    exact E.card_T_le hQ4
  have hfΨ : d.Ψ (inl' (DihedralGroup.r 2) 1) = x := by
    rw [WrData.Ψ_inl']
    show ι (DihedralGroup.r 2) * (b * ι 1 * b⁻¹) = x
    rw [map_one, mul_one, mul_inv_cancel, mul_one, hιu]
    have : eP.symm (DihedralGroup.r 2) = ⟨z, E.hzP⟩ := (eP.symm_apply_eq).2 hz_e.symm
    rw [this]
    exact haz
  have hVsyl : IsSylowOf 2 (Vsub.map d.Ψ) (centralizer ({d.Ψ (inl' (DihedralGroup.r 2) 1)} : Set G)) := by
    rw [hVmap, hfΨ]
    exact E.hsetup.sylowT
  have hrange : d.Ψ.range = S := range_eq_of_sylow hΨ hS2 hΨS hVsyl
  have hSeq : S = T ⊔ zpowers a := by
    apply le_antisymm
    · rw [← hrange]
      rintro _ ⟨m, rfl⟩
      rw [WrData.Ψ_apply]
      refine Subgroup.mul_mem _ ?_ ?_
      · rw [show m.left = (m.left.1, m.left.2) from rfl, WrData.fn_apply]
        exact Subgroup.mem_sup_left (hbmem _ _)
      · by_cases hq : m.right = 1
        · rw [hq, WrData.fg_one]
          exact Subgroup.one_mem _
        · rw [WrData.fg_ne d hq]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers a))
            (Subgroup.mem_sup_left (T.inv_mem hw'T))
    · exact sup_le hTS.le ((zpowers_le).2 haS)
  have hCxN : ∀ c ∈ centralizer ({x} : Set G), ∀ q ∈ CxK x K, c * q * c⁻¹ ∈ CxK x K :=
    fun c hc q hq => P34Real.CMK_conj E.hKN hc hq
  have hQsyl : IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) :=
    E.hsetup.sylowT.inf_of_le_normalizer (fun q hq => hq.1)
      (fun c hc => U1a.mem_normalizer_of_norm hCxN hc)
  refine ⟨E.hu2, E.e7, T, S, a, E.hsetup.sylowT, E.hsetup.sylowT0, hQsyl, hS, hTS, haS, haN, haT,
    ha2, hSeq, ?_, ?_, ?_, ?_, E.hQcyc hQ4⟩
  · rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact E.hPPa haN1 haN2 hxa hQ3 w (Subgroup.mem_inf.1 hw).1
      (mem_map_conj_iff.1 (Subgroup.mem_inf.1 hw).2)
  · intro p hp q hq
    exact (hcomm q hq p hp).symm
  · apply le_antisymm
    · intro t ht
      obtain ⟨d', hd', e', he', rfl⟩ := hdec t ht
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hd') (Subgroup.mem_sup_left he')
    · exact sup_le inf_le_left (fun w hw => hPaT w hw)
  · exact E.exists_eP

end ArgF

end CFSG.GH74.GLS.C3.Layer1.Thm1A7

end

module

public import CFSG.ClassicalInvolution.Q3.Sec13EndSympForm
import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.Polar

variable {V : Type*} [CommGroup V]

private theorem polar_zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

private theorem polar_zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

private theorem polar_zmod2_eq_zero_of : ∀ a : ZMod 2, a = a + a → a = 0 := by decide

private theorem polar_zmod2_ne_one : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide

private theorem polar_zmod2_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

private theorem polar_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private theorem polar_one_add_eq_one : ∀ a : ZMod 2, 1 + a = 1 → a = 0 := by decide

private theorem polar_zero_eq_one_add : ∀ a : ZMod 2, 0 = 1 + a → 1 = a := by decide

private theorem polar_inv_eq (x : V) (hx : x * x = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right hx

private theorem polar_eq_of_eqOn {S : Set V} (hS : Subgroup.closure S = ⊤)
    (hsq : ∀ a : V, a * a = 1) {f g : V → ZMod 2}
    (hf : ∀ x y, f (x * y) = f x + f y) (hg : ∀ x y, g (x * y) = g x + g y)
    (h : ∀ a ∈ S, f a = g a) : ∀ x, f x = g x := by
  intro x
  have hx : x ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact h a ha
  | one =>
    have h1 := hf 1 1
    have h2 := hg 1 1
    rw [mul_one] at h1 h2
    exact (polar_zmod2_eq_zero_of _ h1).trans (polar_zmod2_eq_zero_of _ h2).symm
  | mul a b _ _ ha hb => rw [hf, hg, ha, hb]
  | inv a _ ha =>
    rw [polar_inv_eq a (hsq a)]
    exact ha

theorem exists_form_of_symmetric {S : Set V} (hS : Subgroup.closure S = ⊤)
    (hsq : ∀ a : V, a * a = 1) (β : V → V → ZMod 2)
    (hadd : ∀ a ∈ S, ∀ b b' : V, β a (b * b') = β a b + β a b')
    (hsymm : ∀ a ∈ S, ∀ b ∈ S, β a b = β b a) (halt : ∀ a ∈ S, β a a = 0) :
    ∃ B : V → V → ZMod 2, (∀ a a' b : V, B (a * a') b = B a b + B a' b) ∧
      (∀ a b b' : V, B a (b * b') = B a b + B a b') ∧ (∀ a : V, B a a = 0) ∧
      ∀ a ∈ S, ∀ b : V, B a b = β a b := by
  have hβ1 : ∀ a ∈ S, β a 1 = 0 := by
    intro a ha
    have h := hadd a ha 1 1
    rw [mul_one] at h
    exact polar_zmod2_eq_zero_of _ h
  have hex : ∀ d : V, ∃ φ : V → ZMod 2, (∀ x y, φ (x * y) = φ x + φ y) ∧
      ∀ a ∈ S, φ a = β a d := by
    intro d
    have hd : d ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top d
    induction hd using Subgroup.closure_induction with
    | mem a ha => exact ⟨fun x => β a x, hadd a ha, fun c hc => hsymm a ha c hc⟩
    | one => exact ⟨fun _ => 0, fun _ _ => by simp, fun a ha => (hβ1 a ha).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨φ, hφ, hφS⟩ := hx
      obtain ⟨ψ, hψ, hψS⟩ := hy
      refine ⟨fun z => φ z + ψ z, fun u v => ?_, fun a ha => ?_⟩
      · simp only [hφ, hψ]
        exact add_add_add_comm _ _ _ _
      · simp only [hφS a ha, hψS a ha]
        exact (hadd a ha x y).symm
    | inv x _ hx =>
      rw [polar_inv_eq x (hsq x)]
      exact hx
  choose φ hφ hφS using hex
  have hfirst : ∀ a a' b : V, φ (a * a') b = φ a b + φ a' b := by
    intro a a' b
    have key : ∀ x, φ (a * a') x = φ a x + φ a' x :=
      polar_eq_of_eqOn (f := fun x => φ (a * a') x) (g := fun x => φ a x + φ a' x) hS hsq
        (hφ (a * a'))
        (fun x y => by simp only [hφ a, hφ a']; exact add_add_add_comm _ _ _ _)
        (fun c hc => by
          simp only [hφS (a * a') c hc, hφS a c hc, hφS a' c hc]
          exact hadd c hc a a')
    exact key b
  have hφa : ∀ a ∈ S, ∀ b : V, φ a b = β a b := by
    intro a ha
    refine polar_eq_of_eqOn hS hsq (hφ a) (fun x y => hadd a ha x y) ?_
    intro c hc
    rw [hφS a c hc, hsymm c hc a ha]
  have hsymS : ∀ a ∈ S, ∀ b : V, φ a b = φ b a := by
    intro a ha b
    rw [hφa a ha b, hφS b a ha]
  have hsym : ∀ a b : V, φ a b = φ b a := by
    intro a b
    have ha : a ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top a
    induction ha using Subgroup.closure_induction with
    | mem c hc => exact hsymS c hc b
    | one =>
      have h1 := hfirst 1 1 b
      have h2 := hφ b 1 1
      rw [mul_one] at h1 h2
      rw [polar_zmod2_eq_zero_of _ h1, polar_zmod2_eq_zero_of _ h2]
    | mul x y _ _ hx hy => rw [hfirst x y b, hφ b x y, hx, hy]
    | inv x _ hx =>
      rw [polar_inv_eq x (hsq x)]
      exact hx
  have hdiag : ∀ a : V, φ a a = 0 := by
    intro a
    have ha : a ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top a
    induction ha using Subgroup.closure_induction with
    | mem c hc =>
      rw [hφa c hc c]
      exact halt c hc
    | one =>
      have h1 := hfirst 1 1 1
      rw [mul_one] at h1
      exact polar_zmod2_eq_zero_of _ h1
    | mul x y _ _ hx hy =>
      rw [hfirst x y (x * y), hφ x x y, hφ y x y, hx, hy, hsym y x, zero_add, add_zero]
      exact polar_zmod2_add_self _
    | inv x _ hx =>
      rw [polar_inv_eq x (hsq x)]
      exact hx
  exact ⟨fun a b => φ a b, hfirst, fun a b b' => hφ a b b', fun a => hdiag a,
    fun a ha b => hφa a ha b⟩

@[expose] def polarE (B : V → V → ZMod 2) (S : Set V) (p : V) : Subgroup V :=
  Subgroup.closure {x | x ∈ S ∧ B p x = 0}

structure PolarData (B : V → V → ZMod 2) (S : Set V) : Prop where
  one_notMem : (1 : V) ∉ S
  nonempty : S.Nonempty
  span : Subgroup.closure S = ⊤
  card_E : ∀ p ∈ S, Nat.card (polarE B S p) = 8
  mem_of_mem_E : ∀ p ∈ S, ∀ x ∈ polarE B S p, x ≠ 1 → x ∈ S
  not_isotropic : ∀ p ∈ S, ∃ x ∈ polarE B S p, ∃ y ∈ polarE B S p, B x y ≠ 0

private theorem polar_B_one_left {B : V → V → ZMod 2} (hB : SympForm B) (x : V) :
    B 1 x = 0 := by
  have h := hB.mul_left 1 1 x
  rw [mul_one] at h
  exact polar_zmod2_eq_zero_of _ h

private theorem polar_B_one_right {B : V → V → ZMod 2} (hB : SympForm B) (x : V) :
    B x 1 = 0 := by
  have h := hB.mul_right x 1 1
  rw [mul_one] at h
  exact polar_zmod2_eq_zero_of _ h

private theorem polar_zpowers_cases {g : V} (hg : g * g = 1) {y : V}
    (hy : y ∈ Subgroup.zpowers g) : y = 1 ∨ y = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  by_cases hg1 : g = 1
  · left
    rw [hg1, one_zpow]
  · have hord : orderOf g = 2 := orderOf_eq_prime (p := 2) (by rw [sq]; exact hg) hg1
    have hk := zpow_mod_orderOf g k
    rw [hord] at hk
    simp only [Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← hk, h, zpow_zero]
    · right
      rw [← hk, h, zpow_one]

private theorem polar_card_sup (H K : Subgroup V) (h : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup V) = Nat.card H * Nat.card K := by
  have h1 : K.relIndex (H ⊔ K) * Nat.card (K ⊓ (H ⊔ K) : Subgroup V)
      = Nat.card (H ⊔ K : Subgroup V) :=
    Subgroup.relIndex_mul_card (H := K) (K := H ⊔ K)
  have h2 : K.relIndex (H ⊔ K) = K.relIndex H := Subgroup.relIndex_sup_right (H := H) (K := K)
  have h3 : K.relIndex H * Nat.card (K ⊓ H : Subgroup V) = Nat.card H :=
    Subgroup.relIndex_mul_card (H := K) (K := H)
  rw [inf_eq_left.2 le_sup_right, h2] at h1
  rw [inf_comm, h, Subgroup.card_bot, mul_one] at h3
  rw [← h1, h3]

namespace PolarData

variable {B : V → V → ZMod 2} {S : Set V}

theorem polarE_perp (hB : SympForm B) (p : V) {x : V} (hx : x ∈ polarE B S p) : B p x = 0 := by
  unfold polarE at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact polar_B_one_right hB p
  | mul y z _ _ hy hz => rw [hB.mul_right, hy, hz, add_zero]
  | inv y _ hy =>
    rw [polar_inv_eq y (hB.sq_eq_one y)]
    exact hy

theorem self_mem_polarE (hB : SympForm B) {p : V} (hp : p ∈ S) : p ∈ polarE B S p := by
  unfold polarE
  exact Subgroup.subset_closure ⟨hp, hB.alt p⟩

theorem mul_mem_of_orth (hB : SympForm B) (hS : PolarData B S) {a b : V} (ha : a ∈ S)
    (hb : b ∈ S) (hab : a ≠ b) (h0 : B a b = 0) : a * b ∈ S := by
  have hbE : b ∈ polarE B S a := by
    unfold polarE
    exact Subgroup.subset_closure ⟨hb, h0⟩
  have hprod : a * b ∈ polarE B S a := Subgroup.mul_mem _ (self_mem_polarE hB ha) hbE
  refine hS.mem_of_mem_E a ha (a * b) hprod (fun h1 => hab ?_)
  have h2 : a * b = a * a := by rw [h1, hB.sq_eq_one a]
  exact (mul_left_cancel h2).symm

private theorem polar_exhaust (hB : SympForm B) (hS : PolarData B S) {p : V} (hp : p ∈ S)
    {u v : V} (hu : u ∈ polarE B S p) (hv : v ∈ polarE B S p) (huv : B u v = 1) :
    polarE B S p ≤ (Subgroup.zpowers p ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers v := by
  have hp1 : p ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hp)
  have hpv : B p v = 0 := polarE_perp hB p hv
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, polar_B_one_left hB v] at huv
    exact absurd huv (by decide)
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, polar_B_one_right hB u] at huv
    exact absurd huv (by decide)
  have hpu : p ≠ u := by
    intro h
    have h1 := hpv
    rw [h, huv] at h1
    exact absurd h1 (by decide)
  have hcP : Nat.card (Subgroup.zpowers p) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [sq]; exact hB.sq_eq_one p) hp1]
  have hcU : Nat.card (Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [sq]; exact hB.sq_eq_one u) hu1]
  have hcV : Nat.card (Subgroup.zpowers v) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [sq]; exact hB.sq_eq_one v) hv1]
  have hPU : Subgroup.zpowers p ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    apply Subgroup.mem_bot.2
    rcases polar_zpowers_cases (hB.sq_eq_one p) hx1 with h | h
    · exact h
    · rcases polar_zpowers_cases (hB.sq_eq_one u) hx2 with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hpu
  have hsup : ∀ y ∈ Subgroup.zpowers p ⊔ Subgroup.zpowers u, B y u = 0 := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hy
    rw [hB.mul_left]
    have ha0 : B a u = 0 := by
      rcases polar_zpowers_cases (hB.sq_eq_one p) ha with h | h
      · rw [h]
        exact polar_B_one_left hB u
      · rw [h]
        exact polarE_perp hB p hu
    have hb0 : B b u = 0 := by
      rcases polar_zpowers_cases (hB.sq_eq_one u) hb with h | h
      · rw [h]
        exact polar_B_one_left hB u
      · rw [h]
        exact hB.alt u
    rw [ha0, hb0, add_zero]
  have hPUW : (Subgroup.zpowers p ⊔ Subgroup.zpowers u) ⊓ Subgroup.zpowers v = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    apply Subgroup.mem_bot.2
    rcases polar_zpowers_cases (hB.sq_eq_one v) hx2 with h | h
    · exact h
    · exfalso
      have h3 := hsup x hx1
      rw [h, hB.symm v u, huv] at h3
      exact absurd h3 (by decide)
  have hcard : Nat.card ((Subgroup.zpowers p ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers v :
      Subgroup V) = 8 := by
    rw [polar_card_sup _ _ hPUW, polar_card_sup _ _ hPU, hcP, hcU, hcV]
  have hMle : (Subgroup.zpowers p ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers v ≤ polarE B S p := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact self_mem_polarE hB hp
    · rw [Subgroup.zpowers_le]
      exact hu
    · rw [Subgroup.zpowers_le]
      exact hv
  haveI : Finite (polarE B S p) :=
    Nat.finite_of_card_ne_zero (by rw [hS.card_E p hp]; decide)
  have hEq := Subgroup.eq_of_le_of_card_ge hMle (le_of_eq ((hS.card_E p hp).trans hcard.symm))
  exact le_of_eq hEq.symm

theorem rad_polarE (hB : SympForm B) (hS : PolarData B S) {p : V} (hp : p ∈ S) {x : V}
    (hx : x ∈ polarE B S p) (hxr : ∀ y ∈ polarE B S p, B x y = 0) : x = 1 ∨ x = p := by
  obtain ⟨u, hu, v, hv, huv0⟩ := hS.not_isotropic p hp
  have huv : B u v = 1 := polar_zmod2_ne_zero _ huv0
  have hE := polar_exhaust hB hS hp hu hv huv
  obtain ⟨y1, hy1, w, hw, hxw⟩ := Subgroup.mem_sup.1 (hE hx)
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hy1
  have hxeq : x = a * b * w := by rw [hab, hxw]
  have ha' := polar_zpowers_cases (hB.sq_eq_one p) ha
  have hb' := polar_zpowers_cases (hB.sq_eq_one u) hb
  have hw' := polar_zpowers_cases (hB.sq_eq_one v) hw
  have hau : B a u = 0 := by
    rcases ha' with h | h
    · rw [h]
      exact polar_B_one_left hB u
    · rw [h]
      exact polarE_perp hB p hu
  have hav : B a v = 0 := by
    rcases ha' with h | h
    · rw [h]
      exact polar_B_one_left hB v
    · rw [h]
      exact polarE_perp hB p hv
  have hbu : B b u = 0 := by
    rcases hb' with h | h
    · rw [h]
      exact polar_B_one_left hB u
    · rw [h]
      exact hB.alt u
  have hvu : B v u = 1 := (hB.symm v u).trans huv
  have hw1 : w = 1 := by
    have hBxu : B x u = 0 := hxr u hu
    rw [hxeq, hB.mul_left, hB.mul_left, hau, hbu] at hBxu
    simp only [zero_add] at hBxu
    rcases hw' with h | h
    · exact h
    · exfalso
      rw [h, hvu] at hBxu
      exact absurd hBxu (by decide)
  have hxab : x = a * b := by rw [hxeq, hw1, mul_one]
  have hb1 : b = 1 := by
    have hBxv : B x v = 0 := hxr v hv
    rcases hb' with h | h
    · exact h
    · exfalso
      rw [hxab, hB.mul_left, hav, h, huv] at hBxv
      simp only [zero_add] at hBxv
      exact absurd hBxv (by decide)
  have hxa : x = a := by rw [hxab, hb1, mul_one]
  rcases ha' with h | h
  · left
    rw [hxa, h]
  · right
    rw [hxa, h]

theorem exists_far (hB : SympForm B) (hS : PolarData B S) {z : V} (hz : z ∈ S) :
    ∃ s ∈ S, B z s = 1 := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ x : V, B z x = 0 := by
    intro x
    have hx : x ∈ Subgroup.closure S := by rw [hS.span]; exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem c hc => exact polar_zmod2_ne_one _ (hcon c hc)
    | one => exact polar_B_one_right hB z
    | mul c d _ _ hc hd => rw [hB.mul_right, hc, hd, add_zero]
    | inv c _ hc =>
      rw [polar_inv_eq c (hB.sq_eq_one c)]
      exact hc
  have h1 : z = 1 := hB.nondeg z hzero
  rw [h1] at hz
  exact hS.one_notMem hz

private theorem polar_exists_E_ne (hB : SympForm B) (hS : PolarData B S) {z : V} (hz : z ∈ S) :
    ∃ u ∈ polarE B S z, u ≠ 1 ∧ u ≠ z := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hS.not_isotropic z hz
  by_contra hcon
  push Not at hcon
  apply hxy
  have hx' : x = 1 ∨ x = z := by
    by_cases h : x = 1
    · exact Or.inl h
    · exact Or.inr (hcon x hx h)
  have hy' : y = 1 ∨ y = z := by
    by_cases h : y = 1
    · exact Or.inl h
    · exact Or.inr (hcon y hy h)
  rcases hx' with h | h <;> rcases hy' with h' | h' <;> rw [h, h']
  · exact polar_B_one_left hB 1
  · exact polar_B_one_left hB z
  · exact polar_B_one_right hB z
  · exact hB.alt z

@[expose] def polarA (B : V → V → ZMod 2) (S : Set V) (z s : V) : Subgroup V :=
  polarE B S z ⊔ Subgroup.zpowers s

section Far

variable (hB : SympForm B) (hS : PolarData B S) {z s : V} (hz : z ∈ S) (hs : s ∈ S)
  (hzs : B z s = 1)
include hB hS hz hs hzs

theorem card_polarA : Nat.card (polarA B S z s) = 16 := by
  have hs1 : s ≠ 1 := fun h => hS.one_notMem (by rw [← h]; exact hs)
  have hs2 : s * s = 1 := hB.sq_eq_one s
  have hdisj : polarE B S z ⊓ Subgroup.zpowers s = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    rcases polar_zpowers_cases hs2 hx2 with h | h
    · exact Subgroup.mem_bot.2 h
    · exfalso
      have h3 := polarE_perp hB z hx1
      rw [h, hzs] at h3
      exact absurd h3 (by decide)
  have hcZ : Nat.card (Subgroup.zpowers s) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [sq]; exact hs2) hs1]
  have hcE : Nat.card (polarE B S z) = 8 := hS.card_E z hz
  unfold polarA
  rw [polar_card_sup _ _ hdisj, hcE, hcZ]

theorem mem_polarA_of_orth {x : V} (hx : x ∈ S) (hxs : B s x = 0) : x ∈ polarA B S z s := by
  by_cases hxe : x = s
  · rw [hxe]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  · have hsx : s * x ∈ S := mul_mem_of_orth hB hS hs hx (fun h => hxe h.symm) hxs
    by_cases hzx : B z x = 0
    · have hxE : x ∈ polarE B S z := by
        unfold polarE
        exact Subgroup.subset_closure ⟨hx, hzx⟩
      exact Subgroup.mem_sup_left hxE
    · have hzx1 : B z x = 1 := polar_zmod2_ne_zero _ hzx
      have hzsx : B z (s * x) = 0 := by
        rw [hB.mul_right, hzs, hzx1, polar_one_add_one]
      have hE : s * x ∈ polarE B S z := by
        unfold polarE
        exact Subgroup.subset_closure ⟨hsx, hzsx⟩
      have hxeq : x = s * x * s := by
        rw [mul_comm s x, mul_assoc, hB.sq_eq_one s, mul_one]
      have hmem : s * x * s ∈ polarA B S z s := Subgroup.mul_mem_sup hE (Subgroup.mem_zpowers s)
      rwa [← hxeq] at hmem

theorem far_of_not_mem_polarA {q : V} (hq : q ∈ S) (hqA : q ∉ polarA B S z s) :
    B z q = 1 ∧ B s q = 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    apply hqA
    have h0 : B z q = 0 := polar_zmod2_ne_one _ h
    have hqE : q ∈ polarE B S z := by
      unfold polarE
      exact Subgroup.subset_closure ⟨hq, h0⟩
    exact Subgroup.mem_sup_left hqE
  · by_contra h
    exact hqA (mem_polarA_of_orth hB hS hz hs hzs hq (polar_zmod2_ne_one _ h))

theorem eq_on_polarE_of_not_mem_polarA {q : V} (hq : q ∈ S) (hqA : q ∉ polarA B S z s) {e : V}
    (he : e ∈ polarE B S z) : B q e = B s e := by
  obtain ⟨hzq, hsq⟩ := far_of_not_mem_polarA hB hS hz hs hzs hq hqA
  have hEA : ∀ t ∈ S, B z t = 0 → t ∈ polarA B S z s := by
    intro t ht hzt
    have htE : t ∈ polarE B S z := by
      unfold polarE
      exact Subgroup.subset_closure ⟨ht, hzt⟩
    exact Subgroup.mem_sup_left htE
  have hK : ∀ t ∈ S, B z t = 0 → B q t = 0 → B s t = 0 := by
    intro t ht hzt hqt
    have hqt_ne : q ≠ t := by
      intro h
      exact hqA (by rw [h]; exact hEA t ht hzt)
    have hqtS : q * t ∈ S := mul_mem_of_orth hB hS hq ht hqt_ne hqt
    have hqtA : q * t ∉ polarA B S z s := by
      intro hmem
      apply hqA
      have hq_eq : q = q * t * t := by rw [mul_assoc, hB.sq_eq_one t, mul_one]
      rw [hq_eq]
      exact Subgroup.mul_mem _ hmem (hEA t ht hzt)
    have h1 := (far_of_not_mem_polarA hB hS hz hs hzs hqtS hqtA).2
    rw [hB.mul_right, hsq] at h1
    exact polar_one_add_eq_one _ h1
  have hgen : ∀ t ∈ S, B z t = 0 → B q t = B s t := by
    intro t ht hzt
    rcases polar_zmod2_cases (B q t) with h0 | h1
    · rw [h0, hK t ht hzt h0]
    · rw [h1]
      by_cases htz : t = z
      · rw [htz, hB.symm s z, hzs]
      · have hzt' : z * t ∈ S := mul_mem_of_orth hB hS hz ht (fun h => htz h.symm) hzt
        have hzt0 : B z (z * t) = 0 := by
          rw [hB.mul_right, hB.alt z, hzt, add_zero]
        have hqzt : B q (z * t) = 0 := by
          rw [hB.mul_right, hB.symm q z, hzq, h1, polar_one_add_one]
        have hszt : B s (z * t) = 0 := hK (z * t) hzt' hzt0 hqzt
        have h2 := hB.mul_right s z t
        rw [hszt, hB.symm s z, hzs] at h2
        exact polar_zero_eq_one_add _ h2
  have hE : ∀ e ∈ polarE B S z, B q e = B s e := by
    intro e he
    unfold polarE at he
    induction he using Subgroup.closure_induction with
    | mem c hc => exact hgen c hc.1 hc.2
    | one => rw [polar_B_one_right hB q, polar_B_one_right hB s]
    | mul c d _ _ hc hd => rw [hB.mul_right, hB.mul_right, hc, hd]
    | inv c _ hc =>
      rw [polar_inv_eq c (hB.sq_eq_one c)]
      exact hc
  exact hE e he

theorem orth_of_not_mem_polarA {q q' : V} (hq : q ∈ S) (hqA : q ∉ polarA B S z s)
    (hq' : q' ∈ S) (hq'A : q' ∉ polarA B S z s) (hne : q ≠ q') : B q q' = 1 := by
  by_contra hcon
  have h0 : B q q' = 0 := polar_zmod2_ne_one _ hcon
  obtain ⟨hzq, -⟩ := far_of_not_mem_polarA hB hS hz hs hzs hq hqA
  obtain ⟨hzq', -⟩ := far_of_not_mem_polarA hB hS hz hs hzs hq' hq'A
  have hqq : q * q' ∈ S := mul_mem_of_orth hB hS hq hq' hne h0
  have hzqq : B z (q * q') = 0 := by
    rw [hB.mul_right, hzq, hzq', polar_one_add_one]
  have hmem : q * q' ∈ polarE B S z := by
    unfold polarE
    exact Subgroup.subset_closure ⟨hqq, hzqq⟩
  have hperp : ∀ y ∈ polarE B S z, B (q * q') y = 0 := by
    intro y hy
    rw [hB.mul_left, eq_on_polarE_of_not_mem_polarA hB hS hz hs hzs hq hqA hy,
      eq_on_polarE_of_not_mem_polarA hB hS hz hs hzs hq' hq'A hy]
    exact polar_zmod2_add_self _
  rcases rad_polarE hB hS hz hmem hperp with h1 | h1
  · apply hne
    have h2 : q * q' = q * q := by rw [h1, hB.sq_eq_one q]
    exact (mul_left_cancel h2).symm
  · have h2 : B q (q * q') = B q q' := by
      rw [hB.mul_right, hB.alt q, zero_add]
    rw [h1, hB.symm q z, hzq, h0] at h2
    exact absurd h2 (by decide)

theorem eq_of_not_mem_polarA {q q' : V} (hq : q ∈ S) (hqA : q ∉ polarA B S z s) (hq' : q' ∈ S)
    (hq'A : q' ∉ polarA B S z s) : q = q' := by
  by_contra hne
  have h7 := orth_of_not_mem_polarA hB hS hz hs hzs hq hqA hq' hq'A hne
  obtain ⟨u, hu, hu1, huz⟩ := polar_exists_E_ne hB hS hz
  obtain ⟨f, hf, hf1, hsf⟩ : ∃ f ∈ polarE B S z, f ≠ 1 ∧ B s f = 0 := by
    by_cases hsu : B s u = 0
    · exact ⟨u, hu, hu1, hsu⟩
    · have huz1 : u * z ≠ 1 := by
        intro h
        have h2 : u * z = z * z := by rw [h, hB.sq_eq_one z]
        exact huz (mul_right_cancel h2)
      refine ⟨u * z, Subgroup.mul_mem _ hu (self_mem_polarE hB hz), huz1, ?_⟩
      rw [hB.mul_right, hB.symm s z, hzs, polar_zmod2_ne_zero _ hsu, polar_one_add_one]
  have hfS : f ∈ S := hS.mem_of_mem_E z hz f hf hf1
  have hzf : B z f = 0 := polarE_perp hB z hf
  have hfz : B f z = 0 := (hB.symm f z).trans hzf
  have hfs : B f s = 0 := (hB.symm f s).trans hsf
  have hzE : z ∈ polarE B S f := by
    unfold polarE
    exact Subgroup.subset_closure ⟨hz, hfz⟩
  have hsE : s ∈ polarE B S f := by
    unfold polarE
    exact Subgroup.subset_closure ⟨hs, hfs⟩
  have hEf := polar_exhaust hB hS hfS hzE hsE hzs
  have hqf : B q f = 0 := (eq_on_polarE_of_not_mem_polarA hB hS hz hs hzs hq hqA hf).trans hsf
  have hq'f : B f q' = 0 :=
    (hB.symm f q').trans ((eq_on_polarE_of_not_mem_polarA hB hS hz hs hzs hq' hq'A hf).trans hsf)
  have hq'E : q' ∈ polarE B S f := by
    unfold polarE
    exact Subgroup.subset_closure ⟨hq', hq'f⟩
  obtain ⟨hzq, hsq⟩ := far_of_not_mem_polarA hB hS hz hs hzs hq hqA
  obtain ⟨hzq', hsq'⟩ := far_of_not_mem_polarA hB hS hz hs hzs hq' hq'A
  have haux : ∀ x ∈ (Subgroup.zpowers f ⊔ Subgroup.zpowers z) ⊔ Subgroup.zpowers s,
      B z x = 1 → B s x = 1 → x = z * s ∨ x = f * (z * s) := by
    intro x hx hzx hsx
    obtain ⟨y, hy, w, hw, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hy
    have ha' := polar_zpowers_cases (hB.sq_eq_one f) ha
    have hb' := polar_zpowers_cases (hB.sq_eq_one z) hb
    have hw' := polar_zpowers_cases (hB.sq_eq_one s) hw
    have hBza : B z a = 0 := by
      rcases ha' with h | h
      · rw [h]
        exact polar_B_one_right hB z
      · rw [h]
        exact hzf
    have hBzb : B z b = 0 := by
      rcases hb' with h | h
      · rw [h]
        exact polar_B_one_right hB z
      · rw [h]
        exact hB.alt z
    have hBsa : B s a = 0 := by
      rcases ha' with h | h
      · rw [h]
        exact polar_B_one_right hB s
      · rw [h]
        exact hsf
    have hws : w = s := by
      rcases hw' with h | h
      · exfalso
        rw [h, hB.mul_right, hB.mul_right, polar_B_one_right hB z, hBza, hBzb] at hzx
        exact absurd hzx (by decide)
      · exact h
    have hbz : b = z := by
      rcases hb' with h | h
      · exfalso
        rw [h, hws, hB.mul_right, hB.mul_right, hBsa, polar_B_one_right hB s, hB.alt s] at hsx
        exact absurd hsx (by decide)
      · exact h
    rw [hbz, hws]
    rcases ha' with h | h
    · left
      rw [h, one_mul]
    · right
      rw [h, mul_assoc]
  have hq'form := haux q' (hEf hq'E) hzq' hsq'
  have hqz : B q z = 1 := (hB.symm q z).trans hzq
  have hqs : B q s = 1 := (hB.symm q s).trans hsq
  rcases hq'form with h | h
  · rw [h, hB.mul_right, hqz, hqs] at h7
    exact absurd h7 (by decide)
  · rw [h, hB.mul_right, hB.mul_right, hqf, hqz, hqs] at h7
    exact absurd h7 (by decide)

theorem subset_polarA : ∀ q ∈ S, q ∈ polarA B S z s := by
  intro q hq
  by_contra hqA
  obtain ⟨hzq, hsq⟩ := far_of_not_mem_polarA hB hS hz hs hzs hq hqA
  have hqs : B q s = 1 := (hB.symm q s).trans hsq
  have hwE : ∀ e ∈ polarE B S z, B (q * s * z) e = 0 := by
    intro e he
    rw [hB.mul_left, hB.mul_left, eq_on_polarE_of_not_mem_polarA hB hS hz hs hzs hq hqA he,
      polarE_perp hB z he, add_zero]
    exact polar_zmod2_add_self _
  have hwS : B (q * s * z) s = 0 := by
    rw [hB.mul_left, hB.mul_left, hqs, hB.alt s, hzs]
    decide
  have hzero : ∀ x ∈ S, B (q * s * z) x = 0 := by
    intro x hx
    by_cases hxA : x ∈ polarA B S z s
    · obtain ⟨e, he, t, ht, rfl⟩ := Subgroup.mem_sup.1 hxA
      have hwt : B (q * s * z) t = 0 := by
        rcases polar_zpowers_cases (hB.sq_eq_one s) ht with h | h
        · rw [h]
          exact polar_B_one_right hB _
        · rw [h]
          exact hwS
      rw [hB.mul_right, hwE e he, hwt, add_zero]
    · have hxq : x = q := eq_of_not_mem_polarA hB hS hz hs hzs hx hxA hq hqA
      rw [hxq, hB.mul_left, hB.mul_left, hB.alt q, hsq, hzq]
      decide
  have hall : ∀ x : V, B (q * s * z) x = 0 := by
    intro x
    have hx : x ∈ Subgroup.closure S := by rw [hS.span]; exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem c hc => exact hzero c hc
    | one => exact polar_B_one_right hB _
    | mul c d _ _ hc hd => rw [hB.mul_right, hc, hd, add_zero]
    | inv c _ hc =>
      rw [polar_inv_eq c (hB.sq_eq_one c)]
      exact hc
  have hw1 : q * s * z = 1 := hB.nondeg _ hall
  have hsz : s * z * (s * z) = 1 := by
    rw [mul_mul_mul_comm, hB.sq_eq_one s, hB.sq_eq_one z, mul_one]
  have hq_eq : q = s * z := by
    have h' : q * (s * z) = 1 := by
      rw [← mul_assoc]
      exact hw1
    exact (eq_inv_of_mul_eq_one_left h').trans (inv_eq_of_mul_eq_one_right hsz)
  apply hqA
  rw [hq_eq, mul_comm]
  exact Subgroup.mul_mem_sup (self_mem_polarE hB hz) (Subgroup.mem_zpowers s)

end Far

private theorem polar_mem_of_orth_point (hB : SympForm B) (hS : PolarData B S) {x : V}
    (hx : x ∈ S) {d : V} (hd : d ≠ 1) (hxd : B x d = 0) : d ∈ S := by
  obtain ⟨t, ht, hxt⟩ := exists_far hB hS hx
  have hle : Subgroup.closure S ≤ polarA B S x t :=
    (Subgroup.closure_le _).2 (subset_polarA hB hS hx ht hxt)
  have hdA : d ∈ polarA B S x t := by
    apply hle
    rw [hS.span]
    exact Subgroup.mem_top d
  obtain ⟨e, he, w, hw, hew⟩ := Subgroup.mem_sup.1 hdA
  rw [← hew] at hd hxd ⊢
  rcases polar_zpowers_cases (hB.sq_eq_one t) hw with h | h
  · rw [h, mul_one] at hd ⊢
    exact hS.mem_of_mem_E x hx e he hd
  · exfalso
    rw [h, hB.mul_right, polarE_perp hB x he, hxt, zero_add] at hxd
    exact absurd hxd (by decide)

theorem card_eq_sixteen [Finite V] (hB : SympForm B) (hS : PolarData B S) :
    Nat.card V = 16 ∧ ∀ x : V, x ≠ 1 → x ∈ S := by
  obtain ⟨z, hz⟩ := hS.nonempty
  obtain ⟨s, hs, hzs⟩ := exists_far hB hS hz
  have hle : Subgroup.closure S ≤ polarA B S z s :=
    (Subgroup.closure_le _).2 (subset_polarA hB hS hz hs hzs)
  have htop : polarA B S z s = ⊤ := by
    rw [eq_top_iff]
    intro d _
    apply hle
    rw [hS.span]
    exact Subgroup.mem_top d
  refine ⟨?_, fun d hd => ?_⟩
  · rw [← Subgroup.card_top, ← htop, card_polarA hB hS hz hs hzs]
  · rcases polar_zmod2_cases (B z d) with h0 | h1
    · exact polar_mem_of_orth_point hB hS hz hd h0
    · obtain ⟨t, ht, ht1, htz⟩ := polar_exists_E_ne hB hS hz
      have htS : t ∈ S := hS.mem_of_mem_E z hz t ht ht1
      by_cases htd : B t d = 0
      · exact polar_mem_of_orth_point hB hS htS hd htd
      · have hB1 : B t d = 1 := polar_zmod2_ne_zero _ htd
        have htz1 : t * z ≠ 1 := by
          intro h
          have h2 : t * z = z * z := by rw [h, hB.sq_eq_one z]
          exact htz (mul_right_cancel h2)
        have htzS : t * z ∈ S :=
          hS.mem_of_mem_E z hz (t * z) (Subgroup.mul_mem _ ht (self_mem_polarE hB hz)) htz1
        have hd0 : B (t * z) d = 0 := by
          rw [hB.mul_left, hB1, h1, polar_one_add_one]
        exact polar_mem_of_orth_point hB hS htzS hd hd0

end PolarData

end CFSG.ClassicalInvolution.Q3.Sec13.Polar

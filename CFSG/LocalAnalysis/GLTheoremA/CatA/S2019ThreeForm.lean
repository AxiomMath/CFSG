module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019.Three

open scoped commutatorElement

variable {G : Type*} [Group G]

structure FormData (T N : Subgroup G) (z : G) : Prop where
  le : N ≤ T
  central : ∀ n ∈ N, ∀ t ∈ T, n * t = t * n
  sq : ∀ t ∈ T, t * t ∈ N
  z_central : ∀ g : G, g * z = z * g
  z_sq : z * z = 1
  z_ne : z ≠ 1
  comm : ∀ s ∈ T, ∀ t ∈ T, ⁅s, t⁆ = 1 ∨ ⁅s, t⁆ = z

structure ActData (T N : Subgroup G) (x : G) : Prop where
  pow : x ^ 3 = 1
  normT : ∀ t ∈ T, x * t * x⁻¹ ∈ T
  normN : ∀ n ∈ N, x * n * x⁻¹ ∈ N
  ab : ∀ A : Subgroup G, A ≤ T → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    (∀ a ∈ A, x * a * x⁻¹ ∈ A) → ∀ a ∈ A, x * a * x⁻¹ = a

@[expose] def nu (x t : G) : G := t * (x * t * x⁻¹) * (x ^ 2 * t * (x ^ 2)⁻¹)

theorem eqv_trans {N : Subgroup G} {a b c : G} (h1 : a⁻¹ * b ∈ N) (h2 : b⁻¹ * c ∈ N) :
    a⁻¹ * c ∈ N := by
  have := mul_mem h1 h2
  rwa [mul_assoc, mul_inv_cancel_left] at this

theorem eqv_symm {N : Subgroup G} {a b : G} (h : a⁻¹ * b ∈ N) : b⁻¹ * a ∈ N := by
  have := inv_mem h
  rwa [mul_inv_rev, inv_inv] at this

theorem eqv_mul_left {N : Subgroup G} (c : G) {a b : G} (h : a⁻¹ * b ∈ N) :
    (c * a)⁻¹ * (c * b) ∈ N := by
  rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem eqv_conj {N : Subgroup G} {y : G} (hy : ∀ n ∈ N, y * n * y⁻¹ ∈ N) {a b : G}
    (h : a⁻¹ * b ∈ N) : (y * a * y⁻¹)⁻¹ * (y * b * y⁻¹) ∈ N := by
  have e : (y * a * y⁻¹)⁻¹ * (y * b * y⁻¹) = y * (a⁻¹ * b) * y⁻¹ := by group
  rw [e]
  exact hy _ h

theorem mem_of_eqv {N : Subgroup G} {a b : G} (ha : a ∈ N) (h : a⁻¹ * b ∈ N) : b ∈ N := by
  have := mul_mem ha h
  rwa [mul_inv_cancel_left] at this

namespace FormData

variable {T N : Subgroup G} {z : G} (hT : FormData T N z)
include hT

theorem commutator_mem {s t : G} (hs : s ∈ T) (ht : t ∈ T) : ⁅s, t⁆ ∈ N := by
  have h1 := hT.sq _ (mul_mem hs ht)
  have h2 := hT.sq _ (inv_mem hs)
  have h3 := hT.sq _ (inv_mem ht)
  have hc := hT.central _ h2 _ (inv_mem ht)
  have e : ⁅s, t⁆ = s * t * (s * t) * (s⁻¹ * s⁻¹) * (t⁻¹ * t⁻¹) := by
    rw [commutatorElement_def]
    calc s * t * s⁻¹ * t⁻¹ = s * t * (s * t) * (t⁻¹ * (s⁻¹ * s⁻¹)) * t⁻¹ := by group
      _ = s * t * (s * t) * (s⁻¹ * s⁻¹ * t⁻¹) * t⁻¹ := by rw [← hc]
      _ = s * t * (s * t) * (s⁻¹ * s⁻¹) * (t⁻¹ * t⁻¹) := by group
  rw [e]
  exact mul_mem (mul_mem h1 h2) h3

theorem swap {a b : G} (ha : a ∈ T) (hb : b ∈ T) : (a * b)⁻¹ * (b * a) ∈ N := by
  have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact hT.commutator_mem (inv_mem hb) (inv_mem ha)

theorem mid_swap {p q r s : G} (hq : q ∈ T) (hr : r ∈ T) (hs : s ∈ T) :
    (p * q * (r * s))⁻¹ * (p * r * (q * s)) ∈ N := by
  have h := hT.commutator_mem (inv_mem hr) (inv_mem hq)
  have hc := hT.central _ h _ hs
  have e : (p * q * (r * s))⁻¹ * (p * r * (q * s)) = s⁻¹ * ⁅r⁻¹, q⁻¹⁆ * s := by
    rw [commutatorElement_def]
    group
  rw [e, mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  exact h

theorem eqv_mul_right {c : G} (hc : c ∈ T) {a b : G} (h : a⁻¹ * b ∈ N) :
    (a * c)⁻¹ * (b * c) ∈ N := by
  have e : (a * c)⁻¹ * (b * c) = c⁻¹ * (a⁻¹ * b) * c := by group
  rw [e, mul_assoc, hT.central _ h _ hc, ← mul_assoc, inv_mul_cancel, one_mul]
  exact h

theorem eqv_mul {a a' b b' : G} (hb : b ∈ T) (h1 : a⁻¹ * a' ∈ N) (h2 : b⁻¹ * b' ∈ N) :
    (a * b)⁻¹ * (a' * b') ∈ N :=
  eqv_trans (hT.eqv_mul_right hb h1) (eqv_mul_left a' h2)

theorem comm_central {s t : G} (hs : s ∈ T) (ht : t ∈ T) (g : G) : g * ⁅s, t⁆ = ⁅s, t⁆ * g := by
  rcases hT.comm s hs t ht with h | h
  · rw [h, mul_one, one_mul]
  · rw [h]
    exact hT.z_central g

theorem comm_inv {s t : G} (hs : s ∈ T) (ht : t ∈ T) : ⁅t, s⁆ = ⁅s, t⁆ := by
  rw [← commutatorElement_inv]
  rcases hT.comm s hs t ht with h | h
  · rw [h, inv_one]
  · rw [h, inv_eq_of_mul_eq_one_right hT.z_sq]

theorem comm_mul_left {a b c : G} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have e : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, hT.comm_central hb hc a, mul_inv_cancel_right]
  exact hT.comm_central ha hc _

theorem comm_mul_right {a b c : G} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have e : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, hT.comm_central ha hc b, mul_inv_cancel_right]

end FormData

theorem nu_conj {x y : G} (hyx : y * x = x * y) (t : G) : nu x (y * t * y⁻¹) = y * nu x t * y⁻¹ := by
  have h1 : x * (y * t * y⁻¹) * x⁻¹ = y * (x * t * x⁻¹) * y⁻¹ := by
    calc x * (y * t * y⁻¹) * x⁻¹ = (x * y) * t * (x * y)⁻¹ := by group
      _ = (y * x) * t * (y * x)⁻¹ := by rw [hyx]
      _ = y * (x * t * x⁻¹) * y⁻¹ := by group
  have hyx2 : y * x ^ 2 = x ^ 2 * y := ((Commute.pow_right (show Commute y x from hyx) 2)).eq
  have h2 : x ^ 2 * (y * t * y⁻¹) * (x ^ 2)⁻¹ = y * (x ^ 2 * t * (x ^ 2)⁻¹) * y⁻¹ := by
    calc x ^ 2 * (y * t * y⁻¹) * (x ^ 2)⁻¹ = (x ^ 2 * y) * t * (x ^ 2 * y)⁻¹ := by group
      _ = (y * x ^ 2) * t * (y * x ^ 2)⁻¹ := by rw [hyx2]
      _ = y * (x ^ 2 * t * (x ^ 2)⁻¹) * y⁻¹ := by group
  unfold nu
  rw [h1, h2]
  group

private theorem mul_comm_of_mem_closure {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    {a b : G} (ha : a ∈ Subgroup.closure S) (hb : b ∈ Subgroup.closure S) : a * b = b * a := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro c hc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro d hd
    exact hS d hd c hc
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set G) := by
    rw [Subgroup.closure_le]
    intro c hc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.1 (h1 hd) c hc).symm
  exact Subgroup.mem_centralizer_iff.1 (h2 hb) a ha

namespace ActData

variable {T N : Subgroup G} {z x : G} (hx : ActData T N x)
include hx

theorem pow_conj_mem_T (k : ℕ) {t : G} (ht : t ∈ T) : x ^ k * t * (x ^ k)⁻¹ ∈ T := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
    have e : x ^ (k + 1) * t * (x ^ (k + 1))⁻¹ = x * (x ^ k * t * (x ^ k)⁻¹) * x⁻¹ := by
      rw [pow_succ']
      group
    rw [e]
    exact hx.normT _ ih

theorem pow_conj_mem_N (k : ℕ) {n : G} (hn : n ∈ N) : x ^ k * n * (x ^ k)⁻¹ ∈ N := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    have e : x ^ (k + 1) * n * (x ^ (k + 1))⁻¹ = x * (x ^ k * n * (x ^ k)⁻¹) * x⁻¹ := by
      rw [pow_succ']
      group
    rw [e]
    exact hx.normN _ ih

theorem conj_three (t : G) : x * (x ^ 2 * t * (x ^ 2)⁻¹) * x⁻¹ = t := by
  have e : x * (x ^ 2 * t * (x ^ 2)⁻¹) * x⁻¹ = x ^ 3 * t * (x ^ 3)⁻¹ := by group
  rw [e, hx.pow, one_mul, inv_one, mul_one]

theorem conj_three' (t : G) : x ^ 2 * (x * t * x⁻¹) * (x ^ 2)⁻¹ = t := by
  have e : x ^ 2 * (x * t * x⁻¹) * (x ^ 2)⁻¹ = x ^ 3 * t * (x ^ 3)⁻¹ := by group
  rw [e, hx.pow, one_mul, inv_one, mul_one]

theorem nu_mem {t : G} (ht : t ∈ T) : nu x t ∈ T :=
  mul_mem (mul_mem ht (hx.normT _ ht)) (hx.pow_conj_mem_T 2 ht)

theorem nu_conj_self (t : G) : nu x (x * t * x⁻¹) = x * nu x t * x⁻¹ := nu_conj (y := x) rfl t

theorem conj_nu (hT : FormData T N z) {t : G} (ht : t ∈ T) :
    (nu x t)⁻¹ * (x * nu x t * x⁻¹) ∈ N := by
  have ht1 := hx.normT _ ht
  have ht2 := hx.pow_conj_mem_T 2 ht
  have e : x * nu x t * x⁻¹ = (x * t * x⁻¹) * (x ^ 2 * t * (x ^ 2)⁻¹) * t := by
    unfold nu
    calc x * (t * (x * t * x⁻¹) * (x ^ 2 * t * (x ^ 2)⁻¹)) * x⁻¹
        = (x * t * x⁻¹) * (x ^ 2 * t * (x ^ 2)⁻¹) * (x * (x ^ 2 * t * (x ^ 2)⁻¹) * x⁻¹) := by
          group
      _ = (x * t * x⁻¹) * (x ^ 2 * t * (x ^ 2)⁻¹) * t := by rw [hx.conj_three]
  rw [e]
  unfold nu
  have := hT.swap ht (mul_mem ht1 ht2)
  simpa only [mul_assoc] using this

theorem nu_mul (hT : FormData T N z) {s t : G} (hs : s ∈ T) (ht : t ∈ T) :
    (nu x s * nu x t)⁻¹ * nu x (s * t) ∈ N := by
  have hs1 := hx.normT _ hs
  have hs2 := hx.pow_conj_mem_T 2 hs
  have ht1 := hx.normT _ ht
  have ht2 := hx.pow_conj_mem_T 2 ht
  have e : nu x (s * t) = s * t * ((x * s * x⁻¹) * (x * t * x⁻¹)) *
      ((x ^ 2 * s * (x ^ 2)⁻¹) * (x ^ 2 * t * (x ^ 2)⁻¹)) := by
    unfold nu
    group
  have h1 := hT.mid_swap (p := s * (x * s * x⁻¹)) hs2 (mul_mem ht ht1) ht2
  have h2 := hT.eqv_mul_right (mul_mem hs2 ht2) (hT.mid_swap (p := s) hs1 ht ht1)
  rw [e]
  unfold nu
  exact eqv_trans h1 h2

theorem nu_eqv_of_fix (hT : FormData T N z) {s : G} (hs : s ∈ T)
    (hfix : s⁻¹ * (x * s * x⁻¹) ∈ N) : (s * s * s)⁻¹ * nu x s ∈ N := by
  have hfix2 : s⁻¹ * (x ^ 2 * s * (x ^ 2)⁻¹) ∈ N := by
    have h := eqv_conj hx.normN hfix
    have e : x * (x * s * x⁻¹) * x⁻¹ = x ^ 2 * s * (x ^ 2)⁻¹ := by rw [pow_two]; group
    rw [e] at h
    exact eqv_trans hfix h
  exact hT.eqv_mul hs (eqv_mul_left s hfix) hfix2

theorem mem_of_fix (hT : FormData T N z) {s : G} (hs : s ∈ T)
    (hfix : s⁻¹ * (x * s * x⁻¹) ∈ N) (hnu : nu x s ∈ N) : s ∈ N := by
  have h3 := hx.nu_eqv_of_fix hT hs hfix
  have hsss : s * s * s ∈ N := by
    have := mul_mem hnu (inv_mem h3)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  have := mul_mem hsss (inv_mem (hT.sq s hs))
  have e : s * s * s * (s * s)⁻¹ = s := by group
  rwa [e] at this

theorem commutator_eq (hT : FormData T N z) {s : G} (hs : s ∈ T) (hsN : s ∉ N)
    (hnu : nu x s ∈ N) : ⁅s, x * s * x⁻¹⁆ = z := by
  have hs1 := hx.normT _ hs
  rcases hT.comm s hs _ hs1 with h | h
  · exfalso
    have hc : s * (x * s * x⁻¹) = (x * s * x⁻¹) * s :=
      commutatorElement_eq_one_iff_mul_comm.1 h
    set S : Set G := insert s (insert (x * s * x⁻¹) (N : Set G)) with hSdef
    have hST : S ⊆ T := by
      intro a ha
      rcases ha with rfl | rfl | ha
      · exact hs
      · exact hs1
      · exact hT.le ha
    have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
      have hN : ∀ a ∈ S, ∀ n ∈ (N : Set G), a * n = n * a := fun a ha n hn =>
        (hT.central n hn a (hST ha)).symm
      intro a ha b hb
      rcases hb with rfl | rfl | hb
      · rcases ha with rfl | rfl | ha
        · rfl
        · exact hc.symm
        · exact hT.central a ha _ hs
      · rcases ha with rfl | rfl | ha
        · exact hc
        · rfl
        · exact hT.central a ha _ hs1
      · exact hN a ha b hb
    have hAT : Subgroup.closure S ≤ T := (Subgroup.closure_le T).2 hST
    have hAx : ∀ a ∈ Subgroup.closure S, x * a * x⁻¹ ∈ Subgroup.closure S := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
        rcases ha with ha | ha | ha
        · rw [ha]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        · have e : x * (x * s * x⁻¹) * x⁻¹ = (s * (x * s * x⁻¹))⁻¹ * nu x s := by
            unfold nu
            rw [pow_two]
            group
          rw [ha, e]
          refine mul_mem (inv_mem (mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
            (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))
            (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hnu)))
        · exact Subgroup.subset_closure
            (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (hx.normN _ ha)))
      | one => simpa using (Subgroup.closure S).one_mem
      | mul a b _ _ iha ihb =>
        have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
        rw [e]
        exact mul_mem iha ihb
      | inv a _ iha =>
        have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem iha
    have hfix := hx.ab (Subgroup.closure S) hAT
      (fun a ha b hb => mul_comm_of_mem_closure hS ha hb) hAx s
      (Subgroup.subset_closure (Set.mem_insert _ _))
    apply hsN
    refine hx.mem_of_fix hT hs ?_ hnu
    rw [hfix, inv_mul_cancel]
    exact N.one_mem
  · exact h

theorem eqv_of_nu (hT : FormData T N z) {s w : G} (hs : s ∈ T) (hw : w ∈ T) (hsN : s ∉ N)
    (hsnu : nu x s ∈ N) (hwnu : nu x w ∈ N) :
    w ∈ N ∨ s⁻¹ * w ∈ N ∨ (x * s * x⁻¹)⁻¹ * w ∈ N ∨ (x ^ 2 * s * (x ^ 2)⁻¹)⁻¹ * w ∈ N := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hw0, hw1, hw2, hw3⟩ := hcon
  have hs1 := hx.normT _ hs
  have hwT1 := hx.normT _ hw
  have hwT2 := hx.pow_conj_mem_T 2 hw
  have hN2 : ∀ n ∈ N, x ^ 2 * n * (x ^ 2)⁻¹ ∈ N := fun n hn => hx.pow_conj_mem_N 2 hn
  have cw1 : x * (x * w * x⁻¹) * x⁻¹ = x ^ 2 * w * (x ^ 2)⁻¹ := by rw [pow_two]; group
  have cw2 : x * (x ^ 2 * w * (x ^ 2)⁻¹) * x⁻¹ = w := hx.conj_three w
  have hnu1 : nu x (x * w * x⁻¹) ∈ N := by
    rw [hx.nu_conj_self]
    exact hx.normN _ hwnu
  have hnu2 : nu x (x ^ 2 * w * (x ^ 2)⁻¹) ∈ N := by
    rw [← cw1, hx.nu_conj_self]
    exact hx.normN _ hnu1
  have hsq : ∀ v, s * v ∈ N → s⁻¹ * v ∈ N := fun v hv => by
    have := mul_mem (hT.sq _ (inv_mem hs)) hv
    have e : s⁻¹ * s⁻¹ * (s * v) = s⁻¹ * v := by group
    rwa [e] at this
  have hu0 : s * w ∉ N := fun h => hw1 (hsq _ h)
  have hu1 : s * (x * w * x⁻¹) ∉ N := fun h => by
    have h' := eqv_conj hN2 (hsq _ h)
    rw [hx.conj_three'] at h'
    exact hw3 h'
  have hu2 : s * (x ^ 2 * w * (x ^ 2)⁻¹) ∉ N := fun h => by
    have h' := eqv_conj hx.normN (hsq _ h)
    rw [cw2] at h'
    exact hw2 h'
  have hnuu : ∀ v, v ∈ T → nu x v ∈ N → nu x (s * v) ∈ N := fun v hv hvnu =>
    mem_of_eqv (mul_mem hsnu hvnu) (hx.nu_mul hT hs hv)
  have hzs := hx.commutator_eq hT hs hsN hsnu
  have hzw := hx.commutator_eq hT hw hw0 hwnu
  have hconj : ∀ a b, a ∈ T → b ∈ T → ⁅x * a * x⁻¹, x * b * x⁻¹⁆ = ⁅a, b⁆ :=
    fun a b ha hb => by
      rw [← conjugate_commutatorElement, hT.comm_central ha hb x, mul_inv_cancel_right]
  have hzw1 : ⁅x * w * x⁻¹, x ^ 2 * w * (x ^ 2)⁻¹⁆ = z := by
    rw [← cw1, hconj _ _ hw hwT1, hzw]
  have hzw2 : ⁅x ^ 2 * w * (x ^ 2)⁻¹, w⁆ = z := by
    have := hconj _ _ hwT1 hwT2
    rw [cw1, cw2, hzw1] at this
    exact this
  have hws1 : ⁅w, x * s * x⁻¹⁆ = ⁅s, x ^ 2 * w * (x ^ 2)⁻¹⁆ := by
    have := hconj _ _ hwT2 hs
    rw [cw2] at this
    rw [this, hT.comm_inv hs hwT2]
  have hw1s1 : ⁅x * w * x⁻¹, x * s * x⁻¹⁆ = ⁅s, w⁆ := by
    rw [hconj _ _ hw hs, hT.comm_inv hs hw]
  have hw2s1 : ⁅x ^ 2 * w * (x ^ 2)⁻¹, x * s * x⁻¹⁆ = ⁅s, x * w * x⁻¹⁆ := by
    have := hconj _ _ hwT1 hs
    rw [cw1] at this
    rw [this, hT.comm_inv hs hwT1]
  have hcancel : ∀ a b : G, z * a * (b * z) = z → a * b = z := by
    intro a b h
    have e : z * a * (b * z) = a * b * (z * z) := by
      rw [(hT.z_central a).symm, mul_assoc, ← mul_assoc z b z, ← hT.z_central b]
      simp only [mul_assoc]
    rwa [e, hT.z_sq, mul_one] at h
  have key0 : ⁅s, x * w * x⁻¹⁆ * ⁅s, x ^ 2 * w * (x ^ 2)⁻¹⁆ = z := by
    have h := hx.commutator_eq hT (mul_mem hs hw) hu0 (hnuu w hw hwnu)
    have ex : x * (s * w) * x⁻¹ = (x * s * x⁻¹) * (x * w * x⁻¹) := by group
    rw [ex, hT.comm_mul_left hs hw (mul_mem hs1 hwT1), hT.comm_mul_right hs hs1 hwT1,
      hT.comm_mul_right hw hs1 hwT1, hzs, hzw, hws1] at h
    exact hcancel _ _ h
  have key1 : ⁅s, x ^ 2 * w * (x ^ 2)⁻¹⁆ * ⁅s, w⁆ = z := by
    have h := hx.commutator_eq hT (mul_mem hs hwT1) hu1 (hnuu _ hwT1 hnu1)
    have ex : x * (s * (x * w * x⁻¹)) * x⁻¹ = (x * s * x⁻¹) * (x ^ 2 * w * (x ^ 2)⁻¹) := by
      rw [← cw1]
      group
    rw [ex, hT.comm_mul_left hs hwT1 (mul_mem hs1 hwT2), hT.comm_mul_right hs hs1 hwT2,
      hT.comm_mul_right hwT1 hs1 hwT2, hzs, hzw1, hw1s1] at h
    exact hcancel _ _ h
  have key2 : ⁅s, w⁆ * ⁅s, x * w * x⁻¹⁆ = z := by
    have h := hx.commutator_eq hT (mul_mem hs hwT2) hu2 (hnuu _ hwT2 hnu2)
    have ex : x * (s * (x ^ 2 * w * (x ^ 2)⁻¹)) * x⁻¹ = (x * s * x⁻¹) * w := by
      calc x * (s * (x ^ 2 * w * (x ^ 2)⁻¹)) * x⁻¹
          = (x * s * x⁻¹) * (x * (x ^ 2 * w * (x ^ 2)⁻¹) * x⁻¹) := by group
        _ = (x * s * x⁻¹) * w := by rw [cw2]
    rw [ex, hT.comm_mul_left hs hwT2 (mul_mem hs1 hw), hT.comm_mul_right hs hs1 hw,
      hT.comm_mul_right hwT2 hs1 hw, hzs, hzw2, hw2s1] at h
    exact hcancel _ _ h
  rcases hT.comm s hs w hw with h0 | h0
  · rw [h0, one_mul] at key2
    rw [h0, mul_one] at key1
    rw [key2, key1, hT.z_sq] at key0
    exact hT.z_ne key0.symm
  · rw [h0] at key1 key2
    have hc1 : ⁅s, x * w * x⁻¹⁆ = 1 := mul_left_cancel (key2.trans (mul_one z).symm)
    have hc2 : ⁅s, x ^ 2 * w * (x ^ 2)⁻¹⁆ = 1 := mul_right_cancel (key1.trans (one_mul z).symm)
    rw [hc1, hc2, one_mul] at key0
    exact hT.z_ne key0.symm

theorem fix_of_forall (hT : FormData T N z) (h : ∀ s ∈ T, nu x s ∈ N → s ∈ N) {t : G}
    (ht : t ∈ T) : t⁻¹ * (x * t * x⁻¹) ∈ N := by
  set v := nu x t with hv
  have hvT : v ∈ T := hx.nu_mem ht
  have hfix : v⁻¹ * (x * v * x⁻¹) ∈ N := hx.conj_nu hT ht
  have h3 := hx.nu_eqv_of_fix hT hvT hfix
  have hvv : v * v ∈ N := hT.sq v hvT
  have h4 : v⁻¹ * nu x v ∈ N := by
    have e : v⁻¹ * (v * v * v) = v * v := by group
    exact eqv_trans (show v⁻¹ * (v * v * v) ∈ N by rw [e]; exact hvv) h3
  have h5 : nu x (v * t) ∈ N := by
    have h6 : nu x v * v ∈ N := by
      have hc := hT.central _ h4 v hvT
      have e : nu x v * v = v * v * (v⁻¹ * nu x v) := by
        calc nu x v * v = v * ((v⁻¹ * nu x v) * v) := by group
          _ = v * (v * (v⁻¹ * nu x v)) := by rw [hc]
          _ = v * v * (v⁻¹ * nu x v) := by group
      rw [e]
      exact mul_mem hvv h4
    exact mem_of_eqv h6 (hx.nu_mul hT hvT ht)
  have hvt : v * t ∈ N := h _ (mul_mem hvT ht) h5
  have e : t⁻¹ * (x * t * x⁻¹) = (v * t)⁻¹ * (v * (x * v * x⁻¹)⁻¹) * (x * (v * t) * x⁻¹) := by
    group
  rw [e]
  refine mul_mem (mul_mem (inv_mem hvt) ?_) (hx.normN _ hvt)
  have h9 : (x * v * x⁻¹)⁻¹ * v ∈ N := eqv_symm hfix
  have := hT.central _ h9 v hvT
  have e2 : v * (x * v * x⁻¹)⁻¹ = (x * v * x⁻¹)⁻¹ * v := by
    calc v * (x * v * x⁻¹)⁻¹ = v * ((x * v * x⁻¹)⁻¹ * v) * v⁻¹ := by group
      _ = (x * v * x⁻¹)⁻¹ * v * v * v⁻¹ := by rw [← this]
      _ = (x * v * x⁻¹)⁻¹ * v := by group
  rw [e2]
  exact h9

end ActData

end CFSG.LocalAnalysis.GLTheoremA.S2019.Three

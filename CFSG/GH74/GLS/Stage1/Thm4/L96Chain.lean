module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Equiv Equiv.Perm

namespace Chain

theorem apply_apply_of_cycleType {n : ℕ} {ζ : Perm (Fin n)}
    (hζ : ζ.cycleType = {2, 2, 2, 2}) (x : Fin n) : ζ (ζ x) = x := by
  have h2 : orderOf ζ = 2 := by rw [← Perm.lcm_cycleType, hζ]; decide
  have h : ζ ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one ζ
  simpa [pow_two, Perm.ext_iff] using Perm.ext_iff.mp h x

theorem eq_of_fixed_of_cycleType {n : ℕ} (hn : n ≤ 9) {ζ : Perm (Fin n)}
    (hζ : ζ.cycleType = {2, 2, 2, 2}) {a b : Fin n} (ha : ζ a = a) (hb : ζ b = b) : a = b := by
  by_contra hab
  have hsupp : ζ.support.card = 8 := by rw [← Perm.sum_cycleType, hζ]; decide
  have hdisj : Disjoint ζ.support {a, b} := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · exact (Perm.mem_support.mp hx) ha
    · exact (Perm.mem_support.mp hx) hb
  have hcard := Finset.card_le_univ (ζ.support ∪ {a, b})
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hab, hsupp, Fintype.card_fin] at hcard
  omega

theorem mul_mem_of_normal_chain {G : Type*} [Group G] {Q U : Subgroup G} {ζ w v₀ v₁ v₂ : G}
    (hQH : ∀ q ∈ Q, ∀ x : G, Commute x ζ → x * q * x⁻¹ ∈ Q)
    (hUQ : U ≤ Q) (hUnorm : ∀ u ∈ U, ∀ q ∈ Q, q * u * q⁻¹ ∈ U) (hwU : w ∈ U)
    (hv₀ : v₀ * v₀ = 1) (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1)
    (h01 : v₀ * v₁ = v₁ * v₀) (h02 : v₀ * v₂ = v₂ * v₀) (h12 : v₁ * v₂ = v₂ * v₁)
    (hc₀ : Commute v₀ ζ) (hc₁ : Commute v₁ ζ)
    (hw₀ : w * v₀ * w⁻¹ = v₁) (hw₁ : w * v₁ * w⁻¹ = v₂) (hw₂ : w * v₂ * w⁻¹ = v₀) :
    v₀ * v₁ ∈ U ∧ v₀ * v₂ ∈ U := by
  have hi₀ : v₀⁻¹ = v₀ := inv_eq_of_mul_eq_one_right hv₀
  have hi₁ : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv₁
  have hi₂ : v₂⁻¹ = v₂ := inv_eq_of_mul_eq_one_right hv₂
  have hwQ : w ∈ Q := hUQ hwU
  have hQ01 : v₀ * v₁ ∈ Q := by
    have h := Q.mul_mem (hQH w hwQ v₀ hc₀) (Q.inv_mem hwQ)
    have e : v₀ * w * v₀⁻¹ * w⁻¹ = v₀ * v₁ := by
      calc v₀ * w * v₀⁻¹ * w⁻¹ = v₀ * (w * v₀ * w⁻¹)⁻¹ := by group
        _ = v₀ * v₁ := by rw [hw₀, hi₁]
    rwa [e] at h
  have hcomm : ∀ ω ∈ Q, ω * w * ω⁻¹ * w⁻¹ ∈ U := fun ω hω =>
    U.mul_mem (hUnorm w hwU ω hω) (U.inv_mem hwU)
  have hconj : ∀ ω : G, ω * w * ω⁻¹ * w⁻¹ = ω * (w * ω * w⁻¹)⁻¹ := fun ω => by group
  have hQ12 : v₁ * v₂ ∈ Q := by
    have h := Q.mul_mem (hQH w hwQ v₁ hc₁) (Q.inv_mem hwQ)
    have e : v₁ * w * v₁⁻¹ * w⁻¹ = v₁ * v₂ := by
      calc v₁ * w * v₁⁻¹ * w⁻¹ = v₁ * (w * v₁ * w⁻¹)⁻¹ := by group
        _ = v₁ * v₂ := by rw [hw₁, hi₂]
    rwa [e] at h
  constructor
  · have h := hcomm _ hQ12
    rw [hconj] at h
    have e : v₁ * v₂ * (w * (v₁ * v₂) * w⁻¹)⁻¹ = v₀ * v₁ := by
      have : w * (v₁ * v₂) * w⁻¹ = v₂ * v₀ := by
        calc w * (v₁ * v₂) * w⁻¹ = (w * v₁ * w⁻¹) * (w * v₂ * w⁻¹) := by group
          _ = v₂ * v₀ := by rw [hw₁, hw₂]
      rw [this, mul_inv_rev, hi₀, hi₂]
      calc v₁ * v₂ * (v₀ * v₂) = v₁ * (v₂ * v₀) * v₂ := by group
        _ = v₁ * (v₀ * v₂) * v₂ := by rw [h02]
        _ = v₀ * v₁ := by
          calc v₁ * (v₀ * v₂) * v₂ = v₁ * v₀ * (v₂ * v₂) := by group
            _ = v₀ * v₁ := by rw [hv₂, mul_one, ← h01]
    rwa [e] at h
  · have h := hcomm _ hQ01
    rw [hconj] at h
    have e : v₀ * v₁ * (w * (v₀ * v₁) * w⁻¹)⁻¹ = v₀ * v₂ := by
      have : w * (v₀ * v₁) * w⁻¹ = v₁ * v₂ := by
        calc w * (v₀ * v₁) * w⁻¹ = (w * v₀ * w⁻¹) * (w * v₁ * w⁻¹) := by group
          _ = v₁ * v₂ := by rw [hw₀, hw₁]
      rw [this, mul_inv_rev, hi₁, hi₂]
      calc v₀ * v₁ * (v₂ * v₁) = v₀ * (v₁ * v₂) * v₁ := by group
        _ = v₀ * (v₂ * v₁) * v₁ := by rw [h12]
        _ = v₀ * v₂ := by
          calc v₀ * (v₂ * v₁) * v₁ = v₀ * v₂ * (v₁ * v₁) := by group
            _ = v₀ * v₂ := by rw [hv₁, mul_one]
    rwa [e] at h

theorem closure_commute_sq {G : Type*} [Group G] (S : Set G)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x ^ 2 = 1) :
    (∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) ∧
      ∀ a ∈ Subgroup.closure S, a ^ 2 = 1 := by
  have hcent : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hcomm y hy x hx
  have habel : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha
    have hS : S ⊆ (Subgroup.centralizer {a} : Subgroup G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.mp (hcent ha) x hx).symm
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp ((Subgroup.closure_le _).mpr hS hb) a rfl
  refine ⟨habel, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => exact one_pow 2
  | mul x y hx hy hx2 hy2 =>
    rw [Commute.mul_pow (habel x hx y hy), hx2, hy2, one_mul]
  | inv x hx hx2 => rw [inv_pow, hx2, inv_one]

theorem closure_gen_commute_sq {G : Type*} [Group G] {ζ v₀ v₁ v₂ : G}
    (hv₀ : v₀ * v₀ = 1) (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1) (hζ : ζ * ζ = 1)
    (h01 : Commute v₀ v₁) (h02 : Commute v₀ v₂) (h12 : Commute v₁ v₂)
    (hc₀ : Commute v₀ ζ) (hc₁ : Commute v₁ ζ) (hc₂ : Commute v₂ ζ) :
    (∀ a ∈ Subgroup.closure {v₀ * v₁, v₀ * v₂, ζ}, ∀ b ∈ Subgroup.closure {v₀ * v₁, v₀ * v₂, ζ},
        a * b = b * a) ∧
      ∀ a ∈ Subgroup.closure {v₀ * v₁, v₀ * v₂, ζ}, a ^ 2 = 1 := by
  have hab : Commute (v₀ * v₁) (v₀ * v₂) :=
    ((Commute.refl v₀).mul_right h02).mul_left (h01.symm.mul_right h12)
  have haζ : Commute (v₀ * v₁) ζ := hc₀.mul_left hc₁
  have hbζ : Commute (v₀ * v₂) ζ := hc₀.mul_left hc₂
  refine closure_commute_sq _ ?_ ?_
  · rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl)
    · rfl
    · exact hab
    · exact haζ
    · exact hab.symm
    · rfl
    · exact hbζ
    · exact haζ.symm
    · exact hbζ.symm
    · rfl
  · rintro x (rfl | rfl | rfl)
    · rw [Commute.mul_pow h01, pow_two, pow_two, hv₀, hv₁, mul_one]
    · rw [Commute.mul_pow h02, pow_two, pow_two, hv₀, hv₂, mul_one]
    · rwa [pow_two]

structure PairData {α : Type*} (ζ : Perm α) (t : Fin 3 → α) : Prop where
  ζ_ζ : ∀ x, ζ (ζ x) = x
  ne_self : ∀ j, ζ (t j) ≠ t j
  ne : ∀ i j, i ≠ j → t i ≠ t j
  ne_ζ : ∀ i j, i ≠ j → t i ≠ ζ (t j)

section PairSwap

variable {α : Type*} [DecidableEq α]

def pairSwap (ζ : Perm α) (x : α) : Perm α := swap x (ζ x)

theorem pairSwap_mul_self (ζ : Perm α) (x : α) : pairSwap ζ x * pairSwap ζ x = 1 :=
  swap_mul_self _ _

theorem pairSwap_apply_self (ζ : Perm α) (x : α) : pairSwap ζ x x = ζ x := swap_apply_left _ _

theorem pairSwap_apply_ζ (ζ : Perm α) (x : α) : pairSwap ζ x (ζ x) = x := swap_apply_right _ _

theorem pairSwap_commute {ζ : Perm α} (hζ : ∀ x, ζ (ζ x) = x) (x : α) :
    Commute (pairSwap ζ x) ζ := by
  have h : ζ * pairSwap ζ x * ζ⁻¹ = pairSwap ζ x := by
    rw [pairSwap, ← swap_apply_apply, hζ, swap_comm]
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem conj_pairSwap {ζ w : Perm α} (hwζ : ∀ x, w (ζ x) = ζ (w x)) (x : α) :
    w * pairSwap ζ x * w⁻¹ = pairSwap ζ (w x) := by
  rw [pairSwap, pairSwap, ← swap_apply_apply, hwζ]

variable {ζ : Perm α} {t : Fin 3 → α}

theorem PairData.pairSwap_apply_t_of_ne (h : PairData ζ t) {i j : Fin 3} (hij : i ≠ j) :
    pairSwap ζ (t j) (t i) = t i :=
  swap_apply_of_ne_of_ne (h.ne i j hij) (h.ne_ζ i j hij)

theorem PairData.pairSwap_apply_ζt_of_ne (h : PairData ζ t) {i j : Fin 3} (hij : i ≠ j) :
    pairSwap ζ (t j) (ζ (t i)) = ζ (t i) :=
  swap_apply_of_ne_of_ne (h.ne_ζ j i hij.symm).symm (fun e => h.ne i j hij (ζ.injective e))

theorem PairData.pairSwap_mul_comm (h : PairData ζ t) {i j : Fin 3} (hij : i ≠ j) :
    pairSwap ζ (t i) * pairSwap ζ (t j) = pairSwap ζ (t j) * pairSwap ζ (t i) := by
  have e : pairSwap ζ (t i) = pairSwap ζ (t j) * pairSwap ζ (t i) * (pairSwap ζ (t j))⁻¹ := by
    have := swap_apply_apply (pairSwap ζ (t j)) (t i) (ζ (t i))
    rwa [h.pairSwap_apply_t_of_ne hij, h.pairSwap_apply_ζt_of_ne hij] at this
  exact eq_mul_inv_iff_mul_eq.mp e

end PairSwap

theorem pairData_of_orbit {α : Type*} [DecidableEq α] {ζ w : Perm α} (hζ : ∀ x, ζ (ζ x) = x)
    (hwζ : ∀ x, w (ζ x) = ζ (w x)) (hw3 : ∀ x, w (w (w x)) = x) {x : α} (h1 : w x ≠ x)
    (h2 : w x ≠ ζ x) (h3 : ζ x ≠ x) : PairData ζ ![x, w x, w (w x)] := by
  have e_xy : x ≠ w x := h1.symm
  have e_yz : w x ≠ w (w x) := fun h => h1 (w.injective h).symm
  have e_xz : x ≠ w (w x) := fun h => h1 ((congrArg w h).trans (hw3 x))
  have f_y : ζ (w x) ≠ w x := fun h => h3 (w.injective ((hwζ x).trans h))
  have f_z : ζ (w (w x)) ≠ w (w x) := fun h =>
    f_y (w.injective ((hwζ (w x)).trans h))
  have hzz : ζ (w (w x)) = w (w (ζ x)) := by rw [← hwζ (w x), ← hwζ x]
  have g_xy : x ≠ ζ (w x) := fun h => h2 ((congrArg ζ h).trans (hζ (w x))).symm
  have g_xz : x ≠ ζ (w (w x)) := fun h =>
    h2 ((congrArg w (h.trans hzz)).trans (hw3 (ζ x)))
  have g_yz : w x ≠ ζ (w (w x)) := fun h =>
    g_xy ((w.injective (h.trans hzz)).trans (hwζ x))
  have g_zx : w (w x) ≠ ζ x := fun h =>
    g_xy (((hw3 x).symm.trans (congrArg w h)).trans (hwζ x))
  have g_zy : w (w x) ≠ ζ (w x) := fun h => h2 (w.injective (h.trans (hwζ x).symm))
  refine ⟨hζ, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · simpa using h3
    · simpa using f_y
    · simpa using f_z
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [e_xy, e_xy.symm, e_yz, e_yz.symm, e_xz, e_xz.symm] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [g_xy, g_xz, h2, g_yz, g_zx, g_zy] at hij ⊢

theorem PairData.eight_le_card {n : ℕ} {ζ : Perm (Fin n)} {t : Fin 3 → Fin n}
    (h : PairData ζ t) (E : Subgroup (Perm (Fin n)))
    (ha : pairSwap ζ (t 0) * pairSwap ζ (t 1) ∈ E) (hb : pairSwap ζ (t 0) * pairSwap ζ (t 2) ∈ E)
    (hζE : ζ ∈ E) : 8 ≤ Nat.card E := by
  let F : E → Bool × Bool × Bool := fun g =>
    (decide ((g : Perm (Fin n)) (t 0) = t 0), decide ((g : Perm (Fin n)) (t 1) = t 1),
      decide ((g : Perm (Fin n)) (t 2) = t 2))
  have hsurj : Function.Surjective F := by
    rintro ⟨(_ | _), (_ | _), (_ | _)⟩
    · exact ⟨⟨ζ, hζE⟩, by simp [F, h.ne_self]⟩
    · exact ⟨⟨_, ha⟩, by
        simp [F, Perm.mul_apply, h.pairSwap_apply_t_of_ne, h.pairSwap_apply_ζt_of_ne,
          pairSwap_apply_self, h.ne_self]⟩
    · exact ⟨⟨_, hb⟩, by
        simp [F, Perm.mul_apply, h.pairSwap_apply_t_of_ne, h.pairSwap_apply_ζt_of_ne,
          pairSwap_apply_self, h.ne_self]⟩
    · exact ⟨⟨ζ * (_ * _), E.mul_mem hζE (E.mul_mem ha hb)⟩, by
        simp [F, Perm.mul_apply, h.pairSwap_apply_t_of_ne, h.pairSwap_apply_ζt_of_ne,
          pairSwap_apply_self, pairSwap_apply_ζ, h.ζ_ζ, h.ne_self]⟩
    · exact ⟨⟨_ * _, E.mul_mem ha hb⟩, by
        simp [F, Perm.mul_apply, h.pairSwap_apply_t_of_ne, h.pairSwap_apply_ζt_of_ne,
          pairSwap_apply_self, pairSwap_apply_ζ, h.ne_self]⟩
    · exact ⟨⟨ζ * _, E.mul_mem hζE hb⟩, by
        simp [F, Perm.mul_apply, h.pairSwap_apply_t_of_ne, h.pairSwap_apply_ζt_of_ne,
          pairSwap_apply_self, h.ζ_ζ, h.ne_self]⟩
    · exact ⟨⟨ζ * _, E.mul_mem hζE ha⟩, by
        simp [F, Perm.mul_apply, h.pairSwap_apply_t_of_ne, h.pairSwap_apply_ζt_of_ne,
          pairSwap_apply_self, h.ζ_ζ, h.ne_self]⟩
    · exact ⟨⟨1, E.one_mem⟩, by simp [F]⟩
  calc 8 = Nat.card (Bool × Bool × Bool) := by simp
    _ ≤ Nat.card E := Nat.card_le_card_of_surjective F hsurj

end Chain

theorem exists_elemAbelian_of_normal_chain {n : ℕ} (hn : n = 8 ∨ n = 9) {ζ : Perm (Fin n)}
    (hζ : ζ.cycleType = {2, 2, 2, 2}) (Q U : Subgroup (Perm (Fin n)))
    (hQ : ∀ q ∈ Q, Commute q ζ)
    (hQH : ∀ q ∈ Q, ∀ x : Perm (Fin n), Commute x ζ → x * q * x⁻¹ ∈ Q)
    (hUQ : U ≤ Q) (hUnorm : ∀ u ∈ U, ∀ q ∈ Q, q * u * q⁻¹ ∈ U)
    (hζU : ζ ∈ U) {w : Perm (Fin n)} (hwU : w ∈ U) (hw : orderOf w = 3) :
    ∃ E : Subgroup (Perm (Fin n)), E ≤ U ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a ^ 2 = 1) ∧ 8 ≤ Nat.card E := by
  have hn9 : n ≤ 9 := by omega
  have hζζ : ∀ x, ζ (ζ x) = x := Chain.apply_apply_of_cycleType hζ
  have hwζ' : Commute w ζ := hQ w (hUQ hwU)
  have hwζ : ∀ x, w (ζ x) = ζ (w x) := fun x => by
    simpa [Perm.mul_apply] using Perm.ext_iff.mp hwζ' x
  have hw3 : ∀ x, w (w (w x)) = x := fun x => by
    have h3 : w ^ 3 = 1 := hw ▸ pow_orderOf_eq_one w
    simpa [pow_succ, Perm.mul_apply] using Perm.ext_iff.mp h3 x
  obtain ⟨x, h1, h2⟩ : ∃ x, w x ≠ x ∧ w x ≠ ζ x := by
    by_contra hcon
    have hcon' : ∀ x, w x ≠ x → w x = ζ x := fun x hx =>
      by_contra fun hne => hcon ⟨x, hx, hne⟩
    have hsq : ∀ x, w (w x) = x := fun x => by
      by_cases hx : w x = x
      · rw [hx, hx]
      · exact (congrArg w (hcon' x hx)).trans
          ((hwζ x).trans ((congrArg ζ (hcon' x hx)).trans (hζζ x)))
    have hone : w = 1 := Equiv.ext fun x => by
      rw [Perm.one_apply]
      have := hw3 x
      rwa [hsq (w x)] at this
    rw [hone, orderOf_one] at hw
    omega
  have h3 : ζ x ≠ x := fun h =>
    h1 (Chain.eq_of_fixed_of_cycleType hn9 hζ h ((hwζ x).symm.trans (congrArg w h))).symm
  obtain ⟨t, hP, ht0, ht1, ht2⟩ : ∃ t : Fin 3 → Fin n, Chain.PairData ζ t ∧ w (t 0) = t 1 ∧
      w (t 1) = t 2 ∧ w (t 2) = t 0 :=
    ⟨![x, w x, w (w x)], Chain.pairData_of_orbit hζζ hwζ hw3 h1 h2 h3, by simp, by simp,
      by simp [hw3]⟩
  have hw₀ : w * Chain.pairSwap ζ (t 0) * w⁻¹ = Chain.pairSwap ζ (t 1) := by
    rw [Chain.conj_pairSwap hwζ, ht0]
  have hw₁ : w * Chain.pairSwap ζ (t 1) * w⁻¹ = Chain.pairSwap ζ (t 2) := by
    rw [Chain.conj_pairSwap hwζ, ht1]
  have hw₂ : w * Chain.pairSwap ζ (t 2) * w⁻¹ = Chain.pairSwap ζ (t 0) := by
    rw [Chain.conj_pairSwap hwζ, ht2]
  have hv₀ := Chain.pairSwap_mul_self ζ (t 0)
  have hv₁ := Chain.pairSwap_mul_self ζ (t 1)
  have hv₂ := Chain.pairSwap_mul_self ζ (t 2)
  have h01 := hP.pairSwap_mul_comm (i := 0) (j := 1) (by decide)
  have h02 := hP.pairSwap_mul_comm (i := 0) (j := 2) (by decide)
  have h12 := hP.pairSwap_mul_comm (i := 1) (j := 2) (by decide)
  have hc₀ := Chain.pairSwap_commute hζζ (t 0)
  have hc₁ := Chain.pairSwap_commute hζζ (t 1)
  have hc₂ := Chain.pairSwap_commute hζζ (t 2)
  obtain ⟨haU, hbU⟩ := Chain.mul_mem_of_normal_chain hQH hUQ hUnorm hwU hv₀ hv₁ hv₂ h01 h02 h12
    hc₀ hc₁ hw₀ hw₁ hw₂
  have hζ2 : ζ * ζ = 1 := Equiv.ext fun y => by simp [hζζ]
  obtain ⟨hcomm, hsq⟩ := Chain.closure_gen_commute_sq hv₀ hv₁ hv₂ hζ2 h01 h02 h12 hc₀ hc₁ hc₂
  refine ⟨Subgroup.closure {Chain.pairSwap ζ (t 0) * Chain.pairSwap ζ (t 1),
    Chain.pairSwap ζ (t 0) * Chain.pairSwap ζ (t 2), ζ}, ?_, hcomm, hsq, ?_⟩
  · rw [Subgroup.closure_le]
    exact Set.insert_subset_iff.mpr
      ⟨haU, Set.insert_subset_iff.mpr ⟨hbU, Set.singleton_subset_iff.mpr hζU⟩⟩
  · exact hP.eight_le_card _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

end CFSG.GH74.GLS.Stage1.Thm4.L96

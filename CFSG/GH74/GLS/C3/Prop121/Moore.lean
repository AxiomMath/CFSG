module

public import CFSG.GH74.GLS.C3.Prop121.MooreR7c

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.Sporadic.SchreierLemmas

@[expose] def mooreFam {G : Type} [Group G] (n : ℕ) (t x : G) (φ : Perm (Fin (n + 1)) →* G) :
    ℕ → G :=
  fun j => if j = 1 then t else if j = 2 then x else φ (cs n (j - 3))

section

variable {G : Type} [Group G] {n : ℕ} {t x : G} {φ : Perm (Fin (n + 1)) →* G}

theorem mooreFam_one : mooreFam n t x φ 1 = t := by simp [mooreFam]

theorem mooreFam_two : mooreFam n t x φ 2 = x := by simp [mooreFam]

theorem mooreFam_of_ge {j : ℕ} (hj : 3 ≤ j) : mooreFam n t x φ j = φ (cs n (j - 3)) := by
  have h1 : j ≠ 1 := by omega
  have h2 : j ≠ 2 := by omega
  simp [mooreFam, h1, h2]

theorem cs_sq_distant (n : ℕ) {k l : ℕ} (hkl : k + 2 ≤ l) : (cs n k * cs n l) ^ 2 = 1 := by
  calc (cs n k * cs n l) ^ 2 = cs n k * cs n l * (cs n k * cs n l) := sq _
    _ = cs n k * (cs n l * cs n k) * cs n l := by group
    _ = cs n k * (cs n k * cs n l) * cs n l := by rw [(cs_comm n hkl).symm]
    _ = (cs n k * cs n k) * (cs n l * cs n l) := by group
    _ = 1 := by rw [cs_mul_self, cs_mul_self, mul_one]

theorem sq_of_conj_inv {t p : G} (hpp : p * p = 1) (h1 : p * t * p⁻¹ = t⁻¹) : (t * p) ^ 2 = 1 := by
  calc (t * p) ^ 2 = t * (p * t * p⁻¹) * (p * p) := by rw [sq]; group
    _ = 1 := by rw [h1, hpp]; group

theorem sq_of_comm {p : G} (hxx : x * x = 1) (hpp : p * p = 1) (h0 : p * x = x * p) :
    (x * p) ^ 2 = 1 := by
  calc (x * p) ^ 2 = x * (p * x) * p := by rw [sq]; group
    _ = (x * x) * (p * p) := by rw [h0]; group
    _ = 1 := by rw [hxx, hpp]; group

end

theorem isMooreFamily_of_ctx
    {G : Type} [Group G] {n : ℕ} {x : G} {K Q : Subgroup G} {t u g : G}
    {L : Subgroup G} {φ : Perm (Fin (n + 1)) →* G} (h : MCtx n x K Q t u g L φ) :
    IsMooreFamily (n + 2) (mooreFam n t x φ) := by
  have hφmm : ∀ k, φ (cs n k) * φ (cs n k) = 1 := fun k => by
    rw [← map_mul, cs_mul_self, map_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mooreFam_one]
    have := pow_orderOf_eq_one t
    rwa [h.S.t_order] at this
  · intro j hj2 hjn
    rcases Nat.lt_or_ge j 3 with hj | hj
    · have : j = 2 := by omega
      subst this
      rw [mooreFam_two]
      exact h.S.x_sq
    · rw [mooreFam_of_ge hj, sq]
      exact hφmm _
  · intro j hj2 hjn
    rcases Nat.lt_or_ge j 4 with hj | hj
    · rcases Nat.lt_or_ge j 3 with hj' | hj'
      · have : j = 2 := by omega
        subst this
        show (mooreFam n t x φ 1 * mooreFam n t x φ 2) ^ 3 = 1
        rw [mooreFam_one, mooreFam_two]
        exact h.S.tx_cube
      · have : j = 3 := by omega
        subst this
        show (mooreFam n t x φ 2 * mooreFam n t x φ 3) ^ 3 = 1
        rw [mooreFam_two, mooreFam_of_ge le_rfl]
        exact h.R7
    · have e1 : mooreFam n t x φ (j - 1) = φ (cs n (j - 4)) := by
        rw [mooreFam_of_ge (by omega : 3 ≤ j - 1), show j - 1 - 3 = j - 4 by omega]
      rw [e1, mooreFam_of_ge (by omega : 3 ≤ j), ← map_mul, ← map_pow,
        show j - 3 = j - 4 + 1 by omega, cs_braid n (by omega : j - 4 + 1 < n), map_one]
  · intro i j hi1 hij hjn
    have hj3 : 3 ≤ j := by omega
    rw [mooreFam_of_ge hj3]
    have hjn' : j - 3 < n := by omega
    rcases Nat.lt_or_ge i 2 with hi | hi
    · have : i = 1 := by omega
      subst this
      rw [mooreFam_one]
      exact sq_of_conj_inv (hφmm _) (h.odd_inv_t (sign_cs hjn'))
    · rcases Nat.lt_or_ge i 3 with hi' | hi'
      · have : i = 2 := by omega
        subst this
        rw [mooreFam_two]
        exact sq_of_comm h.x_mul_self (hφmm _)
          (h.stab_comm_x (cs_apply_zero (by omega : 1 ≤ j - 3)))
      · rw [mooreFam_of_ge hi', ← map_mul, ← map_pow, cs_sq_distant n (by omega : i - 3 + 2 ≤ j - 3),
          map_one]

theorem exists_moore_of_threeLocal
    {G : Type} [Group G] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7)
    {x : G} {K Q : Subgroup G} {t u g : G} (hS : Stage3Loc n x K Q t u g) {L : Subgroup G}
    {Θ : ↥(L ⊔ zpowers u) ≃* Perm (Fin (n + 1))} (hL : ThreeLocal n K t u g L Θ) :
    ∃ y : ℕ → G, IsMooreFamily (n + 2) y ∧ y 1 ≠ 1 := by
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl | rfl <;> norm_num
  obtain ⟨φ, hφ, hc⟩ := exists_phi hn3 hS hL
  have h : MCtx n x K Q t u g L φ := ⟨hn, hS, hL.toThreeLocalCore, hφ, hc⟩
  refine ⟨mooreFam n t x φ, isMooreFamily_of_ctx h, ?_⟩
  rw [mooreFam_one]
  intro ht
  have h3 := hS.t_order
  rw [ht, orderOf_one] at h3
  exact absurd h3 (by norm_num)

end CFSG.GH74.GLS.C3.Prop121

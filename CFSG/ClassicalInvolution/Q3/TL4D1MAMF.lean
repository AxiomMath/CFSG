module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAMC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Generic Wr Equiv

variable {n : ℕ}

theorem pair_eq_of_modPi (hn : 5 ≤ n) {σ : Perm (Fin n)} {a b : Fin n} (hab : a ≠ b)
    (h : ModPi (pairVec (σ a) (σ b)) (pairVec a b)) :
    (σ a = a ∨ σ a = b) ∧ (σ b = a ∨ σ b = b) := by
  obtain ⟨d, h1, h2, h3, h4⟩ := exists_ne_four hn a b (σ a) (σ b)
  have hσab : σ a ≠ σ b := fun e => hab (σ.injective e)
  have heq : pairVec (σ a) (σ b) = pairVec a b := by
    rcases h with h | h
    · exact h
    · exfalso
      have := congrFun h d
      simp [pairVec_apply, h1, h2, h3, h4] at this
  constructor
  · by_contra hne
    push Not at hne
    have := congrFun heq (σ a)
    simp [pairVec_apply, hσab, hne.1, hne.2] at this
  · by_contra hne
    push Not at hne
    have := congrFun heq (σ b)
    simp [pairVec_apply, hσab.symm, hne.1, hne.2] at this

theorem modPi_of_add_modPi_zero {x y : Fin n → ZMod 2} (h : ModPi (x + y) 0) : ModPi y x := by
  rcases h with h | h
  · left
    funext i
    have h' := congrFun h i
    revert h'
    show x i + y i = 0 → y i = x i
    generalize x i = c
    generalize y i = d
    revert c d
    decide
  · right
    funext i
    have h' := congrFun h i
    revert h'
    show x i + y i = 0 + 1 → y i = x i + 1
    generalize x i = c
    generalize y i = d
    revert c d
    decide

theorem pairVec_comm (j k : Fin n) : pairVec j k = pairVec k j := add_comm _ _

theorem vbar_conj (p : Fin n → ZMod 2) (z : AEQ n) :
    vbar n p * z * (vbar n p)⁻¹ = vbar n (p + actV (permBar n z) p) * z := by
  have hinv : (vbar n p)⁻¹ = vbar n p :=
    inv_eq_of_mul_eq_one_right (by rw [← vbar_add, add_self_vec, vbar_zero])
  rw [vbar_add, ← conj_vbar (g := z) rfl, hinv]
  group

theorem comm_apply_of_preserve {s t : Perm (Fin n)} {a b : Fin n} (hab : a ≠ b)
    (hs : (s a = a ∨ s a = b) ∧ (s b = a ∨ s b = b))
    (ht : (t a = a ∨ t a = b) ∧ (t b = a ∨ t b = b)) : s (t a) = t (s a) := by
  have hsab : s a ≠ s b := fun e => hab (s.injective e)
  have htab : t a ≠ t b := fun e => hab (t.injective e)
  obtain ⟨h1 | h1, h2 | h2⟩ := hs
  · exact absurd (h1.trans h2.symm) hsab
  · obtain ⟨h3 | h3, -⟩ := ht
    · rw [h3, h1, h3]
    · rw [h3, h2, h1, h3]
  · obtain ⟨h3 | h3, h4 | h4⟩ := ht
    · exact absurd (h3.trans h4.symm) htab
    · rw [h3, h1, h4]
    · rw [h3, h2, h1, h4]
    · exact absurd (h3.trans h4.symm) htab
  · exact absurd (h1.trans h2.symm) hsab

theorem permBar_eq_one_of_conj (hn : 5 ≤ n) {P : Subgroup (Perm (Fin n))}
    {B : Subgroup (AEQ n)} {w : AEQ n} (hw2 : w * w = 1)
    (hBv : ∀ x ∈ B, permBar n x = 1 → x = 1 ∨ x = w)
    {x y : AEQ n} (hx : x ∈ B) (hy : y ∈ B) (hxy : x * y = w * (y * x))
    (h9 : ∀ g ∈ aeBarOver P, g * w = w * g → conjSub g B = B ∨ Commutes B (conjSub g B)) :
    permBar n w = 1 := by
  obtain ⟨τ, hτw⟩ : ∃ τ, permBar n w = τ := ⟨_, rfl⟩
  rw [hτw]
  by_contra hτ1
  have hτ2 : τ * τ = 1 := by rw [← hτw, ← map_mul, hw2, map_one]
  obtain ⟨a, ha⟩ : ∃ a, τ a ≠ a := by
    by_contra h
    push Not at h
    exact hτ1 (Equiv.ext h)
  have hττ : τ (τ a) = a := apply_apply_of_mul_self hτ2 a
  have hgM : vbar n (pairVec a (τ a)) ∈ aeBarOver P := vbar_mem_aeBarOver (sum_pairVec a (τ a))
  have hgw : vbar n (pairVec a (τ a)) * w = w * vbar n (pairVec a (τ a)) := by
    have h1 := conj_vbar hτw (pairVec a (τ a))
    rw [actV_pairVec, hττ, pairVec_comm (τ a) a] at h1
    calc vbar n (pairVec a (τ a)) * w = w * vbar n (pairVec a (τ a)) * w⁻¹ * w := by rw [h1]
      _ = w * vbar n (pairVec a (τ a)) := by group
  rcases h9 _ hgM hgw with h | h
  · have key : ∀ z ∈ B, (permBar n z a = a ∨ permBar n z a = τ a) ∧
        (permBar n z (τ a) = a ∨ permBar n z (τ a) = τ a) := by
      intro z hz
      have hm : vbar n (pairVec a (τ a)) * z * (vbar n (pairVec a (τ a)))⁻¹ ∈ B := by
        rw [← h]
        exact conj_mem_conjSub hz
      rw [vbar_conj] at hm
      have hm2 := B.mul_mem hm (B.inv_mem hz)
      rw [mul_inv_cancel_right] at hm2
      rcases hBv _ hm2 (permBar_vbar _) with h1 | h1
      · rw [← vbar_zero, vbar_eq_iff, actV_pairVec] at h1
        exact pair_eq_of_modPi hn (Ne.symm ha) (modPi_of_add_modPi_zero h1)
      · exfalso
        have := congrArg (permBar n) h1
        rw [permBar_vbar, hτw] at this
        exact hτ1 this.symm
    have hs := key x hx
    have ht := key y hy
    have hc := comm_apply_of_preserve (Ne.symm ha) hs ht
    have h5 : permBar n x (permBar n y a) = τ (permBar n y (permBar n x a)) := by
      rw [← Perm.mul_apply, ← map_mul, hxy, map_mul, map_mul, hτw, Perm.mul_apply,
        Perm.mul_apply]
    rw [hc] at h5
    have hmem : permBar n y (permBar n x a) = a ∨ permBar n y (permBar n x a) = τ a := by
      rcases hs.1 with h1 | h1 <;> rw [h1]
      · exact ht.1
      · exact ht.2
    rcases hmem with h6 | h6 <;> rw [h6] at h5
    · exact ha h5.symm
    · rw [hττ] at h5
      exact ha h5
  · have hc := h x hx _ (conj_mem_conjSub (n := vbar n (pairVec a (τ a))) hy)
    rw [vbar_conj] at hc
    have e2 : ∀ q : Fin n → ZMod 2, x * vbar n q = vbar n (actV (permBar n x) q) * x :=
      fun q => by rw [← conj_vbar (g := x) rfl]; group
    have e3 : vbar n (actV (permBar n x) (pairVec a (τ a) +
        actV (permBar n y) (pairVec a (τ a)))) * w =
        vbar n (pairVec a (τ a) + actV (permBar n y) (pairVec a (τ a))) := by
      refine mul_right_cancel (b := y * x) ?_
      rw [mul_assoc, ← hxy, ← mul_assoc, ← e2, mul_assoc, hc, mul_assoc]
    have := congrArg (permBar n) e3
    rw [map_mul, permBar_vbar, permBar_vbar, one_mul, hτw] at this
    exact hτ1 this

end CFSG.ClassicalInvolution.Q3.TL4

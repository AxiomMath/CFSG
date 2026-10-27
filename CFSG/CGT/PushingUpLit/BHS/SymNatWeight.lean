module

public import CFSG.CGT.PushingUpLit.BHS.SymNatBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6

variable {n : ℕ}

theorem two_mul_lt_two_pow (s : ℕ) (hs : 3 ≤ s) : 2 * s < 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ]
    have h2 : 2 ≤ 2 ^ s :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem two_mul_le_two_pow (s : ℕ) : 2 * s ≤ 2 ^ s := by
  rcases Nat.lt_or_ge s 3 with h | h
  · interval_cases s <;> norm_num
  · exact (two_mul_lt_two_pow s h).le

theorem fix_of_fix_orbRep {A : Subgroup (Equiv.Perm (Fin n))}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {b : Equiv.Perm (Fin n)} (hb : b ∈ A) {z : Fin n}
    (h : b (orbRep A (orbOf A z)) = orbRep A (orbOf A z)) : b z = z := by
  obtain ⟨c, hcA, hcz⟩ := orbOf_eq_iff.1 (orbOf_orbRep A (orbOf A z)).symm
  have hbc : b (c (orbRep A (orbOf A z))) = c (b (orbRep A (orbOf A z))) := by
    have := congrArg (fun t : Equiv.Perm (Fin n) => t (orbRep A (orbOf A z))) (hc b hb c hcA)
    simpa only [Equiv.Perm.mul_apply] using this
  rw [← hcz, hbc, h]

@[expose] noncomputable def evRep (A : Subgroup (Equiv.Perm (Fin n))) (a : A) :
    (q : OrbQ A) → {x : Fin n // orbOf A x = q} := fun q =>
  ⟨(a : Equiv.Perm (Fin n)) (orbRep A q), by rw [orbOf_apply a.2, orbOf_orbRep]⟩

theorem evRep_injective {A : Subgroup (Equiv.Perm (Fin n))}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Function.Injective (evRep A) := by
  intro a b hab
  refine Subtype.ext (Equiv.ext fun x => ?_)
  have h1 : ∀ q, (a : Equiv.Perm (Fin n)) (orbRep A q) = (b : Equiv.Perm (Fin n)) (orbRep A q) :=
    fun q => congrArg Subtype.val (congrFun hab q)
  have h2 : ((b : Equiv.Perm (Fin n))⁻¹ * (a : Equiv.Perm (Fin n))) x = x := by
    refine fix_of_fix_orbRep hc (A.mul_mem (A.inv_mem b.2) a.2) ?_
    rw [Equiv.Perm.mul_apply, h1, perm_inv_apply_self]
  have h3 : (b : Equiv.Perm (Fin n))⁻¹ ((a : Equiv.Perm (Fin n)) x) = x := h2
  have h4 := congrArg (fun t => (b : Equiv.Perm (Fin n)) t) h3
  rwa [perm_apply_inv_self] at h4

theorem card_le_prod_orbSize {A : Subgroup (Equiv.Perm (Fin n))}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card A ≤ ∏ q : OrbQ A, orbSize A q := by
  have h := Nat.card_le_card_of_injective _ (evRep_injective hc)
  rw [Nat.card_pi] at h
  exact h

theorem two_mul_weight_le (hn : Odd n) {A : Subgroup (Equiv.Perm (Fin n))}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    2 * (Nat.card A * Nat.card (fixV (A.map (coreAct n)))) ≤ ∏ q : OrbQ A, (2 * orbSize A q) := by
  have h1 := card_fixV_mul_two hn A
  have h2 := card_le_prod_orbSize hc
  calc 2 * (Nat.card A * Nat.card (fixV (A.map (coreAct n))))
      = Nat.card A * 2 ^ Nat.card (OrbQ A) := by rw [← h1]; ring
    _ ≤ (∏ q : OrbQ A, orbSize A q) * 2 ^ Nat.card (OrbQ A) := Nat.mul_le_mul_right _ h2
    _ = ∏ q : OrbQ A, (2 * orbSize A q) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          ← Nat.card_eq_fintype_card, mul_comm]

theorem prod_two_mul_le_two_pow (A : Subgroup (Equiv.Perm (Fin n))) :
    ∏ q : OrbQ A, (2 * orbSize A q) ≤ 2 ^ n := by
  calc ∏ q : OrbQ A, (2 * orbSize A q) ≤ ∏ q : OrbQ A, 2 ^ orbSize A q :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) fun q _ => two_mul_le_two_pow _
    _ = 2 ^ ∑ q : OrbQ A, orbSize A q := Finset.prod_pow_eq_pow_sum _ _ _
    _ = 2 ^ n := by rw [sum_orbSize]

theorem weight_le (hn : Odd n) {A : Subgroup (Equiv.Perm (Fin n))}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A * Nat.card (fixV (A.map (coreAct n))) ≤ Nat.card (coreMod n) := by
  have h1 := two_mul_weight_le hn hc
  have h2 := prod_two_mul_le_two_pow A
  have h3 := card_coreMod_mul_two hn
  omega

theorem weight_eq_of_ge (hn : Odd n) {A : Subgroup (Equiv.Perm (Fin n))}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hge : Nat.card (coreMod n) ≤ Nat.card A * Nat.card (fixV (A.map (coreAct n)))) :
    (∀ q : OrbQ A, orbSize A q ≤ 2) ∧ Nat.card A = ∏ q : OrbQ A, orbSize A q ∧
      Nat.card A * Nat.card (fixV (A.map (coreAct n))) = Nat.card (coreMod n) := by
  have h1 := two_mul_weight_le hn hc
  have h2 := prod_two_mul_le_two_pow A
  have h3 := card_coreMod_mul_two hn
  have h4 := weight_le hn hc
  have hP : ∏ q : OrbQ A, (2 * orbSize A q) = 2 ^ n := by omega
  have hP' : ∏ q : OrbQ A, (2 * orbSize A q) = ∏ q : OrbQ A, 2 ^ orbSize A q := by
    rw [Finset.prod_pow_eq_pow_sum, sum_orbSize]
    exact hP
  have hsmall : ∀ q : OrbQ A, orbSize A q ≤ 2 := by
    intro q
    by_contra hlt
    push Not at hlt
    have hlt' := Finset.prod_lt_prod₀ (s := Finset.univ) (f := fun q : OrbQ A => 2 * orbSize A q)
      (g := fun q : OrbQ A => 2 ^ orbSize A q)
      (fun q _ => Nat.mul_pos (by norm_num) (orbSize_pos A q))
      (fun q _ => two_mul_le_two_pow _)
      ⟨q, Finset.mem_univ q, two_mul_lt_two_pow _ hlt⟩
    exact absurd hP' (ne_of_lt hlt')
  have hweq : Nat.card A * Nat.card (fixV (A.map (coreAct n))) = Nat.card (coreMod n) :=
    le_antisymm h4 hge
  refine ⟨hsmall, ?_, hweq⟩
  have hpos : 0 < 2 ^ Nat.card (OrbQ A) := pow_pos (by norm_num) _
  have hfix := card_fixV_mul_two hn A
  have hcard := card_le_prod_orbSize hc
  have hprod : ∏ q : OrbQ A, (2 * orbSize A q) =
      (∏ q : OrbQ A, orbSize A q) * 2 ^ Nat.card (OrbQ A) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, mul_comm]
  have hmul : Nat.card A * 2 ^ Nat.card (OrbQ A) =
      (∏ q : OrbQ A, orbSize A q) * 2 ^ Nat.card (OrbQ A) := by
    rw [← hprod, hP, ← hfix]
    nlinarith
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

theorem three_le_orbSize {A : Subgroup (Equiv.Perm (Fin n))} {q : OrbQ A} {x y z : Fin n}
    (hx : orbOf A x = q) (hy : orbOf A y = q) (hz : orbOf A z = q) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : 3 ≤ orbSize A q := by
  let g : Fin 3 → {w : Fin n // orbOf A w = q} := ![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩]
  have hg : Function.Injective g := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [g]
  have := Nat.card_le_card_of_injective g hg
  simpa [orbSize] using this

theorem eq_or_eq_of_orbSize_le_two {A : Subgroup (Equiv.Perm (Fin n))} {q : OrbQ A}
    (h : orbSize A q ≤ 2) {x y z : Fin n} (hx : orbOf A x = q) (hy : orbOf A y = q)
    (hz : orbOf A z = q) (hxy : x ≠ y) : z = x ∨ z = y := by
  by_contra hne
  push Not at hne
  have := three_le_orbSize hx hy hz hxy (Ne.symm hne.1) (Ne.symm hne.2)
  omega

end CFSG.CGT.PushingUpLit.BHS

module

public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpCount

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421OmCountProof

theorem card_norm_one_general_aux1 {F : Type} [Field F] {b c s β : F}
    (h : β ^ 2 * (s ^ 2 + b * s + c) = 1) :
    (s * β) ^ 2 + b * (s * β) * β + c * β ^ 2 = 1 := by
  linear_combination h

theorem card_norm_one_general {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {p : F × F // p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = 1} = Nat.card F + 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  choose r hr using K421SpCountProof.spc_sq_exists (F := F)
  have hbij : Function.Bijective (fun o : Option F =>
      o.elim (⟨(1, 0), by simp⟩ : {p : F × F // p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = 1})
        (fun s => ⟨(s * r (s ^ 2 + b * s + c)⁻¹, r (s ^ 2 + b * s + c)⁻¹),
          card_norm_one_general_aux1 (s := s) (β := r (s ^ 2 + b * s + c)⁻¹)
            (by rw [hr, inv_mul_cancel₀ (hirr s)])⟩)) := by
    refine ⟨?_, ?_⟩
    · rintro (_ | s) (_ | t) h
      · rfl
      · exfalso
        have h2 : (0 : F) = r (t ^ 2 + b * t + c)⁻¹ :=
          congrArg (fun p : {p : F × F // p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = 1} => p.1.2) h
        have h3 := hr (t ^ 2 + b * t + c)⁻¹
        rw [← h2, zero_pow two_ne_zero] at h3
        exact inv_ne_zero (hirr t) h3.symm
      · exfalso
        have h2 : r (s ^ 2 + b * s + c)⁻¹ = 0 :=
          congrArg (fun p : {p : F × F // p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = 1} => p.1.2) h
        have h3 := hr (s ^ 2 + b * s + c)⁻¹
        rw [h2, zero_pow two_ne_zero] at h3
        exact inv_ne_zero (hirr s) h3.symm
      · have h1 : s * r (s ^ 2 + b * s + c)⁻¹ = t * r (t ^ 2 + b * t + c)⁻¹ :=
          congrArg (fun p : {p : F × F // p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = 1} => p.1.1) h
        have h2 : r (s ^ 2 + b * s + c)⁻¹ = r (t ^ 2 + b * t + c)⁻¹ :=
          congrArg (fun p : {p : F × F // p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = 1} => p.1.2) h
        rw [← h2] at h1
        have hne : r (s ^ 2 + b * s + c)⁻¹ ≠ 0 := by
          intro h0
          have h3 := hr (s ^ 2 + b * s + c)⁻¹
          rw [h0, zero_pow two_ne_zero] at h3
          exact inv_ne_zero (hirr s) h3.symm
        rw [mul_right_cancel₀ hne h1]
    · rintro ⟨⟨a, d⟩, hp⟩
      change a ^ 2 + b * a * d + c * d ^ 2 = 1 at hp
      by_cases hd0 : d = 0
      · have ha2 : a ^ 2 = 1 ^ 2 := by
          rw [hd0] at hp
          linear_combination hp
        have ha : a = 1 := K421SpCountProof.spc_sq_inj ha2
        refine ⟨none, Subtype.ext (Prod.ext ?_ ?_)⟩
        · exact ha.symm
        · exact hd0.symm
      · obtain ⟨s, hs⟩ : ∃ s : F, s = a / d := ⟨_, rfl⟩
        have hsd : s * d = a := by
          rw [hs]
          exact div_mul_cancel₀ a hd0
        have hb2 : d ^ 2 * (s ^ 2 + b * s + c) = 1 := by
          linear_combination hp + (s * d + a + b * d) * hsd
        have hbinv : d ^ 2 = (s ^ 2 + b * s + c)⁻¹ := eq_inv_of_mul_eq_one_left hb2
        have hrd : r (s ^ 2 + b * s + c)⁻¹ = d :=
          K421SpCountProof.spc_sq_inj ((hr (s ^ 2 + b * s + c)⁻¹).trans hbinv.symm)
        refine ⟨some s, Subtype.ext (Prod.ext ?_ ?_)⟩
        · show s * r (s ^ 2 + b * s + c)⁻¹ = a
          rw [hrd]
          exact hsd
        · show r (s ^ 2 + b * s + c)⁻¹ = d
          exact hrd
  rw [← Nat.card_eq_of_bijective _ hbij, Finite.card_option]

theorem card_quadMinus_eq_one_aux1 {F : Type} [Field F] {b c : F}
    (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    CFSG.Open.StatedQuadMinus 4 F b c v = ∑ i : Fin 3, v (.inl i) * v (.inr (.inl i)) +
      (v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        c * v (.inr (.inr 1)) ^ 2) := by
  change (∑ i : Fin 3, v (.inl i) * v (.inr (.inl i))) + v (.inr (.inr 0)) ^ 2 +
    b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 = _
  ring

theorem card_quadMinus_eq_one_aux2 {F : Type} [Field F] (x : Fin 3 → F) (m : F) (h0 : x 0 ≠ 0)
    (a d : F) : ∑ i, x i * ![(1 - m - x 1 * a - x 2 * d) / x 0, a, d] i + m = 1 := by
  rw [Fin.sum_univ_three]
  have key : x 0 * ((1 - m - x 1 * a - x 2 * d) / x 0) = 1 - m - x 1 * a - x 2 * d := by
    rw [mul_comm (x 0)]
    exact div_mul_cancel₀ _ h0
  show x 0 * ((1 - m - x 1 * a - x 2 * d) / x 0) + x 1 * a + x 2 * d + m = 1
  linear_combination key

theorem card_quadMinus_eq_one_aux3 {F : Type} [Field F] (x : Fin 3 → F) (m : F) (h1 : x 1 ≠ 0)
    (a d : F) : ∑ i, x i * ![a, (1 - m - x 0 * a - x 2 * d) / x 1, d] i + m = 1 := by
  rw [Fin.sum_univ_three]
  have key : x 1 * ((1 - m - x 0 * a - x 2 * d) / x 1) = 1 - m - x 0 * a - x 2 * d := by
    rw [mul_comm (x 1)]
    exact div_mul_cancel₀ _ h1
  show x 0 * a + x 1 * ((1 - m - x 0 * a - x 2 * d) / x 1) + x 2 * d + m = 1
  linear_combination key

theorem card_quadMinus_eq_one_aux4 {F : Type} [Field F] (x : Fin 3 → F) (m : F) (h2 : x 2 ≠ 0)
    (a d : F) : ∑ i, x i * ![a, d, (1 - m - x 0 * a - x 1 * d) / x 2] i + m = 1 := by
  rw [Fin.sum_univ_three]
  have key : x 2 * ((1 - m - x 0 * a - x 1 * d) / x 2) = 1 - m - x 0 * a - x 1 * d := by
    rw [mul_comm (x 2)]
    exact div_mul_cancel₀ _ h2
  show x 0 * a + x 1 * d + x 2 * ((1 - m - x 0 * a - x 1 * d) / x 2) + m = 1
  linear_combination key

theorem card_quadMinus_eq_one_aux5 {F : Type} [Field F] [Finite F] (x : Fin 3 → F) (m : F)
    (h : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0) :
    Nat.card {y : Fin 3 → F // ∑ i, x i * y i + m = 1} = Nat.card F ^ 2 := by
  rcases h with h0 | h1 | h2
  · have hf : Function.Bijective (fun q : F × F =>
        (⟨![(1 - m - x 1 * q.1 - x 2 * q.2) / x 0, q.1, q.2],
          card_quadMinus_eq_one_aux2 x m h0 q.1 q.2⟩ :
            {y : Fin 3 → F // ∑ i, x i * y i + m = 1})) := by
      refine ⟨?_, ?_⟩
      · rintro ⟨a, d⟩ ⟨a', d'⟩ hh
        have e1 : a = a' :=
          congrArg (fun y : {y : Fin 3 → F // ∑ i, x i * y i + m = 1} => y.1 1) hh
        have e2 : d = d' :=
          congrArg (fun y : {y : Fin 3 → F // ∑ i, x i * y i + m = 1} => y.1 2) hh
        rw [e1, e2]
      · rintro ⟨y, hy⟩
        rw [Fin.sum_univ_three] at hy
        refine ⟨(y 1, y 2), Subtype.ext (funext fun j => ?_)⟩
        fin_cases j
        · show (1 - m - x 1 * y 1 - x 2 * y 2) / x 0 = y 0
          exact (div_eq_iff h0).2 (by linear_combination (-1 : F) * hy)
        · rfl
        · rfl
    rw [← Nat.card_eq_of_bijective _ hf, Nat.card_prod, sq]
  · have hf : Function.Bijective (fun q : F × F =>
        (⟨![q.1, (1 - m - x 0 * q.1 - x 2 * q.2) / x 1, q.2],
          card_quadMinus_eq_one_aux3 x m h1 q.1 q.2⟩ :
            {y : Fin 3 → F // ∑ i, x i * y i + m = 1})) := by
      refine ⟨?_, ?_⟩
      · rintro ⟨a, d⟩ ⟨a', d'⟩ hh
        have e1 : a = a' :=
          congrArg (fun y : {y : Fin 3 → F // ∑ i, x i * y i + m = 1} => y.1 0) hh
        have e2 : d = d' :=
          congrArg (fun y : {y : Fin 3 → F // ∑ i, x i * y i + m = 1} => y.1 2) hh
        rw [e1, e2]
      · rintro ⟨y, hy⟩
        rw [Fin.sum_univ_three] at hy
        refine ⟨(y 0, y 2), Subtype.ext (funext fun j => ?_)⟩
        fin_cases j
        · rfl
        · show (1 - m - x 0 * y 0 - x 2 * y 2) / x 1 = y 1
          exact (div_eq_iff h1).2 (by linear_combination (-1 : F) * hy)
        · rfl
    rw [← Nat.card_eq_of_bijective _ hf, Nat.card_prod, sq]
  · have hf : Function.Bijective (fun q : F × F =>
        (⟨![q.1, q.2, (1 - m - x 0 * q.1 - x 1 * q.2) / x 2],
          card_quadMinus_eq_one_aux4 x m h2 q.1 q.2⟩ :
            {y : Fin 3 → F // ∑ i, x i * y i + m = 1})) := by
      refine ⟨?_, ?_⟩
      · rintro ⟨a, d⟩ ⟨a', d'⟩ hh
        have e1 : a = a' :=
          congrArg (fun y : {y : Fin 3 → F // ∑ i, x i * y i + m = 1} => y.1 0) hh
        have e2 : d = d' :=
          congrArg (fun y : {y : Fin 3 → F // ∑ i, x i * y i + m = 1} => y.1 1) hh
        rw [e1, e2]
      · rintro ⟨y, hy⟩
        rw [Fin.sum_univ_three] at hy
        refine ⟨(y 0, y 1), Subtype.ext (funext fun j => ?_)⟩
        fin_cases j
        · rfl
        · rfl
        · show (1 - m - x 0 * y 0 - x 1 * y 1) / x 2 = y 2
          exact (div_eq_iff h2).2 (by linear_combination (-1 : F) * hy)
    rw [← Nat.card_eq_of_bijective _ hf, Nat.card_prod, sq]

theorem card_quadMinus_eq_one_aux6 {F : Type} [Finite F] :
    Nat.card (Fin 3 → F) = Nat.card F ^ 3 := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

theorem card_quadMinus_eq_one_aux7 {F : Type} [Field F] [Finite F] {b c : F} {x : Fin 3 → F}
    (hx : x ≠ 0) :
    Nat.card {q : (Fin 3 → F) × (F × F) //
      ∑ i, x i * q.1 i + (q.2.1 ^ 2 + b * q.2.1 * q.2.2 + c * q.2.2 ^ 2) = 1} =
      Nat.card F ^ 4 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    exact hx (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2.1, hcon.2.2])
  have hfib : ∀ m : F, Nat.card {y : Fin 3 → F // ∑ i, x i * y i + m = 1} = Nat.card F ^ 2 :=
    fun m => card_quadMinus_eq_one_aux5 x m hx'
  let Ψ : {q : (Fin 3 → F) × (F × F) //
      ∑ i, x i * q.1 i + (q.2.1 ^ 2 + b * q.2.1 * q.2.2 + c * q.2.2 ^ 2) = 1} ≃
      Σ uw : F × F, {y : Fin 3 → F //
        ∑ i, x i * y i + (uw.1 ^ 2 + b * uw.1 * uw.2 + c * uw.2 ^ 2) = 1} :=
    { toFun := fun q => ⟨q.1.2, ⟨q.1.1, q.2⟩⟩
      invFun := fun s => ⟨(s.2.1, s.1), s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr Ψ, Nat.card_sigma]
  simp only [hfib]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_prod,
    smul_eq_mul]
  ring

theorem card_quadMinus_eq_one_aux8 {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {q : (Fin 3 → F) × (F × F) //
      ∑ i, (0 : Fin 3 → F) i * q.1 i + (q.2.1 ^ 2 + b * q.2.1 * q.2.2 + c * q.2.2 ^ 2) = 1} =
      Nat.card F ^ 3 * (Nat.card F + 1) := by
  let e : {q : (Fin 3 → F) × (F × F) //
      ∑ i, (0 : Fin 3 → F) i * q.1 i + (q.2.1 ^ 2 + b * q.2.1 * q.2.2 + c * q.2.2 ^ 2) = 1} ≃
      (Fin 3 → F) × {uw : F × F // uw.1 ^ 2 + b * uw.1 * uw.2 + c * uw.2 ^ 2 = 1} :=
    { toFun := fun q => (q.1.1, ⟨q.1.2, by simpa using q.2⟩)
      invFun := fun p => ⟨(p.1, p.2.1), by simpa using p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_norm_one_general hirr, card_quadMinus_eq_one_aux6]

theorem card_quadMinus_eq_one_aux9 (Q : ℕ) (hQ : 0 < Q) :
    Q ^ 3 * (Q + 1) + (Q ^ 3 - 1) * Q ^ 4 = Q ^ 7 + Q ^ 3 := by
  obtain ⟨k, hk⟩ : ∃ k, Q ^ 3 = k + 1 := ⟨Q ^ 3 - 1, by have := pow_pos hQ 3; omega⟩
  rw [hk, Nat.add_sub_cancel]
  have h7 : Q ^ 7 = Q ^ 4 * (k + 1) := by rw [← hk]; ring
  have h4 : (k + 1) * Q = Q ^ 4 := by rw [← hk]; ring
  rw [h7]
  nlinarith [h4]

theorem card_quadMinus_eq_one {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F // CFSG.Open.StatedQuadMinus 4 F b c v = 1} =
      Nat.card F ^ 7 + Nat.card F ^ 3 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hQ : 0 < Nat.card F := Nat.card_pos
  let Φ : {v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F // CFSG.Open.StatedQuadMinus 4 F b c v = 1} ≃
      Σ x : Fin 3 → F, {q : (Fin 3 → F) × (F × F) //
        ∑ i, x i * q.1 i + (q.2.1 ^ 2 + b * q.2.1 * q.2.2 + c * q.2.2 ^ 2) = 1} :=
    { toFun := fun v => ⟨fun i => v.1 (.inl i),
        ⟨(fun i => v.1 (.inr (.inl i)), (v.1 (.inr (.inr 0)), v.1 (.inr (.inr 1)))), by
          have h := v.2
          rw [card_quadMinus_eq_one_aux1] at h
          exact h⟩⟩
      invFun := fun s => ⟨Sum.elim s.1 (Sum.elim s.2.1.1 ![s.2.1.2.1, s.2.1.2.2]), by
          rw [card_quadMinus_eq_one_aux1]
          exact s.2.2⟩
      left_inv := fun v => Subtype.ext (funext fun j => by
          rcases j with j | j | j
          · rfl
          · rfl
          · fin_cases j <;> rfl)
      right_inv := fun _ => rfl }
  have hsum : ∑ x ∈ Finset.univ.erase (0 : Fin 3 → F), Nat.card {q : (Fin 3 → F) × (F × F) //
      ∑ i, x i * q.1 i + (q.2.1 ^ 2 + b * q.2.1 * q.2.2 + c * q.2.2 ^ 2) = 1} =
      (Finset.univ.erase (0 : Fin 3 → F)).card * Nat.card F ^ 4 :=
    Finset.sum_const_nat fun x hx => card_quadMinus_eq_one_aux7 (Finset.ne_of_mem_erase hx)
  rw [Nat.card_congr Φ, Nat.card_sigma,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin 3 → F)), hsum,
    card_quadMinus_eq_one_aux8 hirr, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ← Nat.card_eq_fintype_card, card_quadMinus_eq_one_aux6]
  exact card_quadMinus_eq_one_aux9 _ hQ

end K421OmCountProof

end CFSG.LocalAnalysis.RankThreeUC.S15

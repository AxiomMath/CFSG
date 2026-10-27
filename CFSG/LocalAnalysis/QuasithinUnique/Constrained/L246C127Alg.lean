module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.QuasithinUnique

namespace L246C127

@[expose] def NoOrderFour (Q : Type*) [Group Q] : Prop := ∀ g : Q, g ^ 4 = 1 → g ^ 2 = 1

theorem NoOrderFour.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (h : NoOrderFour B) :
    NoOrderFour A := by
  intro g hg
  have h1 : e g ^ 4 = 1 := by rw [← map_pow, hg, map_one]
  have h2 : e g ^ 2 = 1 := h (e g) h1
  rw [← map_pow] at h2
  exact e.injective (h2.trans (map_one e).symm)

section Alt

theorem perm_three_pow_four :
    ∀ g : Equiv.Perm (Fin 3), g ^ 4 = 1 → g ^ 2 = 1 := by decide

theorem perm_five_pow_four :
    ∀ g : Equiv.Perm (Fin 5), Equiv.Perm.sign g = 1 → g ^ 4 = 1 → g ^ 2 = 1 := by decide +kernel

theorem noOrderFour_alt_three : NoOrderFour (alternatingGroup (Fin 3)) := by
  intro g hg
  apply Subtype.ext
  have := congrArg Subtype.val hg
  have h1 := perm_three_pow_four g.1 (by simpa using this)
  simpa using h1

theorem noOrderFour_alt_five : NoOrderFour (alternatingGroup (Fin 5)) := by
  intro g hg
  apply Subtype.ext
  have := congrArg Subtype.val hg
  have h1 := perm_five_pow_four g.1 (Equiv.Perm.mem_alternatingGroup.1 g.2) (by simpa using this)
  simpa using h1

theorem not_noOrderFour_alt {n : ℕ} (hn : 6 ≤ n) : ¬ NoOrderFour (alternatingGroup (Fin n)) := by
  classical
  intro h
  obtain ⟨g, hg⟩ := (Equiv.Perm.exists_with_cycleType_iff (α := Fin n)
    (m := ({4, 2} : Multiset ℕ))).2 ⟨by simp [Fintype.card_fin]; omega, by simp⟩
  have hsign : Equiv.Perm.sign g = 1 := by
    rw [Equiv.Perm.sign_of_cycleType, hg]
    decide
  have hord : orderOf g = 4 := by
    rw [← Equiv.Perm.lcm_cycleType, hg]
    decide
  have h4 : (⟨g, Equiv.Perm.mem_alternatingGroup.2 hsign⟩ : alternatingGroup (Fin n)) ^ 4 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one g
    rw [hord] at this
    simpa using this
  have h2 := h _ h4
  have h2' : g ^ 2 = 1 := by simpa using congrArg Subtype.val h2
  have := orderOf_dvd_of_pow_eq_one h2'
  rw [hord] at this
  omega

theorem alt_five_le_of_quasisimple {A : Type} [Group A] {n : ℕ} (e : A ≃* alternatingGroup (Fin n))
    (hq : CFSG.IsQuasisimple A) : 5 ≤ n := by
  by_contra h5
  push Not at h5
  have h4 : Nat.card (Fin n) ≤ 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  have hsolv : Group.IsSolvable (alternatingGroup (Fin n)) := alternatingGroup.isSolvable h4
  have hsA : Group.IsSolvable A :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hsQ : Group.IsSolvable (A ⧸ Subgroup.center A) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center A))
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hq
  have := (IsSimpleGroup.comm_iff_isSolvable (G := A ⧸ Subgroup.center A)).2 hsQ
  exact hab (this a b)

theorem alt_degree_cases {A : Type} [Group A] {n : ℕ} (e : A ≃* alternatingGroup (Fin n))
    (h : CFSG.IsQuasisimple A ∨ Nat.card A = 3) : n = 3 ∨ 5 ≤ n := by
  rcases h with hq | hc
  · exact Or.inr (alt_five_le_of_quasisimple e hq)
  · by_contra hcon
    push Not at hcon
    obtain ⟨h3, h5⟩ := hcon
    have hc' : Nat.card (alternatingGroup (Fin n)) = 3 := by
      rw [← Nat.card_congr e.toEquiv]; exact hc
    rw [Nat.card_eq_fintype_card] at hc'
    interval_cases n
    · revert hc'; decide
    · revert hc'; decide
    · revert hc'; decide
    · exact h3 rfl
    · revert hc'; decide

end Alt

section SL

theorem sl2_entries {F : Type*} [Field F] (h2 : (2 : F) = 0) (a b c d : F) (hdet : a * d - b * c = 1)
    (e00 : (a * a + b * c) * (a * a + b * c) + (a * b + b * d) * (c * a + d * c) = 1)
    (e01 : (a * a + b * c) * (a * b + b * d) + (a * b + b * d) * (c * b + d * d) = 0)
    (e10 : (c * a + d * c) * (a * a + b * c) + (c * b + d * d) * (c * a + d * c) = 0) :
    a * a + b * c = 1 ∧ a * b + b * d = 0 ∧ c * a + d * c = 0 ∧ c * b + d * d = 1 := by
  by_cases ht : a + d = 0
  · refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (-1 : F) * hdet + a * ht - h2
    · linear_combination b * ht
    · linear_combination c * ht
    · linear_combination (-1 : F) * hdet + d * ht - h2
  · exfalso
    have hb3 : b * (a + d) ^ 3 = 0 := by
      linear_combination e01 + (2 * (a * b + b * d)) * hdet + (a * b + b * d) * h2
    have hc3 : c * (a + d) ^ 3 = 0 := by
      linear_combination e10 + (2 * (c * a + d * c)) * hdet + (c * a + d * c) * h2
    have hb : b = 0 := by
      rcases mul_eq_zero.1 hb3 with h | h
      · exact h
      · exact absurd ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).1 h) ht
    have hc : c = 0 := by
      rcases mul_eq_zero.1 hc3 with h | h
      · exact h
      · exact absurd ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).1 h) ht
    subst hb hc
    have hdet' : a * d = 1 := by simpa using hdet
    have e00' : a * a * (a * a) = 1 := by simpa using e00
    have hsq : (a * a + 1) ^ 2 = 0 := by linear_combination e00' + (1 + a * a) * h2
    have h1 : a * a + 1 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
    have hat : a * (a + d) = 0 := by linear_combination h1 + hdet'
    rcases mul_eq_zero.1 hat with ha | ha
    · rw [ha] at hdet'
      simp at hdet'
    · exact ht ha

theorem matrix_sq_eq_one_of_pow_four {F : Type*} [Field F] [CharP F 2] (M : Matrix (Fin 2) (Fin 2) F)
    (hdet : M.det = 1) (h4 : M ^ 4 = 1) : M ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : F, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [Matrix.det_fin_two_of] at hdet
  have hM2 : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) ^ 2 =
      !![a * a + b * c, a * b + b * d; c * a + d * c, c * b + d * d] := by
    rw [pow_two, Matrix.mul_fin_two]
  have hM4 : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) ^ 4 =
      !![(a * a + b * c) * (a * a + b * c) + (a * b + b * d) * (c * a + d * c),
        (a * a + b * c) * (a * b + b * d) + (a * b + b * d) * (c * b + d * d);
        (c * a + d * c) * (a * a + b * c) + (c * b + d * d) * (c * a + d * c),
        (c * a + d * c) * (a * b + b * d) + (c * b + d * d) * (c * b + d * d)] := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hM2, pow_two, Matrix.mul_fin_two]
  rw [hM4] at h4
  have e00 : (a * a + b * c) * (a * a + b * c) + (a * b + b * d) * (c * a + d * c) = 1 := by
    simpa using congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) h4
  have e01 : (a * a + b * c) * (a * b + b * d) + (a * b + b * d) * (c * b + d * d) = 0 := by
    simpa using congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 1) h4
  have e10 : (c * a + d * c) * (a * a + b * c) + (c * b + d * d) * (c * a + d * c) = 0 := by
    simpa using congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 1 0) h4
  obtain ⟨hp, hq, hr, hs⟩ := sl2_entries h2 a b c d hdet e00 e01 e10
  rw [hM2, hp, hq, hr, hs, Matrix.one_fin_two]

theorem noOrderFour_sl2 (F : Type*) [Field F] [CharP F 2] :
    NoOrderFour (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro g hg
  have h4 : (g : Matrix (Fin 2) (Fin 2) F) ^ 4 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hg, Matrix.SpecialLinearGroup.coe_one]
  have h2 := matrix_sq_eq_one_of_pow_four (g : Matrix (Fin 2) (Fin 2) F) g.2 h4
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact h2

theorem not_noOrderFour_sl3 :
    ¬ NoOrderFour (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  intro h
  have hdet : (!![1, 1, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    decide +kernel
  have hM4 : (!![1, 1, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 4 = 1 := by
    decide +kernel
  have hM2 : (!![1, 1, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 2 ≠ 1 := by
    decide +kernel
  let g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], hdet⟩
  have h4 : g ^ 4 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hM4
  have h2 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 2 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, h g h4, Matrix.SpecialLinearGroup.coe_one]
  exact hM2 h2

theorem center_sl3_eq_bot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr1 : r = 1 := by
    have : ∀ r : ZMod 2, r ^ Fintype.card (Fin 3) = 1 → r = 1 := by decide
    exact this r hr
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

end SL

end L246C127

end CFSG.QuasithinUnique

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Fin

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma zmod_two_val_eq (a : ZMod 2) : a.val = 0 ∨ a.val = 1 := by
  fin_cases a <;> decide

@[simp] private lemma zmod_two_val_one : (1 : ZMod 2).val = 1 := by decide

private lemma pow_zmod_two_add {Q : Type} [Monoid Q] (hsq : ∀ x : Q, x * x = 1)
    (x : Q) (a b : ZMod 2) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add]
  rcases zmod_two_val_eq a with ha | ha <;> rcases zmod_two_val_eq b with hb | hb <;>
    rw [ha, hb] <;> norm_num <;> simp [hsq]

private def Pc {Q : Type} [CommMonoid Q] (q : Fin 5 → Q) (c : Fin 5 → ZMod 2) : Q :=
  ∏ i, q i ^ (c i).val

private lemma Pc_add {Q : Type} [CommMonoid Q] (hsq : ∀ x : Q, x * x = 1)
    (q : Fin 5 → Q) (c d : Fin 5 → ZMod 2) : Pc q (c + d) = Pc q c * Pc q d := by
  simp only [Pc, Pi.add_apply]
  rw [Finset.prod_congr rfl (fun i _ => pow_zmod_two_add hsq (q i) (c i) (d i))]
  exact Finset.prod_mul_distrib

private lemma Pc_zero {Q : Type} [CommMonoid Q] (q : Fin 5 → Q) : Pc q 0 = 1 := by
  simp [Pc]

private lemma Pc_single {Q : Type} [CommMonoid Q] (q : Fin 5 → Q) (i : Fin 5) :
    Pc q (Pi.single i (1 : ZMod 2)) = q i := by
  simp only [Pc]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma isEvenVec_single_add (i j : Fin 5) :
    IsEvenVec (Pi.single i (1 : ZMod 2) + Pi.single j 1) := by
  simp only [IsEvenVec, Pi.add_apply, Finset.sum_add_distrib, Fintype.sum_pi_single']
  decide

theorem sec121_closure_pairs {Q : Type} [Group Q] (hcomm : ∀ x y : Q, x * y = y * x)
    (hsq : ∀ x : Q, x * x = 1) (q : Fin 5 → Q) (ℓ : Q → Fin 5 → ZMod 2)
    (hℓ : ∀ x y, ℓ (x * y) = ℓ x + ℓ y) (hq : ∀ i, ℓ (q i) = wvec i) :
    ∀ x ∈ Subgroup.closure {z : Q | ∃ i j, z = q i * q j}, ℓ x = 0 → x = 1 := by
  letI : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  have hsq' : ∀ x : Q, x * x = 1 := fun x => hsq x
  have hℓ' : ∀ x y : Q, ℓ (x * y) = ℓ x + ℓ y := fun x y => hℓ x y
  have hℓ_one : ℓ (1 : Q) = 0 := by
    have h : ℓ (1 : Q) = ℓ (1 : Q) + ℓ (1 : Q) := by simpa using hℓ' 1 1
    have h2 : ℓ (1 : Q) + 0 = ℓ (1 : Q) + ℓ (1 : Q) := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have hℓ_pow : ∀ (x : Q) (n : ℕ), ℓ (x ^ n) = (n : ZMod 2) • ℓ x := by
    intro x n
    induction n with
    | zero => simp [hℓ_one]
    | succ n ih =>
      rw [pow_succ, hℓ', ih, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  have hℓ_Pc : ∀ c : Fin 5 → ZMod 2, ℓ (Pc q c) = ∑ i, c i • wvec i := by
    intro c
    have key : ∀ s : Finset (Fin 5),
        ℓ (∏ i ∈ s, q i ^ (c i).val) = ∑ i ∈ s, ((c i).val : ZMod 2) • wvec i := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [hℓ_one]
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, hℓ', hℓ_pow, hq, ih]
    have h := key Finset.univ
    simp only [ZMod.natCast_zmod_val] at h
    simpa [Pc] using h
  intro x hx hlx
  have hT : ∃ c : Fin 5 → ZMod 2, IsEvenVec c ∧ x = Pc q c := by
    refine Subgroup.closure_induction (p := fun g _ => ∃ c, IsEvenVec c ∧ g = Pc q c)
      ?_ ?_ ?_ ?_ hx
    · rintro g ⟨i, j, rfl⟩
      exact ⟨Pi.single i 1 + Pi.single j 1, isEvenVec_single_add i j,
        by rw [Pc_add hsq', Pc_single, Pc_single]⟩
    · exact ⟨0, by simp [IsEvenVec], (Pc_zero q).symm⟩
    · rintro g h _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      refine ⟨c + d, ?_, ?_⟩
      · simp only [IsEvenVec] at hc hd
        simp only [IsEvenVec, Pi.add_apply, Finset.sum_add_distrib, hc, hd, add_zero]
      · rw [Pc_add hsq']
    · rintro g _ ⟨c, hc, rfl⟩
      exact ⟨c, hc, inv_eq_of_mul_eq_one_right (hsq' (Pc q c))⟩
  obtain ⟨c, hc, hxeq⟩ := hT
  rw [hxeq] at hlx ⊢
  have h1 : ℓ (Pc q c) = c := by rw [hℓ_Pc c, even_eq_sum_wvec hc]
  have hc0 : c = 0 := by rw [← h1, hlx]
  rw [hc0, Pc_zero]

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4E16
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank

section L34

theorem s3_charP_two_of_card_four (F : Type) [Field F] [Finite F] (h : Nat.card F = 2 ^ 2) :
    CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hc, n, hp, hn⟩ := FiniteField.card' F
  rw [Nat.card_eq_fintype_card, hn] at h
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (h ▸ dvd_pow_self p n.ne_zero)
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2
  exact hc

theorem s3_exists_ne_zero_one (F : Type) [Field F] [Finite F] (h : Nat.card F = 2 ^ 2) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra hcon
  push Not at hcon
  have h2 : Nat.card F ≤ 2 := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card F = (Finset.univ : Finset F).card := rfl
      _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card fun x _ => by
          by_cases hx : x = 0 <;> simp [hx, hcon x]
      _ ≤ 2 := Finset.card_le_two
  omega

variable {F : Type} [Field F]

@[expose] def s3Mat (x y : F) : Matrix (Fin 3) (Fin 3) F := !![1, x, y; 0, 1, 0; 0, 0, 1]

theorem s3Mat_mul (x y x' y' : F) : s3Mat x y * s3Mat x' y' = s3Mat (x + x') (y + y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s3Mat, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem s3Mat_zero : s3Mat (0 : F) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s3Mat]

theorem det_s3Mat (x y : F) : (s3Mat x y).det = 1 := by
  simp [s3Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

@[expose] def s3GL (x y : F) : GL (Fin 3) F :=
  ⟨s3Mat x y, s3Mat (-x) (-y), by rw [s3Mat_mul, add_neg_cancel, add_neg_cancel, s3Mat_zero],
    by rw [s3Mat_mul, neg_add_cancel, neg_add_cancel, s3Mat_zero]⟩

theorem coe_s3GL (x y : F) : ((s3GL x y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = s3Mat x y :=
  rfl

theorem s3GL_mul (x y x' y' : F) : s3GL x y * s3GL x' y' = s3GL (x + x') (y + y') :=
  Units.ext (by rw [Units.val_mul, coe_s3GL, coe_s3GL, coe_s3GL, s3Mat_mul])

theorem s3GL_zero : s3GL (0 : F) 0 = 1 :=
  Units.ext (by rw [coe_s3GL, s3Mat_zero, Units.val_one])

theorem s3GL_comm (x y x' y' : F) : s3GL x y * s3GL x' y' = s3GL x' y' * s3GL x y := by
  rw [s3GL_mul, s3GL_mul, add_comm x, add_comm y]

theorem s3GL_pow (x y : F) (n : ℕ) : s3GL x y ^ n = s3GL ((n : F) * x) ((n : F) * y) := by
  induction n with
  | zero => simp [s3GL_zero]
  | succ n ih =>
    rw [pow_succ, ih, s3GL_mul]
    congr 1 <;> push_cast <;> ring

@[expose] def s3Gen (ω : F) : Fin 4 → GL (Fin 3) F :=
  ![s3GL 1 0, s3GL ω 0, s3GL 0 1, s3GL 0 ω]

theorem s3Gen_sq [CharP F 2] (ω : F) (i : Fin 4) : s3Gen ω i * s3Gen ω i = 1 := by
  fin_cases i <;> simp [s3Gen, s3GL_mul, CharTwo.add_self_eq_zero, s3GL_zero]

theorem s3Gen_comm (ω : F) (i j : Fin 4) : s3Gen ω i * s3Gen ω j = s3Gen ω j * s3Gen ω i := by
  fin_cases i <;> fin_cases j <;> exact s3GL_comm _ _ _ _

theorem det_s3Gen (ω : F) (i : Fin 4) :
    ((s3Gen ω i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  fin_cases i <;> exact det_s3Mat _ _

theorem s3Gen_prod (ω : F) (a : Fin 4 → ℕ) :
    (List.ofFn fun i => s3Gen ω i ^ a i).prod =
      s3GL ((a 0 : F) + (a 1 : F) * ω) ((a 2 : F) + (a 3 : F) * ω) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  show s3GL 1 0 ^ a 0 * (s3GL ω 0 ^ a 1 * (s3GL 0 1 ^ a 2 * s3GL 0 ω ^ a 3)) = _
  rw [s3GL_pow, s3GL_pow, s3GL_pow, s3GL_pow, s3GL_mul, s3GL_mul, s3GL_mul]
  congr 1 <;> ring

theorem s3_indep [CharP F 2] {ω : F} (h0 : ω ≠ 0) (h1 : ω ≠ 1) (s t : Fin 2)
    (h : ((s : ℕ) : F) + ((t : ℕ) : F) * ω = 0) : s = 0 ∧ t = 0 := by
  fin_cases s <;> fin_cases t
  · exact ⟨rfl, rfl⟩
  · simp at h
    exact absurd h h0
  · simp at h
  · simp at h
    exact absurd (by rw [← CharTwo.neg_eq (1 : F)]; exact (neg_eq_of_add_eq_zero_right h).symm) h1

end L34

theorem e16_psl3_four {K : Type} [Group K] [Finite K] (h : LieModel K .PSL 3 2 2) :
    ∃ E : Subgroup K, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) h
  have : CharP F 2 := s3_charP_two_of_card_four F hcard
  obtain ⟨ω, hω0, hω1⟩ := s3_exists_ne_zero_one F hcard
  refine exists_E16_of_equiv e
    (exists_E16_statedProj (H := StatedSL 3 F) (s3Gen ω) (fun i => ?_) (fun i => ?_) (fun i j => ?_)
      ?_)
  · exact Subgroup.subset_closure (det_s3Gen ω i)
  · refine ⟨1, ?_⟩
    rw [one_smul, ← Units.val_mul, s3Gen_sq, Units.val_one]
  · refine ⟨1, ?_⟩
    rw [one_smul, ← Units.val_mul, ← Units.val_mul, s3Gen_comm]
  · intro a ha c hc
    rw [s3Gen_prod, coe_s3GL] at hc
    have h01 := congrFun (congrFun hc 0) 1
    have h02 := congrFun (congrFun hc 0) 2
    simp [s3Mat] at h01 h02
    obtain ⟨h0, h1⟩ := s3_indep hω0 hω1 (a 0) (a 1) h01
    obtain ⟨h2, h3⟩ := s3_indep hω0 hω1 (a 2) (a 3) h02
    refine ha (funext fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3

section Alt

@[expose] def s3AltInv (n : ℕ) (hn : 8 ≤ n) : Fin 4 → Equiv.Perm (Fin n) :=
  ![Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩,
    Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩ * Equiv.swap ⟨1, by omega⟩ ⟨3, by omega⟩,
    Equiv.swap ⟨4, by omega⟩ ⟨5, by omega⟩ * Equiv.swap ⟨6, by omega⟩ ⟨7, by omega⟩,
    Equiv.swap ⟨4, by omega⟩ ⟨6, by omega⟩ * Equiv.swap ⟨5, by omega⟩ ⟨7, by omega⟩]

theorem s3AltInv_sign8 : ∀ i, Equiv.Perm.sign (s3AltInv 8 (by norm_num) i) = 1 := by decide

theorem s3AltInv_sq8 : ∀ i, s3AltInv 8 (by norm_num) i ^ 2 = 1 := by decide

theorem s3AltInv_comm8 : ∀ i j,
    s3AltInv 8 (by norm_num) i * s3AltInv 8 (by norm_num) j =
      s3AltInv 8 (by norm_num) j * s3AltInv 8 (by norm_num) i := by decide

theorem s3AltInv_ker8 : ∀ a : Fin 4 → Fin 2, a ≠ 0 →
    (List.ofFn fun i => s3AltInv 8 (by norm_num) i ^ (a i : ℕ)).prod ≠ 1 := by decide

theorem s3AltInv_sign9 : ∀ i, Equiv.Perm.sign (s3AltInv 9 (by norm_num) i) = 1 := by decide

theorem s3AltInv_sq9 : ∀ i, s3AltInv 9 (by norm_num) i ^ 2 = 1 := by decide

theorem s3AltInv_comm9 : ∀ i j,
    s3AltInv 9 (by norm_num) i * s3AltInv 9 (by norm_num) j =
      s3AltInv 9 (by norm_num) j * s3AltInv 9 (by norm_num) i := by decide

theorem s3AltInv_ker9 : ∀ a : Fin 4 → Fin 2, a ≠ 0 →
    (List.ofFn fun i => s3AltInv 9 (by norm_num) i ^ (a i : ℕ)).prod ≠ 1 := by decide

theorem s3AltInv_spec (n : ℕ) (hn8 : 8 ≤ n) (hn9 : n ≤ 9) :
    (∀ i, Equiv.Perm.sign (s3AltInv n hn8 i) = 1) ∧ (∀ i, s3AltInv n hn8 i ^ 2 = 1) ∧
      (∀ i j, s3AltInv n hn8 i * s3AltInv n hn8 j = s3AltInv n hn8 j * s3AltInv n hn8 i) ∧
      (∀ a : Fin 4 → Fin 2, a ≠ 0 →
        (List.ofFn fun i => s3AltInv n hn8 i ^ (a i : ℕ)).prod ≠ 1) := by
  interval_cases n
  · exact ⟨s3AltInv_sign8, s3AltInv_sq8, s3AltInv_comm8, s3AltInv_ker8⟩
  · exact ⟨s3AltInv_sign9, s3AltInv_sq9, s3AltInv_comm9, s3AltInv_ker9⟩

end Alt

theorem e16_alt_eight_nine {K : Type} [Group K] [Finite K] {n : ℕ} (hn8 : 8 ≤ n) (hn9 : n ≤ 9)
    (e : K ≃* alternatingGroup (Fin n)) :
    ∃ E : Subgroup K, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨hs, hsq, hcomm, hker⟩ := s3AltInv_spec n hn8 hn9
  let u : Fin 4 → alternatingGroup (Fin n) := fun i =>
    ⟨s3AltInv n hn8 i, Equiv.Perm.mem_alternatingGroup.2 (hs i)⟩
  refine exists_E16_of_equiv e (exists_E16_of_commuting_involutions u ?_ ?_ ?_)
  · intro i
    exact Subtype.ext (hsq i)
  · intro i j
    exact Subtype.ext (hcomm i j)
  · intro a ha hprod
    refine hker a ha ?_
    have h := congrArg Subtype.val hprod
    rwa [← Subgroup.coe_subtype, map_list_prod, List.map_ofFn] at h

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94

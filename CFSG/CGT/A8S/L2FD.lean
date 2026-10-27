module

public import CFSG.CGT.A8S.L2Words

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

theorem avc_d1 : avc (dE 0) = 3160 := avc_dE 0

theorem avc_d2 : avc (dE 1) = 2717 := avc_dE 1

theorem fd1_check : d0Codes.all (fun z => !(Nat.beq (cmul z 3160) (cmul 3160 z) &&
    Nat.beq (cmul z 2717) (cmul 2717 z)) || Nat.beq z 2184) = true := by
  decide +kernel

theorem centerA8 (z : PG 5 relsN0A8) (hz : z ∈ D0)
    (hc : ∀ i, z * dE i = dE i * z) : z = 1 := by
  have h := forall_D0 fd1_check hz
  have h0 : Nat.beq (cmul (avc z) 3160) (cmul 3160 (avc z)) = true := by
    rw [Nat.beq_eq, ← avc_d1, ← avc_mul, ← avc_mul, hc 0]
  have h1 : Nat.beq (cmul (avc z) 2717) (cmul 2717 (avc z)) = true := by
    rw [Nat.beq_eq, ← avc_d2, ← avc_mul, ← avc_mul, hc 1]
  rw [h0, h1] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Nat.beq_eq] at h
  exact avc_inj (h.trans avc_one.symm)

@[expose] def wTh : Fin 2 → List (Fin 2) := ![[1, 0, 1, 0, 0], [0, 1, 0, 1, 1]]

theorem fd2_check : ∀ i : Fin 2, evD 3160 2717 (wTh i) = thC i ∧ evD 3675 3228 (wTh i) = dC i := by
  decide +kernel

theorem theta_wordsA8 (i : Fin 2) :
    evalD (dE 0) (dE 1) (wTh i) = thE i ∧ evalD (thE 0) (thE 1) (wTh i) = dE i := by
  refine ⟨avc_inj ?_, avc_inj ?_⟩
  · rw [avc_evalD_dE, avc_thE]
    exact (fd2_check i).1
  · rw [avc_evalD, avc_thE, avc_thE, avc_dE]
    exact (fd2_check i).2

abbrev commTB : PG 5 relsN0A8 := tGenA8 2 * beta1 * (tGenA8 2)⁻¹ * beta1⁻¹

theorem avc_tGen (j : Fin 3) : avc (tGenA8 j) = 2184 + 2 ^ j.val := by
  fin_cases j <;> rfl

theorem tau_not_mem : tGenA8 2 ∉ D0 := by
  intro h
  have h' := avc_mem_d0Codes h
  rw [avc_tGen] at h'
  exact absurd h' (by decide +kernel)

theorem beta1_ne : beta1 ≠ 1 := by
  intro h
  have h' := avc_beta1
  rw [h, avc_one] at h'
  exact absurd h' (by decide)

theorem swap_codes : cmul 2188 2188 = 2184 ∧ cmul 3211 3211 = 2184 ∧
    cmul (cmul (cmul 2188 3211) 2188) 3211 = 2186 ∧ normB0c 2186 = true ∧
    cmul 2717 3211 = cmul 3211 2717 ∧ cmul 2717 2186 = cmul 2186 2717 ∧
    b0Codes.all (fun s => !Nat.beq (cmul 2717 s) (cmul s 2717) || Nat.beq s 2184 ||
      Nat.beq s 3211) = true := by
  decide +kernel

theorem commTB_eq : commTB = tGenA8 1 := by
  have h1 : (tGenA8 2)⁻¹ = tGenA8 2 :=
    inv_eq_of_mul_eq_one_right (avc_inj (by rw [avc_mul, avc_tGen, avc_one]; exact swap_codes.1))
  have h2 : beta1⁻¹ = beta1 :=
    inv_eq_of_mul_eq_one_right (avc_inj (by
      rw [avc_mul, avc_beta1, avc_one]; exact swap_codes.2.1))
  rw [commTB, h1, h2]
  apply avc_inj
  rw [avc_mul, avc_mul, avc_mul, avc_tGen, avc_beta1, avc_tGen]
  exact swap_codes.2.2.1

theorem commTB_mem_D0 : commTB ∈ D0 := by
  rw [commTB_eq]
  exact mem_D0_of_normB0c (by rw [avc_tGen]; exact swap_codes.2.2.2.1)

theorem commTB_ne : commTB ≠ 1 := by
  rw [commTB_eq]
  intro h
  have h' := avc_tGen 1
  rw [h, avc_one] at h'
  exact absurd h' (by decide)

theorem sig_beta1 : dE 1 * beta1 = beta1 * dE 1 :=
  avc_inj (by rw [avc_mul, avc_mul, avc_dE, avc_beta1]; exact swap_codes.2.2.2.2.1)

theorem sig_commTB : dE 1 * commTB = commTB * dE 1 := by
  rw [commTB_eq]
  exact avc_inj (by rw [avc_mul, avc_mul, avc_dE, avc_tGen]; exact swap_codes.2.2.2.2.2.1)

theorem sig_fix (y : PG 5 relsN0A8) (hy : y ∈ B0)
    (h : dE 1 * y = y * dE 1) : y = 1 ∨ y = beta1 := by
  have hc := List.all_eq_true.1 swap_codes.2.2.2.2.2.2 _ ((mem_B0_iff y).1 hy)
  have h' : Nat.beq (cmul 2717 (avc y)) (cmul (avc y) 2717) = true := by
    rw [Nat.beq_eq, ← avc_d2, ← avc_mul, ← avc_mul, h]
  rw [h'] at hc
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Nat.beq_eq] at hc
  rcases hc with hc | hc
  · exact Or.inl (avc_inj (hc.trans avc_one.symm))
  · exact Or.inr (avc_inj (hc.trans avc_beta1.symm))

end CFSG.CGT.A8S.L2

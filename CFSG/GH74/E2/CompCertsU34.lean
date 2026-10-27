module

public import CFSG.GH74.Generic.ClassicalCerts

public section

namespace CFSG.GH74.E2

open CFSG.GH74.Generic CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd CFSG.GH74.L5U5
  CFSG.SectionRank.ClassicalOdd Matrix

section U34

variable {F : Type} [Field F]

@[expose] def u34A : Matrix (Fin 3) (Fin 3) F := !![1, 1, 1; 1, 1, 1; 0, 0, 0]

@[expose] def u34B : Matrix (Fin 3) (Fin 3) F := !![1, 1, 0; 1, 1, 0; 1, 1, 0]

@[expose] def u34M : Matrix (Fin 3) (Fin 3) F := !![1, 1, 0; 1, 1, 0; 0, 0, 0]

theorem u34A_mul_u34B (h2 : (2 : F) = 0) : (u34A * u34B : Matrix (Fin 3) (Fin 3) F) = u34M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34A, u34B, u34M, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem u34B_mul_u34A (h2 : (2 : F) = 0) : (u34B * u34A : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34A, u34B, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem u34A_mul_u34A (h2 : (2 : F) = 0) : (u34A * u34A : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34A, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem u34B_mul_u34B (h2 : (2 : F) = 0) : (u34B * u34B : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34B, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem u34A_mul_u34M (h2 : (2 : F) = 0) : (u34A * u34M : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34A, u34M, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem u34M_mul_u34A (h2 : (2 : F) = 0) : (u34M * u34A : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34A, u34M, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem u34B_mul_u34M (h2 : (2 : F) = 0) : (u34B * u34M : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34B, u34M, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem u34M_mul_u34B (h2 : (2 : F) = 0) : (u34M * u34B : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34B, u34M, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem u34M_mul_u34M (h2 : (2 : F) = 0) : (u34M * u34M : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34M, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

@[expose] def u34Gen (a b c : F) : Matrix (Fin 3) (Fin 3) F :=
  1 + a • u34A + b • u34B + c • u34M

theorem u34Gen_zero : u34Gen (0 : F) 0 0 = 1 := by
  simp [u34Gen]

theorem u34Gen_mul (h2 : (2 : F) = 0) (a b c a' b' c' : F) :
    u34Gen a b c * u34Gen a' b' c' = u34Gen (a + a') (b + b') (c + c' + a * b') := by
  simp only [u34Gen, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, u34A_mul_u34B h2, u34B_mul_u34A h2, u34A_mul_u34A h2,
    u34B_mul_u34B h2, u34A_mul_u34M h2, u34M_mul_u34A h2, u34B_mul_u34M h2, u34M_mul_u34B h2,
    u34M_mul_u34M h2, smul_zero, add_zero]
  module

theorem u34Gen_apply_two_zero (a b c : F) : u34Gen a b c 2 0 = b := by
  simp [u34Gen, u34A, u34B, u34M]

theorem det_u34Gen (h2 : (2 : F) = 0) (a b c : F) : (u34Gen a b c).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [u34Gen, u34A, u34B, u34M]
  linear_combination (a + b + c - a * b) * h2

theorem hstar_u34A (σ : F →+* F) : hstar σ (u34A : Matrix (Fin 3) (Fin 3) F) = u34B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hstar, u34A, u34B]

theorem hstar_u34B (σ : F →+* F) : hstar σ (u34B : Matrix (Fin 3) (Fin 3) F) = u34A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hstar, u34A, u34B]

theorem hstar_u34M (σ : F →+* F) : hstar σ (u34M : Matrix (Fin 3) (Fin 3) F) = u34M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hstar, u34M]

theorem hstar_u34Gen (σ : F →+* F) (a b c : F) :
    hstar σ (u34Gen a b c) = u34Gen (σ b) (σ a) (σ c) := by
  unfold u34Gen
  rw [hstar_add, hstar_add, hstar_add, hstar_one, hstar_smul, hstar_smul, hstar_smul,
    hstar_u34A, hstar_u34B, hstar_u34M]
  module

def u34T (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x) (h2 : (2 : F) = 0) : Subgroup (GL (Fin 3) F) where
  carrier := {A | ∃ x y : F, y + σ y = x * σ x ∧
    (A : Matrix (Fin 3) (Fin 3) F) = u34Gen (σ x) x y}
  mul_mem' := by
    rintro A A' ⟨x, y, hy, hA⟩ ⟨x', y', hy', hA'⟩
    refine ⟨x + x', y + y' + σ x * x', ?_, ?_⟩
    · simp only [map_add, map_mul, hσσ]
      linear_combination hy + hy'
    · rw [Units.val_mul, hA, hA', u34Gen_mul h2, map_add]
  one_mem' := ⟨0, 0, by simp, by simp [u34Gen_zero]⟩
  inv_mem' := by
    rintro A ⟨x, y, hy, hA⟩
    refine ⟨x, σ y, ?_, ?_⟩
    · rw [hσσ]
      linear_combination hy
    · have e1 : σ x + σ x = 0 := by linear_combination (σ x) * h2
      have e2 : x + x = 0 := by linear_combination x * h2
      have e3 : y + σ y + σ x * x = 0 := by linear_combination hy + (x * σ x) * h2
      have h1 : (A : Matrix (Fin 3) (Fin 3) F) * u34Gen (σ x) x (σ y) = 1 := by
        rw [hA, u34Gen_mul h2, e1, e2, e3, u34Gen_zero]
      rw [Matrix.GeneralLinearGroup.coe_inv]
      exact Matrix.inv_eq_right_inv h1

def u34Beta (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x) (h2 : (2 : F) = 0) :
    u34T σ hσσ h2 →* Multiplicative F where
  toFun A := Multiplicative.ofAdd (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0)
  map_one' := by simp
  map_mul' A A' := by
    obtain ⟨x, y, hy, hA⟩ := A.2
    obtain ⟨x', y', hy', hA'⟩ := A'.2
    change Multiplicative.ofAdd ((((A : GL (Fin 3) F) * (A' : GL (Fin 3) F) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 2 0) = _
    rw [Units.val_mul, hA, hA', u34Gen_mul h2, u34Gen_apply_two_zero, u34Gen_apply_two_zero,
      u34Gen_apply_two_zero]
    rfl

theorem u34Beta_surjective (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x) (h2 : (2 : F) = 0)
    (hθ : ∃ θ : F, θ + σ θ = 1) : Function.Surjective (u34Beta σ hσσ h2) := by
  obtain ⟨θ, hθ⟩ := hθ
  intro k
  set ξ : F := Multiplicative.toAdd k with hξ
  have hy : θ * (ξ * σ ξ) + σ (θ * (ξ * σ ξ)) = ξ * σ ξ := by
    simp only [map_mul, hσσ]
    linear_combination (ξ * σ ξ) * hθ
  let A : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (u34Gen (σ ξ) ξ (θ * (ξ * σ ξ)))
    (by rw [det_u34Gen h2]; exact one_ne_zero)
  refine ⟨⟨A, ξ, θ * (ξ * σ ξ), hy, rfl⟩, ?_⟩
  change Multiplicative.ofAdd (u34Gen (σ ξ) ξ (θ * (ξ * σ ξ)) 2 0) = k
  rw [u34Gen_apply_two_zero]
  exact ofAdd_toAdd k

theorem exists_trace_one [Finite F] (σ : F →+* F) (hσ : ∀ x, σ x = x ^ 4) (h2 : (2 : F) = 0)
    (hF : Nat.card F = 16) : ∃ θ : F, θ + σ θ = 1 := by
  obtain ⟨u, hu⟩ := exists_units_orderOf (F := F) (d := 5) (by rw [hF]; norm_num)
  have hu5 : u ^ 5 = 1 := hu ▸ pow_orderOf_eq_one u
  set ζ : F := (u : F) with hζ
  have hζ5 : ζ ^ 5 = 1 := by simpa using congrArg Units.val hu5
  have hζ1 : ζ ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    omega
  have hsum : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
    have : (ζ - 1) * (ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ5
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hζ1
    · exact h
  refine ⟨ζ + ζ ^ 2, ?_⟩
  rw [map_add, hσ, hσ]
  linear_combination hsum - h2 + ζ ^ 3 * hζ5

end U34

theorem rankCertified_SU3_four {F : Type} [Field F] [Finite F] {q : ℕ} (hq : q = 4)
    (hF : Nat.card F = q ^ 2) : RankCertified (StatedProj (StatedSU 3 q F)) 3 := by
  subst hq
  have hF16 : Nat.card F = 2 ^ 4 := by rw [hF]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := 4) hF16
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  let σ : F →+* F := iterateFrobenius F 2 2
  have hσ : ∀ x, σ x = x ^ 4 := fun x => by
    rw [CFSG.SectionRank.ClassicalOdd.frob_apply]
    norm_num
  have hσσ : ∀ x, σ (σ x) = x := fun x =>
    CFSG.SectionRank.ClassicalOdd.frob_frob (by rw [hF]; norm_num) x
  have hθ := exists_trace_one σ hσ h2 (by rw [hF16]; norm_num)
  refine rankCertified_statedProj (A := Multiplicative F) (u34T σ hσσ h2).subtype (fun k => ?_)
    (u34Beta σ hσσ h2) (u34Beta_surjective σ hσσ h2 hθ) (fun a b => mul_comm a b)
    (fun a => ?_) ?_ ?_
  · obtain ⟨x, y, hy, hk⟩ := k.2
    refine mem_statedSU_of_isUni hσ _ ?_ ?_
    · change (((k : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).det = 1
      rw [hk]
      exact det_u34Gen h2 _ _ _
    · change hstar σ (((k : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) *
        (((k : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) = 1
      have e1 : σ x + σ x = 0 := by linear_combination (σ x) * h2
      have e2 : x + x = 0 := by linear_combination x * h2
      have e3 : σ y + y + σ x * x = 0 := by linear_combination hy + (x * σ x) * h2
      rw [hk, hstar_u34Gen, hσσ, u34Gen_mul h2, e1, e2, e3, u34Gen_zero]
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  · rw [Nat.card_congr Multiplicative.toAdd, hF16]
    norm_num
  · intro k c h
    change Multiplicative.ofAdd (((k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0) = 1
    have h' : ((k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) c := h
    rw [h']
    simp [scalar_apply]

end CFSG.GH74.E2

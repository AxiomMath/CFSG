module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open Matrix
open scoped commutatorElement

section Matrices

variable {K : Type} [Field K]

@[expose] def uMat (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, b; 0, 1, c; 0, 0, 1]

@[expose] def uSL (a b c : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨uMat a b c, by simp [uMat, det_fin_three]⟩

theorem coe_uSL (a b c : K) :
    ((uSL a b c : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = uMat a b c := rfl

theorem uSL_mul (a b c a' b' c' : K) :
    uSL a b c * uSL a' b' c' = uSL (a + a') (b + b' + a * c') (c + c') := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, uMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

theorem uSL_zero : uSL (0 : K) 0 0 = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, uMat]

theorem uSL_inv (a b c : K) : (uSL a b c)⁻¹ = uSL (-a) (a * c - b) (-c) := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [uSL_mul]
  have : (a + -a) = 0 := by ring
  rw [show b + (a * c - b) + a * -c = 0 by ring, show c + -c = 0 by ring, this, uSL_zero]

theorem uSL_injective {a b c a' b' c' : K} (h : uSL a b c = uSL a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K) 0 1) h
  have h2 := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K) 0 2) h
  have h3 := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K) 1 2) h
  simp [coe_uSL, uMat] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem uSL_comm (a b c a' b' c' : K) :
    ⁅uSL a b c, uSL a' b' c'⁆ = uSL 0 (a * c' - a' * c) 0 := by
  rw [commutatorElement_def, uSL_inv, uSL_inv, uSL_mul, uSL_mul, uSL_mul]
  congr 1 <;> ring

@[expose] def tMat (t : Kˣ × Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  diagonal ![(t.1 : K), (t.2 : K), (((t.1 * t.2)⁻¹ : Kˣ) : K)]

theorem det_tMat (t : Kˣ × Kˣ) : (tMat t : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp only [tMat, det_diagonal, Fin.prod_univ_three]
  simp
  field_simp

@[expose] def tFun (t : Kˣ × Kˣ) : SpecialLinearGroup (Fin 3) K := ⟨tMat t, det_tMat t⟩

theorem coe_tFun (t : Kˣ × Kˣ) :
    ((tFun t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = tMat t := rfl

@[expose] def tSL : Kˣ × Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun := tFun
  map_one' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_tFun, tMat]
  map_mul' t t' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_tFun, tMat, Matrix.mul_apply, Fin.sum_univ_three]
    ring

theorem tSL_mul_uSL (t : Kˣ × Kˣ) (a b c : K) :
    tSL t * uSL a b c = uSL ((t.1 : K) * (t.2 : K)⁻¹ * a) ((t.1 : K) ^ 2 * t.2 * b)
      ((t.1 : K) * (t.2 : K) ^ 2 * c) * tSL t := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [show (tSL t : SpecialLinearGroup (Fin 3) K) = tFun t from rfl, coe_tFun, coe_uSL, tMat,
      uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem tSL_conj_uSL (t : Kˣ × Kˣ) (a b c : K) :
    tSL t * uSL a b c * (tSL t)⁻¹ = uSL ((t.1 : K) * (t.2 : K)⁻¹ * a) ((t.1 : K) ^ 2 * t.2 * b)
      ((t.1 : K) * (t.2 : K) ^ 2 * c) := by
  rw [tSL_mul_uSL, mul_inv_cancel_right]

end Matrices

section Subgroups

variable (K : Type) [Field K]

@[expose] def Usl : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∃ a b c : K, g = uSL a b c}
  one_mem' := ⟨0, 0, 0, uSL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, uSL_mul a b c a' b' c'⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, uSL_inv a b c⟩

@[expose] def Zsl : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∃ b : K, g = uSL 0 b 0}
  one_mem' := ⟨0, uSL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    exact ⟨b + b', by rw [uSL_mul]; simp⟩
  inv_mem' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨-b, by rw [uSL_inv]; simp⟩

variable {K}

theorem mem_Usl {g : SpecialLinearGroup (Fin 3) K} : g ∈ Usl K ↔ ∃ a b c : K, g = uSL a b c :=
  Iff.rfl

theorem mem_Zsl {g : SpecialLinearGroup (Fin 3) K} : g ∈ Zsl K ↔ ∃ b : K, g = uSL 0 b 0 :=
  Iff.rfl

theorem uSL_mem_Usl (a b c : K) : uSL a b c ∈ Usl K := ⟨a, b, c, rfl⟩

theorem uSL_mem_Zsl (b : K) : uSL 0 b 0 ∈ Zsl K := ⟨b, rfl⟩

theorem Zsl_le_Usl : Zsl K ≤ Usl K := by
  rintro _ ⟨b, rfl⟩
  exact uSL_mem_Usl _ _ _

theorem card_Usl [Finite K] : Nat.card (Usl K) = Nat.card K ^ 3 := by
  let f : K × K × K → Usl K := fun x => ⟨uSL x.1 x.2.1 x.2.2, uSL_mem_Usl _ _ _⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := uSL_injective (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨g, a, b, c, rfl⟩ := g
      exact ⟨(a, b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod]
  ring

theorem card_sl_three [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 3) K) =
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
  rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toEquiv]
  exact CFSG.SectionRank.OddCover.card_statedSL_three

theorem isPGroup_Usl [Finite K] {p f : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ f) :
    IsPGroup p (Usl K) := by
  apply IsPGroup.of_card (n := 3 * f)
  rw [card_Usl, hK, ← pow_mul, mul_comm]

theorem not_dvd_index_Usl [Finite K] {p f : ℕ} [hp : Fact p.Prime] (hK : Nat.card K = p ^ f)
    (hf : 1 ≤ f) : ¬ p ∣ (Usl K).index := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have h1 : (Usl K).index = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
    have h := (Usl K).card_mul_index
    rw [card_Usl, card_sl_three, mul_assoc] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 3) h
  have hpq : p ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self p (by omega)
  have hp' := hp.out
  rw [h1]
  intro h
  rcases (Nat.Prime.dvd_mul hp').1 h with h2 | h2
  · have h3 : p ∣ Nat.card K ^ 2 := dvd_pow hpq (by omega)
    have := Nat.dvd_sub h3 h2
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at this
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)
  · have h3 : p ∣ Nat.card K ^ 3 := dvd_pow hpq (by omega)
    have := Nat.dvd_sub h3 h2
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at this
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)

end Subgroups

end CFSG.ClassicalInvolution.ModelFacts.OddCover

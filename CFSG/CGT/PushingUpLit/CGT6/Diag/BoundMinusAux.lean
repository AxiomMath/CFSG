module

public import CFSG.CGT.PushingUpLit.CGT6.Props

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Bound

theorem card_fixed_le (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {x : Fq (2 * n) // frobHalf n x = x} ≤ 2 ^ n := by
  classical
  have : Fintype (Fq (2 * n)) := Fintype.ofFinite _
  have hp : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq (Fq (2 * n)) hp
  have hne : (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial (Fq (2 * n))) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  let T : Finset (Fq (2 * n)) := Finset.univ.filter (fun x => frobHalf n x = x)
  have hT : T.val ⊆ (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial (Fq (2 * n))).roots := by
    intro x hx
    have hx' : frobHalf n x = x := (Finset.mem_filter.mp hx).2
    rw [Polynomial.mem_roots hne]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [sub_eq_zero]
    exact hx'
  have h1 := Polynomial.card_le_degree_of_subset_roots hT
  rw [hdeg] at h1
  have h2 : Nat.card {x : Fq (2 * n) // frobHalf n x = x} = T.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h2]
  exact h1

theorem card_hermSub_le (n : ℕ) (hn : 1 ≤ n) : Nat.card (hermSub n) ≤ 2 ^ (4 * n) := by
  classical
  let S := {x : Fq (2 * n) // frobHalf n x = x}
  let f : hermSub n → S × S × Fq (2 * n) := fun M =>
    (⟨(M : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 0 0, (M.2 0 0).symm⟩,
     ⟨(M : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 1, (M.2 1 1).symm⟩,
     (M : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 0 1)
  have hf : Function.Injective f := by
    intro M N h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h00, h11, h01⟩ := h
    have h00' : (M : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 0 0 =
        (N : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 0 0 := congrArg Subtype.val h00
    have h11' : (M : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 1 =
        (N : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 1 := congrArg Subtype.val h11
    have h10 : (M : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 0 =
        (N : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 0 := by
      have h1 : (M : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 0 =
          frobHalf n ((M : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 0 1) := M.2 1 0
      have h2 : (N : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 1 0 =
          frobHalf n ((N : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) 0 1) := N.2 1 0
      rw [h1, h2, h01]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00'
    · exact h01
    · exact h10
    · exact h11'
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod] at h1
  have h2 := card_fixed_le n hn
  have h3 : Nat.card (Fq (2 * n)) = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
  have h4 : Nat.card S ≤ 2 ^ n := h2
  calc Nat.card (hermSub n) ≤ Nat.card S * (Nat.card S * Nat.card (Fq (2 * n))) := h1
    _ ≤ 2 ^ n * (2 ^ n * 2 ^ (2 * n)) := by
      rw [h3]
      exact Nat.mul_le_mul h4 (Nat.mul_le_mul h4 le_rfl)
    _ = 2 ^ (4 * n) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

theorem exists_unit_pow (n : ℕ) (hn : 1 ≤ n) :
    ∃ l : (Fq (2 * n))ˣ, l ≠ 1 ∧ l ^ (2 ^ n + 1) = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Fq (2 * n))ˣ)
  have hcard : orderOf g = 2 ^ (2 * n) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
      GaloisField.card 2 (2 * n) (by omega)]
  have hp : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hsq : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
  have hprod : (2 ^ n - 1) * (2 ^ n + 1) = 2 ^ (2 * n) - 1 := by
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ n = s + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hsq, hs]
    have : (s + 1) * (s + 1) = s * (s + 2) + 1 := by ring
    rw [this]
    simp
  refine ⟨g ^ (2 ^ n - 1), ?_, ?_⟩
  · apply pow_ne_one_of_lt_orderOf (by omega)
    rw [hcard]
    have : 2 ^ n < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [← pow_mul, hprod, ← hcard]
    exact pow_orderOf_eq_one g

@[expose] def diagMat (K : Type*) [Field K] (u : Kˣ) : Matrix (Fin 2) (Fin 2) K :=
  !![(u : K), 0; 0, ((u⁻¹ : Kˣ) : K)]

theorem det_diagMat (K : Type*) [Field K] (u : Kˣ) : (diagMat K u).det = 1 := by
  simp [diagMat, Matrix.det_fin_two_of]

theorem diagMat_one (K : Type*) [Field K] : diagMat K 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat]

theorem diagMat_mul (K : Type*) [Field K] (u v : Kˣ) :
    diagMat K (u * v) = diagMat K u * diagMat K v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[expose] def diagHom (K : Type*) [Field K] : Kˣ →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun u := ⟨diagMat K u, det_diagMat K u⟩
  map_one' := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show diagMat K 1 i j = (1 : Matrix (Fin 2) (Fin 2) K) i j
    rw [diagMat_one]
  map_mul' u v := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show diagMat K (u * v) i j = (diagMat K u * diagMat K v) i j
    rw [diagMat_mul]

theorem coe_diagHom (K : Type*) [Field K] (u : Kˣ) :
    ((diagHom K u : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      diagMat K u := rfl

theorem diagHom_apply_zero_zero (K : Type*) [Field K] (u : Kˣ) :
    ((diagHom K u : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = u := by
  simp [coe_diagHom, diagMat]

@[expose] noncomputable def e11 (n : ℕ) : Matrix (Fin 2) (Fin 2) (Fq (2 * n)) := !![1, 0; 0, 0]

theorem e11_mem (n : ℕ) : e11 n ∈ hermSub n := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e11, frobHalf]

theorem e11_ne_zero (n : ℕ) : e11 n ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [e11] at this

theorem omegaMinusAct_of_mem (n : ℕ) (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    (m : Multiplicative (hermSub n))
    (h : (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * (Multiplicative.toAdd m : _) *
      ((A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))).map (frobHalf n)).transpose ∈ hermSub n) :
    omegaMinusAct n A m = Multiplicative.ofAdd ⟨_, h⟩ := by
  classical
  unfold omegaMinusAct
  exact dite_eq_left h

theorem act_e11 (n : ℕ) (l : (Fq (2 * n))ˣ) (hl : l ^ (2 ^ n + 1) = 1) :
    omegaMinusAct n (diagHom _ l) (Multiplicative.ofAdd ⟨e11 n, e11_mem n⟩) =
      Multiplicative.ofAdd ⟨e11 n, e11_mem n⟩ := by
  have hl' : (l : Fq (2 * n)) * (l : Fq (2 * n)) ^ 2 ^ n = 1 := by
    have := congrArg (fun x : (Fq (2 * n))ˣ => (x : Fq (2 * n))) hl
    simpa [pow_succ, mul_comm] using this
  have hmat : ((diagHom _ l : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :
        Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * e11 n *
      (((diagHom _ l : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :
        Matrix (Fin 2) (Fin 2) (Fq (2 * n))).map (frobHalf n)).transpose = e11 n := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_diagHom, diagMat, e11, frobHalf, Matrix.mul_apply, Fin.sum_univ_two, hl']
  have hmem : ((diagHom _ l : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :
        Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * (Multiplicative.toAdd
          (Multiplicative.ofAdd (⟨e11 n, e11_mem n⟩ : hermSub n)) : _) *
      (((diagHom _ l : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :
        Matrix (Fin 2) (Fin 2) (Fq (2 * n))).map (frobHalf n)).transpose ∈ hermSub n := by
    show _ * e11 n * _ ∈ hermSub n
    rw [hmat]
    exact e11_mem n
  rw [omegaMinusAct_of_mem n _ _ hmem]
  exact congrArg Multiplicative.ofAdd (Subtype.ext hmat)

end CFSG.CGT.PushingUpLit.CGT6.Diag.Bound

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Orthogonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.RankThree.PartOne.StrongP CFSG.SectionRank.ClassicalOdd Matrix
open scoped commutatorElement

section Abstract

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] (D : OrthData ι F)

@[expose] noncomputable def wcON (a b : Fin 3) : Matrix ι ι F :=
  Matrix.single (D.X a) (D.X b) 1 - Matrix.single (D.Y b) (D.Y a) 1

theorem wcON_mul_self {a b : Fin 3} (hab : a ≠ b) : wcON D a b * wcON D a b = 0 := by
  simp [wcON, sub_mul, mul_sub, D.injX.eq_iff, D.injY.eq_iff, D.X_ne_Y, D.Y_ne_X, hab,
    hab.symm]

theorem wcON_mul_wcON {a b d : Fin 3} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    wcON D a b * wcON D b d = Matrix.single (D.X a) (D.X d) 1 := by
  simp [wcON, sub_mul, mul_sub, D.injX.eq_iff, D.injY.eq_iff, D.X_ne_Y, D.Y_ne_X, hab, hbd, had,
    hab.symm, hbd.symm, had.symm]

theorem wcON_mul_wcON_rev {a b d : Fin 3} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    wcON D b d * wcON D a b = Matrix.single (D.Y d) (D.Y a) 1 := by
  simp [wcON, sub_mul, mul_sub, D.injX.eq_iff, D.injY.eq_iff, D.X_ne_Y, D.Y_ne_X, hab, hbd, had,
    hab.symm, hbd.symm, had.symm]

theorem wcON_comm {a b d : Fin 3} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    wcON D a b * wcON D b d - wcON D b d * wcON D a b = wcON D a d := by
  rw [wcON_mul_wcON D hab hbd had, wcON_mul_wcON_rev D hab hbd had]
  rfl

theorem wcON_mul_mul {a b d : Fin 3} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    wcON D a b * wcON D b d * wcON D a b = 0 := by
  rw [wcON_mul_wcON D hab hbd had]
  simp [wcON, mul_sub, D.injX.eq_iff, D.injY.eq_iff, D.X_ne_Y, D.Y_ne_X, hab, hbd, had,
    hab.symm, hbd.symm, had.symm]

theorem wcON_rev_mul_mul {a b d : Fin 3} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    wcON D b d * wcON D a b * wcON D b d = 0 := by
  rw [wcON_mul_wcON_rev D hab hbd had]
  simp [wcON, mul_sub, D.injX.eq_iff, D.injY.eq_iff, D.X_ne_Y, D.Y_ne_X, hab, hbd, had,
    hab.symm, hbd.symm, had.symm]

theorem wcO_one_add_mul_one_sub {R : Type*} [Ring R] (M : R) (h : M * M = 0) :
    (1 + M) * (1 - M) = 1 := by
  calc (1 + M) * (1 - M) = 1 - M * M := by noncomm_ring
    _ = 1 := by rw [h, sub_zero]

theorem wcO_one_sub_mul_one_add {R : Type*} [Ring R] (M : R) (h : M * M = 0) :
    (1 - M) * (1 + M) = 1 := by
  calc (1 - M) * (1 + M) = 1 - M * M := by noncomm_ring
    _ = 1 := by rw [h, sub_zero]

theorem wcON_smul_mul_self {a b : Fin 3} (hab : a ≠ b) (c : F) :
    (c • wcON D a b) * (c • wcON D a b) = 0 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, wcON_mul_self D hab, smul_zero, smul_zero]

@[expose] noncomputable def wcOU {a b : Fin 3} (hab : a ≠ b) (c : F) : GL ι F where
  val := 1 + c • wcON D a b
  inv := 1 - c • wcON D a b
  val_inv := wcO_one_add_mul_one_sub _ (wcON_smul_mul_self D hab c)
  inv_val := wcO_one_sub_mul_one_add _ (wcON_smul_mul_self D hab c)

theorem wcOU_val {a b : Fin 3} (hab : a ≠ b) (c : F) :
    ((wcOU D hab c : GL ι F) : Matrix ι ι F) = 1 + c • wcON D a b := rfl

theorem wcOU_inv_val {a b : Fin 3} (hab : a ≠ b) (c : F) :
    (((wcOU D hab c)⁻¹ : GL ι F) : Matrix ι ι F) = 1 - c • wcON D a b := rfl

theorem wcOU_mulVec {a b : Fin 3} (hab : a ≠ b) (c : F) (v : ι → F) :
    (wcOU D hab c : Matrix ι ι F) *ᵥ v =
      v + Pi.single (D.Y b) (-(c * v (D.Y a))) + Pi.single (D.X a) (c * v (D.X b)) := by
  rw [wcOU_val, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, wcON,
    Matrix.sub_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem wcOU_isometry (Q : (ι → F) → F)
    (hQX : ∀ v i a, Q (v + Pi.single (D.X i) a) = Q v + a * v (D.Y i))
    (hQY : ∀ v i a, Q (v + Pi.single (D.Y i) a) = Q v + a * v (D.X i))
    {a b : Fin 3} (hab : a ≠ b) (c : F) (v : ι → F) :
    Q ((wcOU D hab c : Matrix ι ι F) *ᵥ v) = Q v := by
  rw [wcOU_mulVec, hQX, hQY]
  have h : (v + Pi.single (D.Y b) (-(c * v (D.Y a))) : ι → F) (D.Y a) = v (D.Y a) := by
    simp [Pi.single_apply, D.injY.eq_iff, hab]
  rw [h]
  ring

theorem wcO_comm_aux {R : Type*} [Ring R] (a b : R) (ha : a * a = 0) (hb : b * b = 0)
    (haba : a * b * a = 0) (hbab : b * a * b = 0) :
    (1 + a) * (1 + b) * (1 - a) * (1 - b) = 1 + (a * b - b * a) := by
  have h : (1 + a) * (1 + b) * (1 - a) * (1 - b) =
      1 + (a * b - b * a) - a * a - b * b - a * b * a + b * a * b - a * (b * b) + a * a * b +
        a * b * a * b := by
    noncomm_ring
  rw [h, ha, hb, haba, hbab]
  simp

theorem wcOU_comm {a b d : Fin 3} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) (c e : F) :
    ⁅wcOU D hab c, wcOU D hbd e⁆ = wcOU D had (c * e) := by
  apply Units.ext
  rw [commutatorElement_def]
  simp only [Units.val_mul]
  rw [wcOU_inv_val, wcOU_inv_val, wcOU_val, wcOU_val, wcOU_val]
  have h1 : (c • wcON D a b) * (c • wcON D a b) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, wcON_mul_self D hab, smul_zero, smul_zero]
  have h2 : (e • wcON D b d) * (e • wcON D b d) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, wcON_mul_self D hbd, smul_zero, smul_zero]
  have h3 : (c • wcON D a b) * (e • wcON D b d) * (c • wcON D a b) = 0 := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, wcON_mul_mul D hab hbd had, smul_zero]
  have h4 : (e • wcON D b d) * (c • wcON D a b) * (e • wcON D b d) = 0 := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, wcON_rev_mul_mul D hab hbd had, smul_zero]
  rw [wcO_comm_aux _ _ h1 h2 h3 h4]
  congr 1
  rw [← wcON_comm D hab hbd had]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub, mul_comm e c]

theorem wcOU_isUnitri {a b : Fin 3} (hab : a ≠ b) (c : F) {r : ι → ℕ}
    (h1 : r (D.X a) < r (D.X b)) (h2 : r (D.Y b) < r (D.Y a)) : IsUnitri r (wcOU D hab c) := by
  intro i j hij
  rw [wcOU_val, add_sub_cancel_left, Matrix.smul_apply, wcON, Matrix.sub_apply,
    Matrix.single_apply, Matrix.single_apply] at hij
  by_cases hx : D.X a = i ∧ D.X b = j
  · rw [← hx.1, ← hx.2]
    exact h1
  · by_cases hy : D.Y b = i ∧ D.Y a = j
    · rw [← hy.1, ← hy.2]
      exact h2
    · exfalso
      apply hij
      simp [hx, hy]

noncomputable def wcOrank : ι → ℕ :=
  Function.extend D.X (fun a : Fin 3 => (a : ℕ))
    (Function.extend D.Y (fun a : Fin 3 => 5 - (a : ℕ)) (fun _ => 0))

theorem wcOrank_X (a : Fin 3) : wcOrank D (D.X a) = a :=
  D.injX.extend_apply _ _ a

theorem wcOrank_Y (a : Fin 3) : wcOrank D (D.Y a) = 5 - (a : ℕ) := by
  unfold wcOrank
  rw [Function.extend_apply' _ _ _ (fun ⟨a', h⟩ => D.X_ne_Y a' a h)]
  exact D.injY.extend_apply _ _ a

theorem wcOrank_lt (i : ι) : wcOrank D i < 6 := by
  rw [wcOrank, Function.extend_def]
  split_ifs with h1
  · have := (Classical.choose h1).isLt
    omega
  · rw [Function.extend_def]
    split_ifs with h2
    · omega
    · omega

theorem wcO_nonscalarPPair {p : ℕ} [Fact p.Prime] [CharP F p] (Q : (ι → F) → F)
    (hQX : ∀ v i a, Q (v + Pi.single (D.X i) a) = Q v + a * v (D.Y i))
    (hQY : ∀ v i a, Q (v + Pi.single (D.Y i) a) = Q v + a * v (D.X i)) :
    NonscalarPPair p (StatedOmega Q) := by
  haveI : Nonempty ι := ⟨D.X 0⟩
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  set O := Subgroup.closure {A : GL ι F | ∀ v, Q ((A : Matrix ι ι F) *ᵥ v) = Q v}
  have hmem : ∀ {a b : Fin 3} (hab : a ≠ b) (c : F), wcOU D hab c ∈ O := fun {a b} hab c =>
    Subgroup.subset_closure (fun v => wcOU_isometry D Q hQX hQY hab c v)
  have hx : wcOU D h01 1 ∈ StatedOmega Q := by
    change _ ∈ ⁅O, O⁆
    have := Subgroup.commutator_mem_commutator (hmem h02 1) (hmem h21 1)
    rw [wcOU_comm D h02 h21 h01, mul_one] at this
    exact this
  have hy : wcOU D h12 1 ∈ StatedOmega Q := by
    change _ ∈ ⁅O, O⁆
    have := Subgroup.commutator_mem_commutator (hmem h10 1) (hmem h02 1)
    rw [wcOU_comm D h10 h02 h12, mul_one] at this
    exact this
  refine NonscalarPPair.of_unitri (r := wcOrank D) (m := 6) (wcOrank_lt D) hx hy
    (wcOU_isUnitri D h01 1 ?_ ?_) (wcOU_isUnitri D h12 1 ?_ ?_) ?_
  · rw [wcOrank_X, wcOrank_X]
    decide
  · rw [wcOrank_Y, wcOrank_Y]
    decide
  · rw [wcOrank_X, wcOrank_X]
    decide
  · rw [wcOrank_Y, wcOrank_Y]
    decide
  · intro h
    have h1 : ⁅wcOU D h01 1, wcOU D h12 1⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
    rw [wcOU_comm D h01 h12 h02, mul_one] at h1
    have h2 := congrArg (fun u : GL ι F => (u : Matrix ι ι F) (D.X 0) (D.X 2)) h1
    simp [wcOU_val, wcON, Matrix.single_apply, D.injX.eq_iff, D.Y_ne_X] at h2

end Abstract

section Forms

variable {K : Type} [Field K] {n : ℕ}

theorem wcO_quadOdd_Y (hn : 3 ≤ n) (v : Fin n ⊕ Fin n ⊕ Unit → K) (i : Fin 3) (a : K) :
    StatedQuadOdd n K (v + Pi.single ((oddData (K := K) hn).Y i) a) =
      StatedQuadOdd n K v + a * v ((oddData (K := K) hn).X i) := by
  simp only [StatedQuadOdd, oddData, Pi.add_apply, Pi.single_apply, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, ↓reduceIte, add_zero, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  ring

theorem wcO_quadPlus_Y (hn : 4 ≤ n) (v : Fin n ⊕ Fin n → K) (i : Fin 3) (a : K) :
    StatedQuadPlus n K (v + Pi.single ((plusData (K := K) hn).Y i) a) =
      StatedQuadPlus n K v + a * v ((plusData (K := K) hn).X i) := by
  simp only [StatedQuadPlus, plusData, Pi.add_apply, Pi.single_apply, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, ↓reduceIte, add_zero, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  ring

theorem wcO_quadMinus_Y (hn : 4 ≤ n) (b c : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (i : Fin 3) (a : K) :
    StatedQuadMinus n K b c (v + Pi.single ((minusData hn b).Y i) a) =
      StatedQuadMinus n K b c v + a * v ((minusData hn b).X i) := by
  simp only [StatedQuadMinus, minusData, Pi.add_apply, Pi.single_apply, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, ↓reduceIte, add_zero, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  ring

end Forms

theorem wcOn_pomegaOdd {K : Type} [Group K] [Finite K] {n p f : ℕ} [Fact p.Prime] (_hp2 : p ≠ 2)
    (hn : 3 ≤ n) (h : CFSG.Open.StatedClassicalModel K .POmegaOdd n p f) : WCOn p K := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  haveI := CFSG.SectionRank.ClassicalOdd.charP_of_card hF
  exact (wcO_nonscalarPPair (p := p) (oddData hn) _ (quadOdd_X hn) (wcO_quadOdd_Y hn)).wcOn e

theorem wcOn_pomegaPlus {K : Type} [Group K] [Finite K] {n p f : ℕ} [Fact p.Prime] (_hp2 : p ≠ 2)
    (hn : 4 ≤ n) (h : CFSG.Open.StatedClassicalModel K .POmegaPlus n p f) : WCOn p K := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  haveI := CFSG.SectionRank.ClassicalOdd.charP_of_card hF
  exact (wcO_nonscalarPPair (p := p) (plusData hn) _ (quadPlus_X hn) (wcO_quadPlus_Y hn)).wcOn e

theorem wcOn_pomegaMinus {K : Type} [Group K] [Finite K] {n p f : ℕ} [Fact p.Prime]
    (_hp2 : p ≠ 2) (hn : 4 ≤ n) (h : CFSG.Open.StatedClassicalModel K .POmegaMinus n p f) :
    WCOn p K := by
  obtain ⟨-, F, _, _, hF, b, c, -, ⟨e⟩⟩ := h
  haveI := CFSG.SectionRank.ClassicalOdd.charP_of_card hF
  exact (wcO_nonscalarPPair (p := p) (minusData hn b) _ (quadMinus_X hn b c)
    (wcO_quadMinus_Y hn b c)).wcOn e

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

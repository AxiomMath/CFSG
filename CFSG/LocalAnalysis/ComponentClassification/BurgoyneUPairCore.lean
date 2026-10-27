module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUPairComp

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (commutator_eq_self_of_isQuasisimple
  mem_of_mem_oddCoreIn eq_scalar_of_commute_single)
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {m : ℕ}

theorem prDual_transvection {i j : Fin m} (hij : i ≠ j) (c : K) :
    prDual h (Matrix.SpecialLinearGroup.transvection hij c) =
      1 - h.bar c • single j i 1 := by
  rw [prDual, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext x y
  simp only [transpose_apply, map_apply, Matrix.add_apply, Matrix.sub_apply, one_apply,
    single_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    have h1 : ¬ (i = x ∧ j = x) := fun e => hij (e.1.trans e.2.symm)
    have h2 : ¬ (j = x ∧ i = x) := fun e => hij (e.2.trans e.1.symm)
    simp only [h1, h2, ↓reduceIte, add_zero, map_one, mul_zero, sub_zero]
  · simp only [hxy, Ne.symm hxy, ↓reduceIte, zero_add, zero_sub]
    split_ifs <;> simp_all

theorem coe_prSLHom_transvection (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    {i j : Fin m} (hij : i ≠ j) (c : K) :
    (((prSLHom h h2 hl hN (Matrix.SpecialLinearGroup.transvection hij c) :
      StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
        Matrix (Fin (m + m)) (Fin (m + m)) K) =
      prPhi m l (1 + single i j c) (1 - h.bar c • single j i 1) := by
  rw [coe_prSLHom, prDual_transvection h hij, Matrix.SpecialLinearGroup.transvection_coe]

theorem prA_mul_self (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) :
    prA m l * prA m l = (l ^ 2) • 1 := by
  rw [prA_eq_prPhi h2 hl, prPhi_mul h2 hl]
  rw [show (l • (1 : Matrix (Fin m) (Fin m) K)) * (l • 1) = (l ^ 2) • 1 by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, sq],
    show (-(l • (1 : Matrix (Fin m) (Fin m) K))) * (-(l • 1)) = (l ^ 2) • 1 by
      rw [neg_mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, sq],
    prPhi_smul, prPhi_one h2 hl]

theorem paired_oddCoreIn (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))).range ≤ B)
    {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    {y : MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))}
    (hy : y ∈ oddCoreIn B (uConjAut h (by omega) (uPairA h h2 hl hN))) :
    ∃ (a b : K) (D : uU h (m + m)), h.bar a * b = 1 ∧
      ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        prPhi m l (a • 1) (b • 1) ∧ y = uConjAut h (by omega) D := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hn : 3 ≤ m + m := by omega
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(m + m = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  have hK4 : 4 ≤ Nat.card K := by
    rw [h.card]
    have := h.prime.two_le
    have := h.one_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by omega)
  set A₀ := uPairA (m := m) h h2 hl hN with hA₀
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hyBC := mem_of_mem_oddCoreIn hy
  obtain ⟨D, φ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq y
  have hφm : φ ^ orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) φ) = 1 :=
    fieldAut_pow_eq_one h hn hq (pow_orderOf_eq_one _)
  have hlift : ∀ g : StatedSU (m + m) (p ^ f) K,
      (uConjAut h (by omega) A₀) (projH (StatedSU (m + m) (p ^ f) K) g) =
        projH (StatedSU (m + m) (p ^ f) K) (uLift h A₀ 1 g) := by
    intro g
    rw [← uLift_proj h (by omega) A₀ 1 g, map_one, mul_one]
  set L := (prSLHom (m := m) h h2 hl hN).range with hL
  have hQ := isQuasisimple_range_prSLHom h h2 hl hN hm hK4
  have hQF : L ≤ MonoidHom.eqLocus (uLift h A₀ 1) (MonoidHom.id _) := by
    rintro _ ⟨G, rfl⟩
    exact (uLift_one_eq_iff h A₀ _).2 (by rw [hA₀, coe_uPairA, coe_prSLHom,
      prPhi_commute_prA h2 hl])
  have hQn : ∀ x ∈ MonoidHom.eqLocus (uLift h A₀ 1) (MonoidHom.id _), ∀ g ∈ L,
      x * g * x⁻¹ ∈ L := by
    intro x hx g hg
    have hx' := (uLift_one_eq_iff h A₀ x).1 hx
    rw [hA₀, coe_uPairA] at hx'
    exact conj_mem_range_prSLHom h h2 hl hN hx' hg
  have hcomp : ∀ g ∈ L, ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *
      ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K).map φ *
      (((D : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
        Matrix (Fin (m + m)) (Fin (m + m)) K) =
      ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) := fun g hg =>
    uSemilinear_eq_of_fix h (by omega) (commutator_eq_self_of_isQuasisimple hQ)
      (fun g' hg' => commute_oddCoreIn_of_normal hinj hB (uLift h A₀ 1) hlift hQF hQn
        (isQuasisimple_map_conjProjH hinj hQ) hy hg') hg
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
  set N := prPhi m l (single (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ (1 : K))
    (-single (⟨1, by omega⟩ : Fin m) ⟨0, by omega⟩ (1 : K)) with hNdef
  have hNe : N (finSumFinEquiv (Sum.inl ⟨0, by omega⟩)) (finSumFinEquiv (Sum.inl ⟨1, by omega⟩))
      ≠ 0 := by
    rw [hNdef, prPhi_eq h2 hl, prFin_apply, fromBlocks_apply₁₁]
    simp [Matrix.smul_apply, h2]
  have hφ : φ = 1 := by
    refine eq_one_of_odd_of_fix h hodd hφm (fix_of_conj_family h (D := (D : GL (Fin (m + m)) K))
      hNe fun c hc => ?_)
    have e := hcomp _ ⟨Matrix.SpecialLinearGroup.transvection h01 c, rfl⟩
    rw [coe_prSLHom_transvection h h2 hl hN h01 c, hc] at e
    have e' : prPhi m l (1 + single (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ c)
        (1 - c • single (⟨1, by omega⟩ : Fin m) ⟨0, by omega⟩ 1) = 1 + c • N := by
      rw [hNdef, ← prPhi_smul, ← prPhi_one h2 hl, ← prPhi_add, smul_neg, ← sub_eq_add_neg]
      simp only [smul_single, smul_eq_mul, mul_one]
    rwa [e'] at e
  subst hφ
  simp only [map_one, mul_one] at hodd hyBC hy ⊢
  set Dm := ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) with hDm
  set Dmi := (((D : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
    Matrix (Fin (m + m)) (Fin (m + m)) K) with hDmi
  have hDiD : Dmi * Dm = 1 := by rw [hDm, hDmi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hA₀2 : uConjAut h (by omega) (A₀ * A₀) = 1 := by
    refine (uConjAut_eq_one_iff h hn _).2 ⟨Units.mk0 (l ^ 2) (pow_ne_zero 2 hl), Units.ext ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hA₀, coe_uPairA, prA_mul_self h2 hl,
      GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl
  have hcD : D * A₀ = A₀ * D :=
    uCommute_of_odd h hn hA₀2 hodd (mem_centralizer_singleton_iff.1 hyBC.2)
  have hcA : Dm * prA m l = prA m l * Dm := by
    have e := congrArg (fun x : uU h (m + m) =>
      ((x : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K)) hcD
    simp only [Subgroup.coe_mul, Units.val_mul, hA₀, coe_uPairA] at e
    exact e
  obtain ⟨P, Q, hPQ⟩ := exists_prPhi_of_commute h2 hl hcA
  have hcL : ∀ G : SL(m, K), Dm * prPhi m l G (prDual h G) = prPhi m l G (prDual h G) * Dm := by
    intro G
    have e := hcomp _ ⟨G, rfl⟩
    rw [map_one_ringEquiv, coe_prSLHom] at e
    calc Dm * prPhi m l G (prDual h G) = Dm * prPhi m l G (prDual h G) * (Dmi * Dm) := by
          rw [hDiD, Matrix.mul_one]
      _ = prPhi m l G (prDual h G) * Dm := by rw [← Matrix.mul_assoc, e]
  have hPQc : ∀ i j : Fin m, i ≠ j → P * single i j 1 = single i j 1 * P ∧
      Q * single j i 1 = single j i 1 * Q := by
    intro i j hij
    have e := hcL (Matrix.SpecialLinearGroup.transvection hij 1)
    rw [prDual_transvection h hij, map_one, one_smul, Matrix.SpecialLinearGroup.transvection_coe,
      hPQ, prPhi_mul h2 hl, prPhi_mul h2 hl] at e
    obtain ⟨e1, e2⟩ := prPhi_inj h2 hl e
    constructor
    · rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at e1
      exact add_left_cancel e1
    · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at e2
      exact sub_right_injective e2
  set a₀ : Fin m := ⟨0, by omega⟩ with ha₀
  have hP : P = Matrix.scalar (Fin m) (P a₀ a₀) :=
    eq_scalar_of_commute_single a₀ fun i j hij => (hPQc i j hij).1
  have hQ : Q = Matrix.scalar (Fin m) (Q a₀ a₀) :=
    eq_scalar_of_commute_single a₀ fun i j hij => (hPQc j i (Ne.symm hij)).2
  have hsc : ∀ c : K, Matrix.scalar (Fin m) c = c • 1 := fun c => by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  refine ⟨P a₀ a₀, Q a₀ a₀, D, ?_, ?_, rfl⟩
  · have hU : (Dm.map h.bar)ᵀ * Dm = 1 := (mem_uU h).1 D.2
    rw [hPQ, prPhi_unitary_iff h h2 hl hN, hP, hQ, hsc, hsc, smul_one_map h,
      Matrix.smul_mul, Matrix.one_mul, smul_smul] at hU
    have e := congrFun (congrFun hU a₀) a₀
    simpa [Matrix.smul_apply] using e
  · change Dm = _
    rw [hPQ]
    nth_rewrite 1 [hP]
    nth_rewrite 1 [hQ]
    rw [hsc, hsc]

end CFSG.ComponentClassification.Burgoyne.U

module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUTools
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUFam

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (commutator_eq_self_of_isQuasisimple
  eq_scalar_of_commute_single)
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {m : ℕ}

theorem ClU.paired_core (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))))
    {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    {R : Subgroup (MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * uConjAut h (by omega) (uPairA (m := m) h h2 hl hN) =
      uConjAut h (by omega) (uPairA (m := m) h h2 hl hN) * y)
    (hRc : ∀ s, uConjAut h (by omega) (uPairA (m := m) h h2 hl hN) s = s → Odd (orderOf s) →
      ∀ y ∈ R, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R)
    {y : MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))} (hy : y ∈ R) :
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
  have hodd := ClSp.odd_orderOf_of_mem hRodd hy
  have hyBC := hRi _ hy
  obtain ⟨D, φ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq y
  have hφm : φ ^ orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) φ) = 1 :=
    fieldAut_pow_eq_one h hn hq (pow_orderOf_eq_one _)
  have hlift : ∀ g : StatedSU (m + m) (p ^ f) K,
      (uConjAut h (by omega) A₀) (projH (StatedSU (m + m) (p ^ f) K) g) =
        projH (StatedSU (m + m) (p ^ f) K) (uLift h A₀ 1 g) := by
    intro g
    rw [← uLift_proj h (by omega) A₀ 1 g, map_one, mul_one]
  have hliftinj : Function.Injective (uLift h A₀ 1) := by
    intro g₁ g₂ e
    have e' : (A₀ : GL (Fin (m + m)) K) * (g₁ : GL (Fin (m + m)) K) *
        (A₀ : GL (Fin (m + m)) K)⁻¹ = (A₀ : GL (Fin (m + m)) K) *
        (g₂ : GL (Fin (m + m)) K) * (A₀ : GL (Fin (m + m)) K)⁻¹ := by
      apply Units.ext
      have := congrArg (fun g : StatedSU (m + m) (p ^ f) K =>
        ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K)) e
      simpa only [coe_uLift, map_one_ringEquiv, Units.val_mul] using this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel e'))
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
      (fun g' hg' => ClU.fix_of_lift hinj hRodd hRi hRc (uLift h A₀ 1) hliftinj hlift hQF hQn
        hQ hy hg') hg
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
  have hcD : D * A₀ = A₀ * D := uCommute_of_odd h hn hA₀2 hodd hyBC
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

theorem ClU.uPairedInput : ClU.UPairedInput := by
  intro p f K _ h hp2 n hn hinj A l hl0 hlN hAA R hRodd hRi hRc
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := h.prime.two_le
    exact hp2 (by omega)
  set M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hU : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hNi : h.bar l⁻¹ * l⁻¹ = -1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hlN, inv_neg, inv_one]
  have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = -1 := by
    rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, neg_one_smul]
  have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  obtain ⟨m, rfl⟩ := exists_half_of_antiunitary h h2 hU' hA'2
  have hm : 2 ≤ m := by omega
  obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form h h2 hU' hA'2 hl0 hlN
  set HG := uGL h Hm hHU with hHG
  have hHi : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) = (Hm.map h.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) * M *
      ((HG : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        (1 : K) • ((uPairA (m := m) h h2 hl0 hlN : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) := by
    rw [hHi, coe_uGL, coe_uPairA, one_smul]
    have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
    congr 2
    · rw [smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · rw [smul_smul, ← sq]
    · rw [smul_zero]
  refine commute_of_congr (uConjAut h (by omega) ⟨HG, uGL_mem h _ _⟩)⁻¹
    (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  have hcg : MulAut.congr (uConjAut h (by omega) ⟨HG, uGL_mem h _ _⟩)⁻¹
      (uConjAut h (by omega) A) = uConjAut h (by omega) (uPairA (m := m) h h2 hl0 hlN) := by
    rw [congr_eq_conj, inv_inv, ← map_inv, ← map_mul, ← map_mul]
    refine uConjAut_eq_of_eq_smul h hn one_ne_zero ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
    exact hconj
  rw [hcg] at hR'i hR'c
  intro r₁ h₁ r₂ h₂
  obtain ⟨a, b, D, -, hD, rfl⟩ := ClU.paired_core h hp2 h2 hm hinj hl0 hlN hR'odd hR'i hR'c h₁
  obtain ⟨a', b', D', -, hD', rfl⟩ :=
    ClU.paired_core h hp2 h2 hm hinj hl0 hlN hR'odd hR'i hR'c h₂
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hD, hD',
    prPhi_mul h2 hl0, prPhi_mul h2 hl0]
  congr 1 <;> rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm]

end CFSG.ComponentClassification.Foote5.OddLieCore

module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoPair

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false


namespace A2Pair

variable {σ τ : Fin 3 → Fin 3 → V4} {κ κ' : ℤ} {L : Type} [Field L]
  {ψ ψ' : SL(3, L) →* ModGL Tag.F4 L}

private theorem zpow_add_mul_inv_mul_zpow (x y : Lˣ) (A B : ℤ) :
    x ^ (A + B) * (x⁻¹ * y) ^ B = x ^ A * y ^ B := by
  rw [mul_zpow, inv_zpow', zpow_add, mul_assoc, ← mul_assoc (x ^ B), ← zpow_add, add_neg_cancel,
    zpow_zero, one_mul]

private theorem rootChar_mul_tuple (a b : Fin Tag.F4.rank → Lˣ) (v : V4) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem rootChar_single_one (a : Fin Tag.F4.rank → Lˣ) (i : Fin Tag.F4.rank) :
    rootChar a (Pi.single i 1) = a i := by
  have := rootChar_nsmul_single a i 1
  rwa [one_smul, pow_one] at this

private theorem diagParam_prod (s₁ s₂ : Lˣ) :
    (![s₁, s₁⁻¹ * s₂, s₂⁻¹] : Fin 3 → Lˣ) 0 * ![s₁, s₁⁻¹ * s₂, s₂⁻¹] 1 *
      ![s₁, s₁⁻¹ * s₂, s₂⁻¹] 2 = 1 := by
  simp

variable [IsAlgClosed L]

theorem exists_diag_mul_diag_eq (h : A2Pair σ τ κ κ') (hψ : IsA2Frame ψ σ)
    (hψ' : IsA2Frame ψ' τ) (b : Fin Tag.F4.rank → Lˣ) :
    ∃ (l : Fin 3 → Lˣ) (hl : l 0 * l 1 * l 2 = 1) (l' : Fin 3 → Lˣ)
      (hl' : l' 0 * l' 1 * l' 2 = 1),
      ψ (diagSL3 l hl) * ψ' (diagSL3 l' hl') = rootDiagUnit Tag.F4 b := by
  choose c hc using fun i => exists_cube_root (L := L) (b i)
  have hl := diagParam_prod (rootChar c ((2 : ℤ) • σ 0 1 + σ 1 2))
    (rootChar c (σ 0 1 + (2 : ℤ) • σ 1 2))
  have hl' := diagParam_prod (rootChar c ((2 : ℤ) • τ 0 1 + τ 1 2))
    (rootChar c (τ 0 1 + (2 : ℤ) • τ 1 2))
  obtain ⟨d, hd⟩ := exists_param_of_diag hψ _ hl
  obtain ⟨d', hd'⟩ := exists_param_of_diag hψ' _ hl'
  refine ⟨_, hl, _, hl', ?_⟩
  rw [hd, hd', ← rootDiagUnit_mul]
  congr 1
  have hchar : ∀ v : V4, rootChar (d * d') v = rootChar b v := by
    intro v
    obtain ⟨A, B, A', B', h1, h2, h3, h4, h5⟩ := h.exists_dec v
    have eA : lab1 σ κ v = A := by rw [lab1, h1, Int.mul_ediv_cancel_left _ h.κ_ne_zero]
    have eB : lab2 σ κ v = B := by rw [lab2, h2, Int.mul_ediv_cancel_left _ h.κ_ne_zero]
    have eA' : lab1 τ κ' v = A' := by
      rw [lab1, h3, Int.mul_ediv_cancel_left _ h.symm.κ_ne_zero]
    have eB' : lab2 τ κ' v = B' := by
      rw [lab2, h4, Int.mul_ediv_cancel_left _ h.symm.κ_ne_zero]
    have hb : b = c ^ 3 := funext fun i => (hc i).symm
    have h3v : (3 : ℤ) • v = A • ((2 : ℤ) • σ 0 1 + σ 1 2) + B • (σ 0 1 + (2 : ℤ) • σ 1 2) +
        A' • ((2 : ℤ) • τ 0 1 + τ 1 2) + B' • (τ 0 1 + (2 : ℤ) • τ 1 2) := by
      rw [h5]
      module
    have hcube : rootChar c v ^ 3 = rootChar c ((3 : ℤ) • v) := by
      rw [rootChar_zsmul]
      norm_cast
    have hR : ∀ x y z w : V4, rootChar c (A • x + B • y + A' • z + B' • w) =
        rootChar c x ^ A * rootChar c y ^ B * (rootChar c z ^ A' * rootChar c w ^ B') := by
      intro x y z w
      rw [rootChar_add, rootChar_add, rootChar_add, rootChar_zsmul, rootChar_zsmul, rootChar_zsmul,
        rootChar_zsmul, mul_assoc]
    rw [rootChar_mul_tuple, h.diag_chars hψ hd v, h.symm.diag_chars hψ' hd' v, eA, eB, eA', eB',
      hb, rootChar_pow, hcube, h3v, hR]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [zpow_add_mul_inv_mul_zpow, zpow_add_mul_inv_mul_zpow]
  funext i
  have := hchar (Pi.single i 1)
  rwa [rootChar_single_one, rootChar_single_one] at this

theorem torusGroup_le_sup_range (h : A2Pair σ τ κ κ') (hψ : IsA2Frame ψ σ)
    (hψ' : IsA2Frame ψ' τ) : torusGroup Tag.F4 L ≤ ψ.range ⊔ ψ'.range := by
  intro x hx
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  obtain ⟨l, hl, l', hl', he⟩ := h.exists_diag_mul_diag_eq hψ hψ' b
  rw [← he]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)

end A2Pair

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

end

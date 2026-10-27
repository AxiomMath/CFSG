module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightDim
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Data
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
import CFSG.GH74.GLS.IVK.L2.TorusMatrices
import CFSG.LocalAnalysis.SteinbergBSCharTwoSLTwoOdd
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSL2
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts.Levi

set_option linter.unusedSectionVars false

section Torus


theorem rootTorusSL2_eq_thetaDiag_e6 {L : Type} [Field L] {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot .E6 β) (c : Lˣ) :
    rootTorusSL2 .E6 L β c = rootDiagUnit .E6 (thetaDiag β c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .E6 L hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .E6 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .E6 a : ModGL .E6 L) : Module.End L (RootModule .E6 L))
      (rootVec .E6 L (Pi.single i 1))) = ((a i : Lˣ) : L) • rootVec .E6 L (Pi.single i 1) := by
    change rootDiag a (rootVec .E6 L (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .E6 i), hs]
  rw [h2] at h1
  have hne : rootVec .E6 L (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E6 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective L hne h1
  have h4 : 2 * iform β (Pi.single i 1) / iform β β = iform β (Pi.single i 1) := by
    rw [iform_self_isRoot_E6 hβ]
    omega
  rw [h4] at h3
  exact Units.ext h3

end Torus

section SL2

variable {L : Type} [Field L]

theorem exists_conj_HSL_of_orderOf_nine [IsAlgClosed L] [CharP L 2] (A : SL2 L)
    (hA : orderOf A = 9) : ∃ (P : SL2 L) (μ : Lˣ), orderOf μ = 9 ∧ A = P * HSL μ * P⁻¹ := by
  set t : L := (A : Matrix (Fin 2) (Fin 2) L) 0 0 + (A : Matrix (Fin 2) (Fin 2) L) 1 1 with ht
  obtain ⟨a, ha⟩ : ∃ a : L, a ^ 2 - t * a + 1 = 0 := by
    have hdeg : (Polynomial.C (1 : L) * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X +
        Polynomial.C 1).degree ≠ 0 := by
      rw [Polynomial.degree_quadratic one_ne_zero]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨a, ?_⟩
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at ha
    linear_combination ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hab : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  have htr : t = a + a⁻¹ := by
    field_simp
    linear_combination -ha
  have hne : a ≠ a⁻¹ := by
    intro h
    have ht0 : t = 0 := by
      rw [htr, ← h]
      exact CharTwo.add_self_eq_zero a
    have hsq : A ^ 2 = 1 := by
      rw [pow_two]
      refine CFSG.LocalAnalysis.SteinbergBS.sq_eq_one_of_trace_eq_zero A ?_
      rw [Matrix.trace_fin_two]
      exact ht0
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [hA] at hd
    omega
  obtain ⟨P, hP⟩ :=
    CFSG.GH74.GLS.IVK.L2Torus.exists_conj_mem_diagSub_of_eigenvalue hab hne htr
  set D : SL2 L := P⁻¹ * A * P with hD
  have hD01 : (D : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := hP.1
  have hD10 : (D : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := hP.2
  have hdetD := det_SL2 D
  rw [hD01, hD10, mul_zero, sub_zero] at hdetD
  have hD00 : (D : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdetD
  have hD11 : (D : Matrix (Fin 2) (Fin 2) L) 1 1 = ((D : Matrix (Fin 2) (Fin 2) L) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdetD
  have hDH : D = HSL (Units.mk0 _ hD00) := by
    apply SL2_ext
    · simp [coe_HSL]
    · simp [coe_HSL, hD01]
    · simp [coe_HSL, hD10]
    · simp [coe_HSL, hD11]
  have hAD : A = P * D * P⁻¹ := by rw [hD]; group
  have hordD : orderOf D = 9 := by
    have := orderOf_injective (MulAut.conj P⁻¹).toMonoidHom (MulAut.conj P⁻¹).injective A
    rw [hA] at this
    rw [← this]
    simp [hD]
  refine ⟨P, Units.mk0 _ hD00, ?_, by rw [← hDH]; exact hAD⟩
  have := orderOf_injective (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom L)
    (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_injective) (Units.mk0 _ hD00)
  rw [← this]
  rw [CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply, ← hDH]
  exact hordD

end SL2

section Pair


theorem conj_ne_pow_of_mem_rootPair {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) {y : ModGL .E6 L}
    (hy : y ∈ rootSubgroup .E6 L β ⊔ rootSubgroup .E6 L (-β)) (hy9 : orderOf y = 9)
    (x : ModGL .E6 L) {k : ℕ} (hk : k = 4 ∨ k = 7) : x * y * x⁻¹ ≠ y ^ k := by
  rw [← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ] at hy
  obtain ⟨A, rfl⟩ := hy
  have hA : orderOf A = 9 := by
    rw [← orderOf_injective (rootSL2 .E6 L β)
      (CFSG.RankThree.Chevalley.rootSL2_injective_of_field β) A]
    exact hy9
  obtain ⟨P, μ, hμ, rfl⟩ := exists_conj_HSL_of_orderOf_nine A hA
  intro h
  set Q : ModGL .E6 L := rootSL2 .E6 L β P with hQ
  set a : Fin Tag.E6.rank → Lˣ := thetaDiag β μ with ha
  set d : ModGL .E6 L := rootDiagUnit .E6 a with hd
  have hyQ : rootSL2 .E6 L β (P * HSL μ * P⁻¹) = Q * d * Q⁻¹ := by
    rw [map_mul, map_mul, map_inv, hQ, hd, ha, ← rootTorusSL2_eq_thetaDiag_e6 hβ μ]
    rfl
  rw [hyQ, conj_pow] at h
  have hconj : (Q⁻¹ * x * Q) * d * (Q⁻¹ * x * Q)⁻¹ = d ^ k := by
    calc (Q⁻¹ * x * Q) * d * (Q⁻¹ * x * Q)⁻¹
        = Q⁻¹ * (x * (Q * d * Q⁻¹) * x⁻¹) * Q := by group
      _ = Q⁻¹ * (Q * d ^ k * Q⁻¹) * Q := by rw [h]
      _ = d ^ k := by group
  have hcomm : (Q⁻¹ * x * Q) * d = d ^ k * (Q⁻¹ * x * Q) := by
    rwa [mul_inv_eq_iff_eq_mul] at hconj
  set m : RootModule .E6 L ≃ₗ[L] RootModule .E6 L :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (Q⁻¹ * x * Q) with hm
  have hmk : ∀ v, m ((rootDiag a) v) = ((rootDiag a) ^ k) (m v) := by
    intro v
    have h1 := congrArg (fun g : ModGL .E6 L => (g : Module.End L (RootModule .E6 L)) v) hcomm
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Module.End.mul_apply] at h1
    exact h1
  have hμk := finrank_ker_sub_smul_le_of_conj_pow (rootDiag a) m k hmk (μ : L)
  have hβ' : β ∈ rootFinset .E6 := mem_rootFinset.2 hβ
  have hchar : ∀ α ∈ rootFinset .E6, rootChar a α = μ ^ iform α β := by
    intro α _
    rw [ha, rootChar_thetaDiag, iform_comm]
  have hlt := finrank_ker_rootDiag_pow_lt hβ' hμ hchar hk
  rw [← Units.val_pow_eq_pow_val] at hμk
  omega

end Pair

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight

module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriCentHolds
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ApClass
import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJRoots
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonL2Holds
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeSing
import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryGraph

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section MatCube

open Matrix Polynomial

private theorem triD4J_mat_cube {L : Type} [Field L] [IsAlgClosed L] (h3 : (3 : L) ≠ 0)
    (A : Matrix (Fin 3) (Fin 3) L) (hA : A ^ 3 = 1) (hdet : A.det = 1) :
    (∃ c : L, A = Matrix.scalar (Fin 3) c) ∨
      ∀ X Y : Matrix (Fin 3) (Fin 3) L, X * A = A * X → Y * A = A * Y → X * Y = Y * X := by
  classical
  set χ := A.charpoly with hχ
  have hmon : χ.Monic := Matrix.charpoly_monic A
  have hdeg : χ.natDegree = 3 := by rw [hχ, Matrix.charpoly_natDegree_eq_dim]; simp
  have hc3 : χ.coeff 3 = 1 := by
    have := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  have hc0 : χ.coeff 0 = -1 := by
    have h := Matrix.det_eq_sign_charpoly_coeff A
    rw [hdet, Fintype.card_fin] at h
    rw [← hχ] at h
    linear_combination h
  have hCH : χ.coeff 0 • (1 : Matrix (Fin 3) (Fin 3) L) + χ.coeff 1 • A + χ.coeff 2 • A ^ 2 +
      χ.coeff 3 • A ^ 3 = 0 := by
    have h := Matrix.aeval_self_charpoly A
    rw [← hχ, Polynomial.aeval_eq_sum_range, hdeg] at h
    simpa [Finset.sum_range_succ] using h
  rw [hc0, hc3, hA, one_smul] at hCH
  have h1 : χ.coeff 1 • A + χ.coeff 2 • A ^ 2 = 0 := by
    have : (-1 : L) • (1 : Matrix (Fin 3) (Fin 3) L) + χ.coeff 1 • A + χ.coeff 2 • A ^ 2 + 1 =
        χ.coeff 1 • A + χ.coeff 2 • A ^ 2 := by
      rw [neg_one_smul]; abel
    rw [← this, hCH]
  have h2 : χ.coeff 1 • (1 : Matrix (Fin 3) (Fin 3) L) + χ.coeff 2 • A = 0 := by
    have := congrArg (fun B => A ^ 2 * B) h1
    have hA3' : A ^ 2 * A = 1 := by rw [← pow_succ, hA]
    have hA4' : A ^ 2 * A ^ 2 = A := by
      rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, hA, one_mul]
    simp only [mul_add, mul_smul_comm, mul_zero, hA3', hA4'] at this
    exact this
  by_cases hc2 : χ.coeff 2 = 0
  · right
    rw [hc2, zero_smul, add_zero] at h2
    have hc1 : χ.coeff 1 = 0 := by
      have := congrArg (fun B => B 0 0) h2
      simpa using this
    have hev : ∀ t : L, χ.eval t = t ^ 3 - 1 := by
      intro t
      rw [Polynomial.eval_eq_sum_range, hdeg]
      simp [Finset.sum_range_succ, hc0, hc1, hc2, hc3]
      ring
    have hdq : (X ^ 2 + X + 1 : L[X]).degree ≠ 0 := by
      rw [show (X ^ 2 + X + 1 : L[X]).degree = 2 by compute_degree!]
      norm_num
    obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (X ^ 2 + X + 1 : L[X]) hdq
    have hω2 : ω ^ 2 + ω + 1 = 0 := by simpa [Polynomial.IsRoot] using hω
    have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω2
    have hω1 : ω ≠ 1 := by
      rintro rfl
      apply h3
      linear_combination hω2
    have hω0 : ω ≠ 0 := by
      rintro rfl
      norm_num at hω3
    have hωω : ω ^ 2 ≠ ω := by
      intro h
      apply hω1
      have : ω * (ω - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hω0
      · linear_combination h0
    have hω21 : ω ^ 2 ≠ 1 := by
      intro h
      apply hω1
      have : ω ^ 3 = ω * ω ^ 2 := by ring
      rw [hω3, h, mul_one] at this
      exact this.symm
    set μ : Fin 3 → L := ![1, ω, ω ^ 2] with hμ
    have hμ0 : μ 0 = 1 := rfl
    have hμ1 : μ 1 = ω := rfl
    have hμ2 : μ 2 = ω ^ 2 := rfl
    have hμinj : Function.Injective μ := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd (hμ0.symm.trans (hij.trans hμ1)).symm hω1
      · exact absurd (hμ0.symm.trans (hij.trans hμ2)).symm hω21
      · exact absurd (hμ1.symm.trans (hij.trans hμ0)) hω1
      · rfl
      · exact absurd (hμ1.symm.trans (hij.trans hμ2)).symm hωω
      · exact absurd (hμ2.symm.trans (hij.trans hμ0)) hω21
      · exact absurd (hμ2.symm.trans (hij.trans hμ1)) hωω
      · rfl
    have hμ3 : ∀ i, μ i ^ 3 = 1 := by
      intro i
      fin_cases i
      · change μ 0 ^ 3 = 1
        rw [hμ0, one_pow]
      · change μ 1 ^ 3 = 1
        rw [hμ1, hω3]
      · change μ 2 ^ 3 = 1
        rw [hμ2, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hω3, one_pow]
    have hev' : ∀ i, ∃ v : Fin 3 → L, v ≠ 0 ∧ A *ᵥ v = μ i • v := by
      intro i
      have hdet0 : (Matrix.scalar (Fin 3) (μ i) - A).det = 0 := by
        rw [← Matrix.eval_charpoly, ← hχ, hev, hμ3, sub_self]
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
      refine ⟨v, hv0, ?_⟩
      rw [Matrix.sub_mulVec, sub_eq_zero] at hv
      rw [← hv]
      simp [Matrix.scalar_apply, Matrix.smul_mulVec]
    choose v hv0 hv using hev'
    have hli : LinearIndependent L v := by
      refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) μ hμinj v fun i => ?_
      refine ⟨?_, hv0 i⟩
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hv i
    set P : Matrix (Fin 3) (Fin 3) L := Matrix.of fun i j => v j i with hP
    have hPu : IsUnit P := by
      rw [← Matrix.linearIndependent_cols_iff_isUnit]
      exact hli
    have hAP : A * P = P * Matrix.diagonal μ := by
      ext i j
      rw [Matrix.mul_diagonal]
      have := congrFun (hv j) i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, P, mul_comm] using this
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
    have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
    have hinvP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
    have hD : P⁻¹ * A * P = Matrix.diagonal μ := by
      rw [Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, hinvP, Matrix.one_mul]
    have hdiag : ∀ X : Matrix (Fin 3) (Fin 3) L, X * A = A * X →
        P⁻¹ * X * P = Matrix.diagonal (Matrix.diag (P⁻¹ * X * P)) := by
      intro X hX
      have hc : Commute (Matrix.diagonal μ) (P⁻¹ * X * P) := by
        rw [← hD]
        show P⁻¹ * A * P * (P⁻¹ * X * P) = P⁻¹ * X * P * (P⁻¹ * A * P)
        calc P⁻¹ * A * P * (P⁻¹ * X * P) = P⁻¹ * A * (P * P⁻¹) * X * P := by
              simp only [Matrix.mul_assoc]
          _ = P⁻¹ * (A * X) * P := by rw [hPinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = P⁻¹ * (X * A) * P := by rw [hX]
          _ = P⁻¹ * X * (P * P⁻¹) * A * P := by
              rw [hPinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = P⁻¹ * X * P * (P⁻¹ * A * P) := by simp only [Matrix.mul_assoc]
      exact (TauCeti.isDiag_of_commute_diagonal hμinj hc).diagonal_diag.symm
    intro X Y hX hY
    have hXY : (P⁻¹ * X * P) * (P⁻¹ * Y * P) = (P⁻¹ * Y * P) * (P⁻¹ * X * P) := by
      rw [hdiag X hX, hdiag Y hY]
      exact Matrix.commute_diagonal _ _
    have e1 : (P⁻¹ * X * P) * (P⁻¹ * Y * P) = P⁻¹ * (X * Y) * P := by
      calc (P⁻¹ * X * P) * (P⁻¹ * Y * P) = P⁻¹ * X * (P * P⁻¹) * Y * P := by
            simp only [Matrix.mul_assoc]
        _ = P⁻¹ * (X * Y) * P := by rw [hPinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have e2 : (P⁻¹ * Y * P) * (P⁻¹ * X * P) = P⁻¹ * (Y * X) * P := by
      calc (P⁻¹ * Y * P) * (P⁻¹ * X * P) = P⁻¹ * Y * (P * P⁻¹) * X * P := by
            simp only [Matrix.mul_assoc]
        _ = P⁻¹ * (Y * X) * P := by rw [hPinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e1, e2] at hXY
    have := congrArg (fun B => P * B * P⁻¹) hXY
    calc X * Y = (P * P⁻¹) * (X * Y) * (P * P⁻¹) := by rw [hPinv, Matrix.one_mul, Matrix.mul_one]
      _ = P * (P⁻¹ * (X * Y) * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * (P⁻¹ * (Y * X) * P) * P⁻¹ := this
      _ = (P * P⁻¹) * (Y * X) * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Y * X := by rw [hPinv, Matrix.one_mul, Matrix.mul_one]
  · left
    refine ⟨-(χ.coeff 1) / χ.coeff 2, ?_⟩
    have h4 : χ.coeff 2 • A = -(χ.coeff 1 • (1 : Matrix (Fin 3) (Fin 3) L)) :=
      eq_neg_of_add_eq_zero_right h2
    have h5 : A = (χ.coeff 2)⁻¹ • (χ.coeff 2 • A) := by
      rw [smul_smul, inv_mul_cancel₀ hc2, one_smul]
    rw [h5, h4, smul_neg, smul_smul, Matrix.scalar_apply, ← neg_smul, ← Matrix.smul_one_eq_diagonal]
    congr 1
    field_simp

end MatCube

section Torus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Pointwise


section Alg

variable {L : Type} [Field L]

private theorem triD4J_rootChar_longVec (c : Fin TwistTag.D4.tag.rank → Lˣ) (a b : ℤ) :
    rootChar c (d4LongVec a b) = (c 0 * c 1 * c 3) ^ a * c 2 ^ b := by
  rw [rootChar_d4_apply]
  change c 0 ^ a * c 1 ^ a * c 2 ^ b * c 3 ^ a = (c 0 * c 1 * c 3) ^ a * c 2 ^ b
  rw [mul_zpow, mul_zpow, mul_right_comm (c 0 ^ a * c 1 ^ a) (c 2 ^ b) (c 3 ^ a)]

private theorem triD4J_longA2_subset_kernel {c : Fin TwistTag.D4.tag.rank → Lˣ} (hc2 : c 2 = 1)
    (hc : c 0 * c 1 * c 3 = 1) : d4LongA2 ⊆ rootCharKernel c := by
  intro α hα
  refine ⟨d4LongA2_isRoot hα, ?_⟩
  have hα' := hα
  rw [d4LongA2_eq] at hα'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα'
  rcases hα' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rw [triD4J_rootChar_longVec, hc, hc2]; simp only [one_zpow, one_mul])

private theorem triD4J_comm_rootSpan {c : Fin TwistTag.D4.tag.rank → Lˣ} (hc2 : c 2 = 1)
    (hc : c 0 * c 1 * c 3 = 1) {w : ModGL TwistTag.D4.tag L}
    (hw : w ∈ rootSpan TwistTag.D4.tag L d4LongA2) :
    rootDiagUnit TwistTag.D4.tag c * w = w * rootDiagUnit TwistTag.D4.tag c :=
  (Subgroup.mem_centralizer_singleton_iff.1
    (rootSpan_le_centralizer c (triD4J_longA2_subset_kernel hc2 hc) hw)).symm

private theorem triD4J_diagramMap_comm {w : ModGL TwistTag.D4.tag L} (hw : w ∈ rootSpan TwistTag.D4.tag L d4LongA2) :
    diagramMap TwistTag.D4 L * w = w * diagramMap TwistTag.D4 L :=
  CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.diagramMap_comm_of_mem_rootSpan_fixed
    (fun β hβ => ⟨d4LongA2_isRoot hβ, by
      rw [d4LongA2_eq] at hβ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
      rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl <;> exact permLattice_d4LongVec _ _⟩) hw

private theorem triD4J_diagramMap_conj (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    diagramMap TwistTag.D4 L * rootDiagUnit TwistTag.D4.tag b * (diagramMap TwistTag.D4 L)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (fun i => b (TwistTag.D4.perm.symm i)) := by
  rw [diagramMap_mul_rootDiagUnit, mul_inv_cancel_right]

private theorem triD4J_diagramMap_inv_conj (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag b * diagramMap TwistTag.D4 L =
      rootDiagUnit TwistTag.D4.tag (fun i => b (TwistTag.D4.perm i)) := by
  have h := triD4J_diagramMap_conj (L := L) (fun i => b (TwistTag.D4.perm i))
  simp only [Equiv.apply_symm_apply] at h
  rw [← h]
  group

end Alg

section Split

variable {L : Type} [Field L]

private theorem triD4J_single_two_eq : (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 0 1 := by
  funext j; fin_cases j <;> rfl

private theorem triD4J_val1 {l a : Lˣ} : l ^ (2 : ℤ) * (l ^ 2 * a⁻¹) ^ (-1 : ℤ) = a := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, zpow_neg, zpow_one, zpow_two]
  have hl := l.ne_zero
  have ha := a.ne_zero
  field_simp

private theorem triD4J_val2 {l a s : Lˣ} (hl : l ^ 3 = a ^ 3 * s) :
    l ^ (-1 : ℤ) * (l ^ 2 * a⁻¹) ^ (2 : ℤ) = a * s := by
  apply Units.ext
  have hl' := congrArg Units.val hl
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hl'
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, zpow_neg, zpow_one, zpow_two]
  have h0 := l.ne_zero
  have ha := a.ne_zero
  field_simp
  linear_combination hl'

private theorem triD4J_torus_split [IsAlgClosed L] {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ torusGroup TwistTag.D4.tag L) :
    ∃ b c : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag b ∈ rootSpan TwistTag.D4.tag L d4LongA2 ∧
      c 2 = 1 ∧ c 0 * c 1 * c 3 = 1 ∧
      t = rootDiagUnit TwistTag.D4.tag b * rootDiagUnit TwistTag.D4.tag c := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨v₀, hv0, hv2⟩ := exists_smul_d4LongA2
  have himg := d4A2Sigma_image_longA2 hv0 hv2
  obtain ⟨l, hl⟩ : ∃ l : Lˣ, l ^ 3 = a 2 ^ 3 * (a 0 * a 1 * a 3) := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
      (((a 2 ^ 3 * (a 0 * a 1 * a 3) : Lˣ)) : L) (by norm_num : 0 < 3)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hz
      exact (Units.ne_zero _) hz.symm
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]
  set μ : Lˣ := l ^ 2 * (a 2)⁻¹ with hμ
  set b₀ : Fin TwistTag.D4.tag.rank → Lˣ :=
    (fun j => l ^ TwistTag.D4.tag.cartan 0 j) * (fun j => μ ^ TwistTag.D4.tag.cartan 2 j) with hb₀
  set b : Fin TwistTag.D4.tag.rank → Lˣ := weylTuple v₀ b₀ with hb
  have hmem : rootDiagUnit TwistTag.D4.tag b ∈ rootSpan TwistTag.D4.tag L d4LongA2 := by
    have hs0 : (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ d4A2Sigma := Or.inl rfl
    have hs0' : (-Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ d4A2Sigma := Or.inr (Or.inl rfl)
    have hs2 : (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ d4A2Sigma :=
      Or.inr (Or.inr (Or.inl rfl))
    have hs2' : (-Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ d4A2Sigma :=
      Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    have h1 : torusElt TwistTag.D4.tag L 0 l * torusElt TwistTag.D4.tag L 2 μ ∈
        rootSpan TwistTag.D4.tag L d4A2Sigma :=
      mul_mem (CFSG.RankThree.PartTwo.Sec21.Item219LieProof.torusElt_mem_rootSpan hs0 hs0' l)
        (CFSG.RankThree.PartTwo.Sec21.Item219LieProof.torusElt_mem_rootSpan hs2 hs2' μ)
    have h2 := CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.conj_mem_rootSpan_of_monomial_to
      (canonicalRep_mem_monomialSubgroup L v₀) (S := d4A2Sigma) (S' := d4LongA2)
      (fun γ hγ => ⟨isRoot_of_mem_d4A2Sigma hγ, by
        rw [weylQuotientHom_eq (mapsRootLines_canonicalRep v₀), ← himg]
        exact ⟨γ, hγ, rfl⟩⟩) h1
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul,
      canonicalRep_conj_rootDiagUnit] at h2
    exact h2
  have hinv0 : v₀⁻¹ • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = Pi.single 0 1 := by
    rw [inv_smul_eq_iff, hv0, triD4J_single_two_eq]
  have hinv2 : v₀⁻¹ • d4LongVec 1 1 = (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) := by
    rw [inv_smul_eq_iff, hv2]
  have hc00 : TwistTag.D4.tag.cartan 0 0 = 2 := by decide
  have hc20 : TwistTag.D4.tag.cartan 2 0 = -1 := by decide
  have hc02 : TwistTag.D4.tag.cartan 0 2 = -1 := by decide
  have hc22 : TwistTag.D4.tag.cartan 2 2 = 2 := by decide
  have hb2 : b 2 = a 2 := by
    have h := rootChar_weylTuple v₀ b₀ (Pi.single 2 1)
    rw [hinv0, rootChar_single, rootChar_single] at h
    rw [show b 2 = weylTuple v₀ b₀ 2 from rfl, h]
    simp only [hb₀, Pi.mul_apply, hc00, hc20, hμ]
    exact triD4J_val1
  have hsum : (b 0 * b 1 * b 3) * b 2 = (a 0 * a 1 * a 3) * a 2 := by
    have h := rootChar_weylTuple v₀ b₀ (d4LongVec 1 1)
    rw [hinv2, rootChar_single, triD4J_rootChar_longVec] at h
    rw [zpow_one, zpow_one] at h
    rw [show b 0 * b 1 * b 3 * b 2 = weylTuple v₀ b₀ 0 * weylTuple v₀ b₀ 1 * weylTuple v₀ b₀ 3 *
      weylTuple v₀ b₀ 2 from rfl, h]
    simp only [hb₀, Pi.mul_apply, hc02, hc22, hμ]
    rw [triD4J_val2 hl, mul_comm]
  have hprod : b 0 * b 1 * b 3 = a 0 * a 1 * a 3 := by
    rw [hb2] at hsum
    exact mul_right_cancel hsum
  refine ⟨b, b⁻¹ * a, hmem, ?_, ?_, ?_⟩
  · simp only [Pi.mul_apply, Pi.inv_apply, hb2, inv_mul_cancel]
  · simp only [Pi.mul_apply, Pi.inv_apply]
    calc (b 0)⁻¹ * a 0 * ((b 1)⁻¹ * a 1) * ((b 3)⁻¹ * a 3) =
        (b 0 * b 1 * b 3)⁻¹ * (a 0 * a 1 * a 3) := by
          simp only [mul_inv, mul_assoc, mul_comm, mul_left_comm]
      _ = 1 := by rw [hprod, inv_mul_cancel]
  · rw [← rootDiagUnit_mul, mul_inv_cancel_left]

end Split

section Key

variable {L : Type} [Field L]

private theorem triD4J_cube {G : Type*} [Group G] (z M p : G) (hzM : z * M = M * z) (hpM : p * M = M * p) :
    (z * M * p) ^ 3 = M ^ 3 * (z * (p * z * p⁻¹) * (p * (p * z * p⁻¹) * p⁻¹)) * p ^ 3 := by
  have hc : Commute M (z * p) := by
    show M * (z * p) = z * p * M
    rw [← mul_assoc, ← hzM, mul_assoc, mul_assoc, hpM]
  have e1 : z * M * p = M * (z * p) := by rw [hzM, mul_assoc]
  rw [e1, hc.mul_pow, mul_assoc]
  congr 1
  simp only [pow_succ, pow_zero, one_mul]
  group

private theorem triD4J_tuple_norm {c : Fin TwistTag.D4.tag.rank → Lˣ} (hc2 : c 2 = 1)
    (hc : c 0 * c 1 * c 3 = 1) {π : Equiv.Perm (Fin TwistTag.D4.tag.rank)}
    (hπ : π = TwistTag.D4.perm ∨ π = TwistTag.D4.perm.symm) :
    c (π 2) = 1 ∧ c (π 0) * c (π 1) * c (π 3) = 1 ∧
      c * (fun i => c (π i)) * (fun i => c (π (π i))) = 1 := by
  rcases hπ with rfl | rfl
  · have e0 : TwistTag.D4.perm 0 = 1 := by decide
    have e1 : TwistTag.D4.perm 1 = 3 := by decide
    have e2 : TwistTag.D4.perm 2 = 2 := by decide
    have e3 : TwistTag.D4.perm 3 = 0 := by decide
    refine ⟨by rw [e2, hc2], by rw [e0, e1, e3]; simpa only [mul_comm, mul_left_comm, mul_assoc] using hc, ?_⟩
    funext i
    fin_cases i
    · show c 0 * c (TwistTag.D4.perm 0) * c (TwistTag.D4.perm (TwistTag.D4.perm 0)) = 1
      rw [e0, e1]; simpa only [mul_comm, mul_left_comm, mul_assoc] using hc
    · show c 1 * c (TwistTag.D4.perm 1) * c (TwistTag.D4.perm (TwistTag.D4.perm 1)) = 1
      rw [e1, e3]; simpa only [mul_comm, mul_left_comm, mul_assoc] using hc
    · show c 2 * c (TwistTag.D4.perm 2) * c (TwistTag.D4.perm (TwistTag.D4.perm 2)) = 1
      rw [e2, e2, hc2, one_mul, one_mul]
    · show c 3 * c (TwistTag.D4.perm 3) * c (TwistTag.D4.perm (TwistTag.D4.perm 3)) = 1
      rw [e3, e0]; simpa only [mul_comm, mul_left_comm, mul_assoc] using hc
  · have e0 : TwistTag.D4.perm.symm 0 = 3 := by decide
    have e1 : TwistTag.D4.perm.symm 1 = 0 := by decide
    have e2 : TwistTag.D4.perm.symm 2 = 2 := by decide
    have e3 : TwistTag.D4.perm.symm 3 = 1 := by decide
    refine ⟨by rw [e2, hc2], by rw [e0, e1, e3]; simpa only [mul_comm, mul_left_comm, mul_assoc] using hc, ?_⟩
    funext i
    fin_cases i
    · show c 0 * c (TwistTag.D4.perm.symm 0) *
        c (TwistTag.D4.perm.symm (TwistTag.D4.perm.symm 0)) = 1
      rw [e0, e3]; simpa only [mul_comm, mul_left_comm, mul_assoc] using hc
    · show c 1 * c (TwistTag.D4.perm.symm 1) *
        c (TwistTag.D4.perm.symm (TwistTag.D4.perm.symm 1)) = 1
      rw [e1, e0]; simpa only [mul_comm, mul_left_comm, mul_assoc] using hc
    · show c 2 * c (TwistTag.D4.perm.symm 2) *
        c (TwistTag.D4.perm.symm (TwistTag.D4.perm.symm 2)) = 1
      rw [e2, e2, hc2, one_mul, one_mul]
    · show c 3 * c (TwistTag.D4.perm.symm 3) *
        c (TwistTag.D4.perm.symm (TwistTag.D4.perm.symm 3)) = 1
      rw [e3, e1]; simpa only [mul_comm, mul_left_comm, mul_assoc] using hc

private theorem triD4J_diagramPow_conj {p : ModGL TwistTag.D4.tag L}
    (hp : p = diagramMap TwistTag.D4 L ∨ p = (diagramMap TwistTag.D4 L)⁻¹) :
    ∃ π : Equiv.Perm (Fin TwistTag.D4.tag.rank),
      (π = TwistTag.D4.perm ∨ π = TwistTag.D4.perm.symm) ∧
      ∀ c : Fin TwistTag.D4.tag.rank → Lˣ,
        p * rootDiagUnit TwistTag.D4.tag c * p⁻¹ = rootDiagUnit TwistTag.D4.tag (fun i => c (π i)) := by
  rcases hp with rfl | rfl
  · exact ⟨TwistTag.D4.perm.symm, Or.inr rfl, fun c => triD4J_diagramMap_conj c⟩
  · refine ⟨TwistTag.D4.perm, Or.inl rfl, fun c => ?_⟩
    rw [inv_inv]
    exact triD4J_diagramMap_inv_conj c

private theorem triD4J_alg [IsAlgClosed L] [CharP L 2] {B : Lˣ} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1)
    {p : ModGL TwistTag.D4.tag L}
    (hp : p = diagramMap TwistTag.D4 L ∨ p = (diagramMap TwistTag.D4 L)⁻¹)
    {m : ModGL TwistTag.D4.tag L} (hmG : m ∈ adjointGroup TwistTag.D4.tag L)
    (hmd : m * rootDiagUnit TwistTag.D4.tag ![B, B, 1, B] =
      rootDiagUnit TwistTag.D4.tag ![B, B, 1, B] * m)
    (h3 : (m * p) ^ 3 = 1) :
    ∃ M ∈ rootSpan TwistTag.D4.tag L d4LongA2, M ^ 3 = 1 ∧
      ∀ w ∈ rootSpan TwistTag.D4.tag L d4LongA2, (m * p) * w * (m * p)⁻¹ = M * w * M⁻¹ := by
  obtain ⟨v₀, hv0, hv2⟩ := exists_smul_d4LongA2
  have himg := d4A2Sigma_image_longA2 hv0 hv2
  set aB : Fin TwistTag.D4.tag.rank → Lˣ := ![B, B, 1, B] with haB
  set v₁ : WeylGroup Tag.D4 := v₀ with hv₁
  have himg' : (fun α : Fin Tag.D4.rank → ℤ => v₁ • α) '' d4A2Sigma = d4LongA2 := himg
  have hSig : rootCharKernel aB = (fun α : Fin Tag.D4.rank → ℤ => v₁ • α) '' d4A2Sigma := by
    rw [himg']
    ext α
    exact d4Minus_rootCharKernel hB3 hB1 α
  have hord : orderOf (rootDiagUnit TwistTag.D4.tag aB) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · have e : aB * aB * aB = 1 := by
        funext i
        simp only [Pi.mul_apply, Pi.one_apply, ← pow_three']
        fin_cases i
        · exact hB3
        · exact hB3
        · exact one_pow 3
        · exact hB3
      rw [pow_three, ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← mul_assoc, e, rootDiagUnit_one]
    · intro h
      apply hB1
      have h1 := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
        (h.trans rootDiagUnit_one.symm)
      exact congrFun h1 0
  have hpK : ringChar L ≠ 3 := by
    rw [ringChar.eq L 2]
    norm_num
  obtain ⟨-, hX, -, -, -, -, -, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer L 3 Nat.prime_three (by norm_num) hpK aB hord v₁ hSig
  have hQ : d4A2Qv L v₁ = rootSpan TwistTag.D4.tag L d4LongA2 := by
    rw [d4A2Qv_eq_rootSpan, himg']
    rfl
  have hmX : m ∈ toralCentralizer Tag.D4 L aB :=
    ⟨hmG, Subgroup.mem_centralizer_singleton_iff.2 hmd⟩
  have hm' : m ∈ (↑(torusGroup Tag.D4 L) : Set (ModGL Tag.D4 L)) *
      (↑(d4A2Qv L v₁) : Set (ModGL Tag.D4 L)) := by
    rw [← hX]
    exact hmX
  obtain ⟨t, ht, q, hq, htq⟩ := Set.mem_mul.1 hm'
  have hq' : q ∈ rootSpan TwistTag.D4.tag L d4LongA2 := by
    rw [← hQ]
    exact hq
  have ht' : t ∈ torusGroup TwistTag.D4.tag L := ht
  obtain ⟨b, c, hbQ, hc2, hc, htbc⟩ := triD4J_torus_split ht'
  set z := rootDiagUnit TwistTag.D4.tag c with hz
  set M := rootDiagUnit TwistTag.D4.tag b * q with hM
  have hMQ : M ∈ rootSpan TwistTag.D4.tag L d4LongA2 := mul_mem hbQ hq'
  have hzQ : ∀ w ∈ rootSpan TwistTag.D4.tag L d4LongA2, z * w = w * z :=
    fun w hw => triD4J_comm_rootSpan hc2 hc hw
  have hpQ : ∀ w ∈ rootSpan TwistTag.D4.tag L d4LongA2, p * w = w * p := by
    rcases hp with rfl | rfl
    · exact fun w hw => triD4J_diagramMap_comm hw
    · intro w hw
      have h := triD4J_diagramMap_comm hw
      calc (diagramMap TwistTag.D4 L)⁻¹ * w =
          (diagramMap TwistTag.D4 L)⁻¹ * (w * diagramMap TwistTag.D4 L) *
            (diagramMap TwistTag.D4 L)⁻¹ := by group
        _ = (diagramMap TwistTag.D4 L)⁻¹ * (diagramMap TwistTag.D4 L * w) *
            (diagramMap TwistTag.D4 L)⁻¹ := by rw [h]
        _ = w * (diagramMap TwistTag.D4 L)⁻¹ := by group
  have hm : m = z * M := by
    calc m = t * q := htq.symm
      _ = rootDiagUnit TwistTag.D4.tag b * rootDiagUnit TwistTag.D4.tag c * q := by rw [htbc]
      _ = z * M := by
        rw [hM, hz, ← mul_assoc, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm b c]
  have hp3 : p ^ 3 = 1 := by
    rcases hp with rfl | rfl
    · exact CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.diagramMap_d4_pow_three
    · rw [inv_pow, CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.diagramMap_d4_pow_three, inv_one]
  obtain ⟨π, hπ, hconj⟩ := triD4J_diagramPow_conj (L := L) hp
  obtain ⟨-, -, hN⟩ := triD4J_tuple_norm hc2 hc hπ
  have hNz : z * (p * z * p⁻¹) * (p * (p * z * p⁻¹) * p⁻¹) = 1 := by
    rw [hz, hconj, hconj, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    convert rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L) using 2
  refine ⟨M, hMQ, ?_, ?_⟩
  · have h := triD4J_cube z M p (hzQ M hMQ) (hpQ M hMQ)
    rw [← hm, hNz, mul_one, hp3, mul_one] at h
    rw [← h]
    exact h3
  · intro w hw
    rw [hm]
    have hMw : M * w * M⁻¹ ∈ rootSpan TwistTag.D4.tag L d4LongA2 :=
      mul_mem (mul_mem hMQ hw) (inv_mem hMQ)
    have h1 : p * w * p⁻¹ = w := by rw [hpQ w hw, mul_inv_cancel_right]
    calc z * M * p * w * (z * M * p)⁻¹ = z * (M * (p * w * p⁻¹) * M⁻¹) * z⁻¹ := by group
      _ = z * (M * w * M⁻¹) * z⁻¹ := by rw [h1]
      _ = M * w * M⁻¹ := by rw [hzQ _ hMw, mul_inv_cancel_right]

end Key

end Torus

section Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.RankThree.PartOne.KGD
open scoped Pointwise MatrixGroups


section Kernel

variable {L : Type} [Field L]

open CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof in
private theorem triD4J_kernel_gA {ζ : Lˣ} (hζ : orderOf ζ = 3) :
    rootCharKernel (tup ζ gA) = d4A2Sigma := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  ext γ
  constructor
  · intro hγ
    obtain ⟨i, j, hij, rfl⟩ := rootCharKernel_tup_gA_subset hζ hγ
    rcases chainRootA2_cases i j hij with h | h | h | h | h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · intro hγ
    refine ⟨isRoot_of_mem_d4A2Sigma hγ, ?_⟩
    rw [rootChar_tup hζ3]
    have h0 : (∑ i, ((γ i : ℤ) : ZMod 3) * gA i) = 0 := by
      rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h0, ZMod.val_zero, pow_zero]

private theorem triD4J_kernel_weylTuple (w : WeylGroup TwistTag.D4.tag) (a : Fin TwistTag.D4.tag.rank → Lˣ)
    (α : Fin TwistTag.D4.tag.rank → ℤ) :
    α ∈ rootCharKernel (weylTuple w a) ↔ w⁻¹ • α ∈ rootCharKernel a := by
  constructor
  · rintro ⟨hα, h1⟩
    exact ⟨IsRoot.smul hα _, by rwa [rootChar_weylTuple] at h1⟩
  · rintro ⟨hα, h1⟩
    refine ⟨?_, by rwa [rootChar_weylTuple]⟩
    have := IsRoot.smul hα w
    rwa [smul_inv_smul] at this

open CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof in
private theorem triD4J_dA_conj_dB {ζ : Lˣ} (hζ : orderOf ζ = 3) :
    ∃ (n : ModGL TwistTag.D4.tag L) (B : Lˣ), n ∈ adjointGroup TwistTag.D4.tag L ∧ B ^ 3 = 1 ∧
      B ≠ 1 ∧ n * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * n⁻¹ =
        rootDiagUnit TwistTag.D4.tag ![B, B, 1, B] := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  obtain ⟨v₀, hv0, hv2⟩ := exists_smul_d4LongA2
  have himg := d4A2Sigma_image_longA2 hv0 hv2
  have hker : ∀ α, α ∈ rootCharKernel (weylTuple v₀ (tup ζ gA)) ↔ α ∈ d4LongA2 := by
    intro α
    rw [triD4J_kernel_weylTuple, triD4J_kernel_gA hζ, ← himg]
    constructor
    · intro h
      exact ⟨_, h, smul_inv_smul v₀ α⟩
    · rintro ⟨β, hβ, rfl⟩
      rwa [inv_smul_smul]
  have h3 : ∀ i, weylTuple v₀ (tup ζ gA) i ^ 3 = 1 := by
    intro i
    show rootChar (tup ζ gA) (v₀⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) ^ 3 = 1
    rw [rootChar_tup hζ3, ← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
  obtain ⟨B, hB3, hB1, hB⟩ := d4_tuple_of_kernel_longA2 h3 hker
  refine ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) L v₀, B,
    canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.D4.tag) L v₀, hB3, hB1, ?_⟩
  rw [canonicalRep_conj_rootDiagUnit, hB]

end Kernel

section Model

open CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof in
private theorem triD4J_cent_data {L : Type} [Field L] [CharP L 2] {B : Lˣ} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) :
    ⁅toralCentralizer Tag.D4 L ![B, B, 1, B], toralCentralizer Tag.D4 L ![B, B, 1, B]⁆ ≤
        rootSpan Tag.D4 L d4LongA2 ∧
      Nonempty (rootSpan Tag.D4 L d4LongA2 ≃* SL(3, L)) := by
  obtain ⟨v₀, hv0, hv2⟩ := exists_smul_d4LongA2
  set v₁ : WeylGroup Tag.D4 := v₀ with hv₁
  have himg' : (fun α : Fin Tag.D4.rank → ℤ => v₁ • α) '' d4A2Sigma = d4LongA2 :=
    d4A2Sigma_image_longA2 hv0 hv2
  set aB : Fin TwistTag.D4.tag.rank → Lˣ := ![B, B, 1, B] with haB
  have hSig : rootCharKernel aB = (fun α : Fin Tag.D4.rank → ℤ => v₁ • α) '' d4A2Sigma := by
    rw [himg']
    ext α
    exact d4Minus_rootCharKernel hB3 hB1 α
  have hord : orderOf (rootDiagUnit TwistTag.D4.tag aB) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · have e : aB * aB * aB = 1 := by
        funext i
        simp only [Pi.mul_apply, Pi.one_apply, ← pow_three']
        fin_cases i
        · exact hB3
        · exact hB3
        · exact one_pow 3
        · exact hB3
      rw [pow_three, ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← mul_assoc, e, rootDiagUnit_one]
    · intro h
      apply hB1
      have h1 := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
        (h.trans rootDiagUnit_one.symm)
      exact congrFun h1 0
  have hpK : ringChar L ≠ 3 := by
    rw [ringChar.eq L 2]
    norm_num
  obtain ⟨-, -, -, -, ⟨ψ⟩, -, hder, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer L 3 Nat.prime_three (by norm_num) hpK aB hord v₁ hSig
  have hQ : d4A2Qv L v₁ = rootSpan Tag.D4 L d4LongA2 := by
    rw [d4A2Qv_eq_rootSpan, himg']
  refine ⟨?_, ⟨(MulEquiv.subgroupCongr hQ.symm).trans ψ⟩⟩
  rw [hder, hQ]

end Model

section Core

variable {n : ℕ} {K₃ : Type} [Field K₃] [Finite K₃] {Fr : K₃ ≃+* K₃}

private theorem triD4J_fieldActor_eq (c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :
    ((fieldActor Fr Fr c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :
      ModGL TwistTag.D4.tag K₃) =
      (diagramMap TwistTag.D4 K₃)⁻¹ * c * diagramMap TwistTag.D4 K₃ := by
  have hF : twistHom TwistTag.D4 K₃ Fr.toRingHom (c : ModGL TwistTag.D4.tag K₃) = c :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ c.2)).2
  rw [coe_fieldActor]
  have e : twistHom TwistTag.D4 K₃ Fr.toRingHom (c : ModGL TwistTag.D4.tag K₃) =
      diagramMap TwistTag.D4 K₃ * Units.map (entrywiseHom Fr.toRingHom) c *
        (diagramMap TwistTag.D4 K₃)⁻¹ := rfl
  rw [e] at hF
  calc (Units.map (entrywiseHom Fr.toRingHom)) (c : ModGL TwistTag.D4.tag K₃) =
      (diagramMap TwistTag.D4 K₃)⁻¹ * (diagramMap TwistTag.D4 K₃ *
        (Units.map (entrywiseHom Fr.toRingHom)) (c : ModGL TwistTag.D4.tag K₃) *
          (diagramMap TwistTag.D4 K₃)⁻¹) * diagramMap TwistTag.D4 K₃ := by group
    _ = (diagramMap TwistTag.D4 K₃)⁻¹ * c * diagramMap TwistTag.D4 K₃ := by rw [hF]

private theorem triD4J_fieldActor_inv_eq (c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :
    (((fieldActor Fr Fr)⁻¹ c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :
      ModGL TwistTag.D4.tag K₃) =
      diagramMap TwistTag.D4 K₃ * c * (diagramMap TwistTag.D4 K₃)⁻¹ := by
  set c' := (fieldActor Fr Fr)⁻¹ c with hc'
  have h : fieldActor Fr Fr c' = c := by
    rw [hc', MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have h2 := triD4J_fieldActor_eq c'
  rw [h] at h2
  rw [h2]
  group

private theorem triD4J_conj_form {y : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom}
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)}
    (hα : α = MulAut.conj y * fieldActor Fr Fr ∨ α = MulAut.conj y * (fieldActor Fr Fr)⁻¹) :
    ∃ pK : ModGL TwistTag.D4.tag K₃,
      (pK = (diagramMap TwistTag.D4 K₃)⁻¹ ∨ pK = diagramMap TwistTag.D4 K₃) ∧
      ∀ c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom,
        ((α c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) : ModGL TwistTag.D4.tag K₃) =
          ((y : ModGL TwistTag.D4.tag K₃) * pK) * c * ((y : ModGL TwistTag.D4.tag K₃) * pK)⁻¹ := by
  rcases hα with rfl | rfl
  · refine ⟨(diagramMap TwistTag.D4 K₃)⁻¹, Or.inl rfl, fun c => ?_⟩
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, triD4J_fieldActor_eq]
    group
  · refine ⟨diagramMap TwistTag.D4 K₃, Or.inr rfl, fun c => ?_⟩
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, triD4J_fieldActor_inv_eq]
    group

end Core

section ModelCore

variable {K₃ : Type} [Field K₃] [Finite K₃] {Fr : K₃ ≃+* K₃}

private theorem triD4J_diagramPow_conj_mem {L : Type} [Field L] {p : ModGL TwistTag.D4.tag L}
    (hp : p = diagramMap TwistTag.D4 L ∨ p = (diagramMap TwistTag.D4 L)⁻¹)
    {g : ModGL TwistTag.D4.tag L} (hg : g ∈ adjointGroup TwistTag.D4.tag L) :
    p * g * p⁻¹ ∈ adjointGroup TwistTag.D4.tag L := by
  rcases hp with rfl | rfl
  · exact diagramMap_conj_mem_adjointGroup hg
  · have h3 := CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.diagramMap_d4_pow_three (L := L)
    set P := diagramMap TwistTag.D4 L with hP
    have hinv : P⁻¹ = P * P := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_three']
      exact h3
    have hPP : P⁻¹ * P⁻¹ = P := by
      rw [← mul_inv_rev, ← hinv, inv_inv]
    have e : P⁻¹ * g * P⁻¹⁻¹ = P * (P * g * P⁻¹) * P⁻¹ := by
      calc P⁻¹ * g * P⁻¹⁻¹ = P * P * g * P := by rw [inv_inv, hinv]
        _ = P * P * g * (P⁻¹ * P⁻¹) := by rw [hPP]
        _ = P * (P * g * P⁻¹) * P⁻¹ := by group
    rw [e]
    exact diagramMap_conj_mem_adjointGroup (diagramMap_conj_mem_adjointGroup hg)

open CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof in
private theorem triD4J_model_core {L : Type} [Field L] [Algebra K₃ L] [IsAlgClosed L] [CharP L 2]
    {x : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom}
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)} (hαx : α x = x)
    {y : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom} {pK : ModGL TwistTag.D4.tag K₃}
    (hpK : pK = (diagramMap TwistTag.D4 K₃)⁻¹ ∨ pK = diagramMap TwistTag.D4 K₃)
    (hconj : ∀ c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom,
      ((α c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) : ModGL TwistTag.D4.tag K₃) =
        ((y : ModGL TwistTag.D4.tag K₃) * pK) * c * ((y : ModGL TwistTag.D4.tag K₃) * pK)⁻¹)
    (h3 : ((y : ModGL TwistTag.D4.tag K₃) * pK) ^ 3 = 1)
    {B : Lˣ} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) {k : ModGL TwistTag.D4.tag L}
    (hkG : k ∈ adjointGroup TwistTag.D4.tag L)
    (hxk : triEmb K₃ Fr L x = k * rootDiagUnit TwistTag.D4.tag ![B, B, 1, B] * k⁻¹) :
    (∀ d ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))⁆,
        α d = d) ∨
      (∀ d₁ ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
          Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))⁆,
        ∀ d₂ ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
          Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))⁆,
          α d₁ = d₁ → α d₂ = d₂ → d₁ * d₂ = d₂ * d₁) := by
  classical
  set bc := baseChangeGL (τ := TwistTag.D4.tag) (algebraMap K₃ L) with hbc
  set ι := triEmb K₃ Fr L with hι
  have hιbc : ∀ c, ι c = bc (c : ModGL TwistTag.D4.tag K₃) := fun c => rfl
  set dB := rootDiagUnit TwistTag.D4.tag (![B, B, 1, B] : Fin TwistTag.D4.tag.rank → Lˣ) with hdB
  set hK := (y : ModGL TwistTag.D4.tag K₃) * pK with hhK
  set pL := bc pK with hpL
  have hpL' : pL = diagramMap TwistTag.D4 L ∨ pL = (diagramMap TwistTag.D4 L)⁻¹ := by
    rcases hpK with h | h
    · right
      rw [hpL, h, map_inv, baseChangeGL_diagramMap]
    · left
      rw [hpL, h, baseChangeGL_diagramMap]
  set ht := bc hK with hht
  have hια : ∀ c, ι (α c) = ht * ι c * ht⁻¹ := by
    intro c
    rw [hιbc, hιbc, hconj, map_mul, map_mul, map_inv]
  have ht3 : ht ^ 3 = 1 := by rw [hht, ← map_pow, h3, map_one]
  have hht' : ht = ι y * pL := by rw [hht, hhK, map_mul]; rfl
  set m := k⁻¹ * ι y * (pL * k * pL⁻¹) with hm
  have hmG : m ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem (inv_mem hkG) (triEmb_mem_adjointGroup y)) (triD4J_diagramPow_conj_mem hpL' hkG)
  have hh₁ : k⁻¹ * ht * k = m * pL := by rw [hht', hm]; group
  have hdBι : dB = k⁻¹ * ι x * k := by rw [hxk]; group
  have hpd : pL * dB * pL⁻¹ = dB := by
    obtain ⟨π, hπ, hc⟩ := triD4J_diagramPow_conj (L := L) hpL'
    rw [hdB]
    refine (hc _).trans ?_
    congr 1
    funext i
    rcases hπ with rfl | rfl
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
  have hmd : m * dB = dB * m := by
    have h1 : (m * pL) * dB * (m * pL)⁻¹ = dB := by
      rw [← hh₁, hdBι]
      have : ht * ι x * ht⁻¹ = ι x := by rw [← hια, hαx]
      calc k⁻¹ * ht * k * (k⁻¹ * ι x * k) * (k⁻¹ * ht * k)⁻¹ = k⁻¹ * (ht * ι x * ht⁻¹) * k := by
            group
        _ = k⁻¹ * ι x * k := by rw [this]
    have h2 : m * (pL * dB * pL⁻¹) * m⁻¹ = (m * pL) * dB * (m * pL)⁻¹ := by group
    rw [hpd, h1] at h2
    calc m * dB = m * dB * m⁻¹ * m := by group
      _ = dB * m := by rw [h2]
  have hh₁3 : (m * pL) ^ 3 = 1 := by
    have e := conj_pow (a := k⁻¹) (b := ht) (i := 3)
    rw [inv_inv] at e
    rw [← hh₁, e, ht3, mul_one, inv_mul_cancel]
  obtain ⟨M, hMQ, hM3, hMconj⟩ := triD4J_alg hB3 hB1 hpL' hmG hmd hh₁3
  obtain ⟨hder, ⟨ψQ⟩⟩ := triD4J_cent_data (L := L) hB3 hB1
  set φk : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj k⁻¹).toMonoidHom.comp ι with hφk
  have hφk' : ∀ d, φk d = k⁻¹ * ι d * k := fun d => by
    show (MulAut.conj k⁻¹) (ι d) = _
    rw [MulAut.conj_apply, inv_inv]
  have hφkinj : Function.Injective φk := by
    intro a b h
    rw [hφk', hφk'] at h
    exact triEmb_injective (K := K₃) (σ := Fr) (L := L) (mul_left_cancel (mul_right_cancel h))
  have hφkX : (Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))).map
      φk ≤ toralCentralizer Tag.D4 L ![B, B, 1, B] := by
    rintro _ ⟨d, hd₀, rfl⟩
    have hd : d * x = x * d := Subgroup.mem_centralizer_singleton_iff.1 hd₀
    have hG : φk d ∈ adjointGroup TwistTag.D4.tag L := by
      rw [hφk']
      exact mul_mem (mul_mem (inv_mem hkG) (triEmb_mem_adjointGroup d)) hkG
    have hC : φk d * dB = dB * φk d := by
      rw [hφk', hdBι]
      calc k⁻¹ * ι d * k * (k⁻¹ * ι x * k) = k⁻¹ * ι (d * x) * k := by rw [map_mul]; group
        _ = k⁻¹ * ι (x * d) * k := by rw [hd]
        _ = k⁻¹ * ι x * k * (k⁻¹ * ι d * k) := by rw [map_mul]; group
    exact Subgroup.mem_inf.2 ⟨hG, Subgroup.mem_centralizer_singleton_iff.2 hC⟩
  have hφkQ : ∀ d ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
      Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))⁆,
      φk d ∈ rootSpan Tag.D4 L d4LongA2 := by
    intro d hd
    have h1 : φk d ∈ (⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))⁆).map φk :=
      Subgroup.mem_map_of_mem φk hd
    rw [Subgroup.map_commutator] at h1
    exact hder (Subgroup.commutator_mono hφkX hφkX h1)
  have hφkα : ∀ d ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
      Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))⁆,
      φk (α d) = M * φk d * M⁻¹ := by
    intro d hd
    have h1 : φk (α d) = (m * pL) * φk d * (m * pL)⁻¹ := by
      rw [hφk', hφk', hια, ← hh₁]
      group
    rw [h1]
    exact hMconj _ (hφkQ d hd)
  have hM3' : (ψQ ⟨M, hMQ⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨M, hMQ⟩ : rootSpan Tag.D4 L d4LongA2) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hM3)
    rw [this, map_one]
  have h3L : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (3 : L) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  have hdet : ((ψQ ⟨M, hMQ⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L).det = 1 :=
    (ψQ ⟨M, hMQ⟩).2
  have hpow : ((ψQ ⟨M, hMQ⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hM3', Matrix.SpecialLinearGroup.coe_one]
  have hsl : ∀ {w : ModGL TwistTag.D4.tag L} (hw : w ∈ rootSpan Tag.D4 L d4LongA2),
      w * M = M * w ↔
        ((ψQ ⟨w, hw⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) *
            ((ψQ ⟨M, hMQ⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
          ((ψQ ⟨M, hMQ⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) *
            ((ψQ ⟨w, hw⟩ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) := by
    intro w hw
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
      ← map_mul]
    constructor
    · intro hwM
      have e : (⟨w, hw⟩ : rootSpan Tag.D4 L d4LongA2) * ⟨M, hMQ⟩ = ⟨M, hMQ⟩ * ⟨w, hw⟩ :=
        Subtype.ext hwM
      rw [e]
    · intro h
      have e := congrArg Subtype.val (ψQ.injective (Subtype.ext h))
      exact e
  rcases triD4J_mat_cube h3L _ hpow hdet with ⟨c, hc⟩ | hab
  ·
    left
    intro d hd
    apply hφkinj
    rw [hφkα d hd]
    have hw := hφkQ d hd
    have hcomm : φk d * M = M * φk d := by
      rw [hsl hw, hc]
      exact (Matrix.scalar_commute c (fun r => Commute.all c r) _).symm
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm.symm
  ·
    right
    intro d₁ hd₁ d₂ hd₂ h₁ h₂
    apply hφkinj
    have hw₁ := hφkQ d₁ hd₁
    have hw₂ := hφkQ d₂ hd₂
    have hc₁ : φk d₁ * M = M * φk d₁ := by
      have := hφkα d₁ hd₁
      rw [h₁] at this
      have h' : M * φk d₁ * M⁻¹ = φk d₁ := this.symm
      rw [mul_inv_eq_iff_eq_mul] at h'
      exact h'.symm
    have hc₂ : φk d₂ * M = M * φk d₂ := by
      have := hφkα d₂ hd₂
      rw [h₂] at this
      have h' : M * φk d₂ * M⁻¹ = φk d₂ := this.symm
      rw [mul_inv_eq_iff_eq_mul] at h'
      exact h'.symm
    have h12 := hab _ _ ((hsl hw₁).1 hc₁) ((hsl hw₂).1 hc₂)
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
      ← map_mul] at h12
    have h12' := congrArg Subtype.val (ψQ.injective (Subtype.ext h12))
    rw [map_mul, map_mul]
    exact h12'

end ModelCore

section Model2

variable {K₃ : Type} [Field K₃] [Finite K₃] {Fr : K₃ ≃+* K₃}

private theorem triD4J_h3 (hZ0 : Subgroup.center (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) = ⊥)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)} (hα3 : α ^ 3 = 1)
    {y : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom} {pK : ModGL TwistTag.D4.tag K₃}
    (hpK : pK = (diagramMap TwistTag.D4 K₃)⁻¹ ∨ pK = diagramMap TwistTag.D4 K₃)
    (hconj : ∀ c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom,
      ((α c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) : ModGL TwistTag.D4.tag K₃) =
        ((y : ModGL TwistTag.D4.tag K₃) * pK) * c * ((y : ModGL TwistTag.D4.tag K₃) * pK)⁻¹) :
    ((y : ModGL TwistTag.D4.tag K₃) * pK) ^ 3 = 1 := by
  set h := (y : ModGL TwistTag.D4.tag K₃) * pK with hh
  have hp3 : pK ^ 3 = 1 := by
    rcases hpK with rfl | rfl
    · rw [inv_pow, CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.diagramMap_d4_pow_three, inv_one]
    · exact CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.diagramMap_d4_pow_three
  have hP : ∀ c : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom,
      pK * (c : ModGL TwistTag.D4.tag K₃) * pK⁻¹ =
        ((y⁻¹ * α c * y : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :
          ModGL TwistTag.D4.tag K₃) := by
    intro c
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hconj, hh]
    group
  set y₁ := y⁻¹ * α y * y with hy₁
  set y₂ := y⁻¹ * α y₁ * y with hy₂
  have hN : h ^ 3 = ((y * y₁ * y₂ : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :
      ModGL TwistTag.D4.tag K₃) := by
    have e1 : h ^ 3 = (y : ModGL TwistTag.D4.tag K₃) * (pK * y * pK⁻¹) *
        (pK * (pK * y * pK⁻¹) * pK⁻¹) * pK ^ 3 := by
      rw [hh]
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e1, hP y, hP y₁, hp3, mul_one]
    rfl
  have hcen : y * y₁ * y₂ ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := by
    rw [Subgroup.mem_center_iff]
    intro c
    have h1 : α (α (α c)) = c := by
      have := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) => φ c) hα3
      simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at this
      exact this
    have h2 : ((α (α (α c)) : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :
        ModGL TwistTag.D4.tag K₃) = h ^ 3 * c * (h ^ 3)⁻¹ := by
      rw [hconj, hconj, hconj]
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [h1, hN] at h2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    calc (c : ModGL TwistTag.D4.tag K₃) * ↑(y * y₁ * y₂) =
        ↑(y * y₁ * y₂) * c * (↑(y * y₁ * y₂))⁻¹ * ↑(y * y₁ * y₂) := by rw [← h2]
      _ = ↑(y * y₁ * y₂) * c := by group
  rw [hZ0, Subgroup.mem_bot] at hcen
  rw [hN, hcen, Subgroup.coe_one]

open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof in
private theorem triD4J_model {n : ℕ} (hn1 : 1 ≤ n) (hK : Nat.card K₃ = (2 ^ n) ^ 3)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hZ0 : Subgroup.center (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) = ⊥)
    {x : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {g₀ : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom}
    (hg₀ : g₀ * x * g₀⁻¹ ∈ KS11Lie4Proof.d4ShortSL2 K₃ Fr.toRingHom)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut α) (hαx : α x = x) :
    (∀ d ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))⁆,
        α d = d) ∨
      (∀ d₁ ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
          Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))⁆,
        ∀ d₂ ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)),
          Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))⁆,
          α d₁ = d₁ → α d₂ = d₂ → d₁ * d₂ = d₂ * d₁) := by
  classical
  haveI : CharP K₃ 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := n * 3) (by omega) (by rw [hK, pow_mul])
  set L := AlgebraicClosure K₃ with hL
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K₃ L).injective 2
  have h3L : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (3 : L) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  obtain ⟨ζ, hζ⟩ := KS11Lie6Proof.exists_units_orderOf_three L h3L
  have hσ3 : Fr ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hFr c
    simpa [pow_succ] using this
  have hz3 : (g₀ * x * g₀⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hz1 : g₀ * x * g₀⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    calc x = g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨k', hk'G, hk'⟩ := KS11Lie6Proof.exists_conj_dA_of_mem_short (L := L) hσ3 hζ hg₀ hz3 hz1
  obtain ⟨n₀, B, hn₀G, hB3, hB1, hn₀⟩ := triD4J_dA_conj_dB (L := L) hζ
  set ι := triEmb K₃ Fr L with hι
  set k := (ι g₀)⁻¹ * k' * n₀⁻¹ with hk
  have hkG : k ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem (inv_mem (triEmb_mem_adjointGroup g₀)) hk'G) (inv_mem hn₀G)
  have hxk : ι x = k * rootDiagUnit TwistTag.D4.tag ![B, B, 1, B] * k⁻¹ := by
    have hA : rootDiagUnit TwistTag.D4.tag (tup ζ gA) =
        n₀⁻¹ * rootDiagUnit TwistTag.D4.tag ![B, B, 1, B] * n₀ := by
      rw [← hn₀]
      group
    have hz : ι (g₀ * x * g₀⁻¹) = ι g₀ * ι x * (ι g₀)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hz, hA] at hk'
    rw [hk]
    calc ι x = (ι g₀)⁻¹ * (ι g₀ * ι x * (ι g₀)⁻¹) * ι g₀ := by group
      _ = (ι g₀)⁻¹ * (k' * (n₀⁻¹ * rootDiagUnit TwistTag.D4.tag ![B, B, 1, B] * n₀) * k'⁻¹) *
          ι g₀ := by rw [hk']
      _ = (ι g₀)⁻¹ * k' * n₀⁻¹ * rootDiagUnit TwistTag.D4.tag ![B, B, 1, B] *
          ((ι g₀)⁻¹ * k' * n₀⁻¹)⁻¹ := by group
  obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.Sec8.Item8ModelProof.exists_conj_mul_sigma hn1 hK hFr hα3 hαout
  obtain ⟨pK, hpK, hconj⟩ := triD4J_conj_form hy
  have h3 := triD4J_h3 hZ0 hα3 hpK hconj
  exact triD4J_model_core (L := L) hαx hpK hconj h3 hB3 hB1 hkG hxk

end Model2

end Model

section Card

private theorem triD4J_card_ne {q : ℕ} (hq : 2 ≤ q) : 3 * (q ^ 6 - 1) ≠ (q ^ 2 - 1) * (q ^ 3 + 1) := by
  intro h
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hz : (3 : ℤ) * ((q : ℤ) ^ 6 - 1) = ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub h1, Nat.cast_sub h6] at this
    linarith
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  nlinarith [pow_pos (show (0 : ℤ) < q by linarith) 5, pow_pos (show (0 : ℤ) < q by linarith) 2,
    pow_pos (show (0 : ℤ) < q by linarith) 3]

end Card

section Holds

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo


theorem triD4LemmaJ_holds : TriD4LemmaJ := by
  intro Γ _ _ J K a g lab hlab htag hodd hn3 hZ haJ ha3 ha1 hKc hKlab hgN hg3 hgout hga
  obtain ⟨K₃, _, _, hn1, hK₃, hs, hna, ⟨θ⟩⟩ := triD4_datum hlab htag
  haveI : CharP K₃ 2 := charP_two_of_card (m := lab.n * 3) (by rw [hK₃, pow_mul])
  set σ₀ := iterateFrobeniusEquiv K₃ 2 lab.n with hσ₀def
  have hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ lab.n := fun c => by
    rw [hσ₀def, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e₀⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn1 K₃ hK₃ σ₀ hσ₀
  set ψ : ↥J ≃* ↥(graphFixedRootGroup TwistTag.D4 K₃ σ₀.toRingHom) :=
    (ggCenterlessEquiv θ hZ).trans e₀ with hψ
  have hZ0 : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K₃ σ₀.toRingHom) = ⊥ :=
    tcent_center_bot_of_equiv e₀.symm (tcent_center_eq_bot_of_simple hs hna)
  set a' : ↥J := ⟨a, haJ⟩ with ha'
  set x := ψ a' with hx
  have hx3 : x ^ 3 = 1 := by
    have : a' ^ 3 = 1 := Subtype.ext (by simp [a', ha3])
    rw [hx, ← map_pow, this, map_one]
  have hx1 : x ≠ 1 := fun h => ha1 (congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm)))
  set gN : ↥(Subgroup.normalizer (J : Set Γ)) := ⟨g, hgN⟩ with hgN'
  set σJ : MulAut ↥J := J.normalizerMonoidHom gN with hσJdef
  have hσJ : ∀ j : ↥J, ((σJ j : ↥J) : Γ) = g * j * g⁻¹ := fun j => rfl
  set α : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ σ₀.toRingHom) := MulAut.congr ψ σJ with hαdef
  have hαψ : ∀ j : ↥J, α (ψ j) = ψ (σJ j) := by
    intro j
    rw [hαdef, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hα3 : α ^ 3 = 1 := by
    have hg3' : gN ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hg3)
    have : σJ ^ 3 = 1 := by rw [hσJdef, ← map_pow, hg3', map_one]
    rw [hαdef, ← map_pow, this, map_one]
  have hαout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut α := by
    rintro ⟨c, hc⟩
    apply hgout
    refine ⟨((ψ.symm c : ↥J) : Γ), (ψ.symm c).2, fun j hj => ?_⟩
    have h1 : α (ψ ⟨j, hj⟩) = c * ψ ⟨j, hj⟩ * c⁻¹ := by
      rw [← hc]
      rfl
    rw [hαψ] at h1
    have h2 : ψ (σJ ⟨j, hj⟩) = ψ (ψ.symm c * ⟨j, hj⟩ * (ψ.symm c)⁻¹) := by
      rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h3 := congrArg Subtype.val (ψ.injective h2)
    rw [hσJ] at h3
    simpa using h3
  have hαx : α x = x := by
    rw [hx, hαψ]
    congr 1
    apply Subtype.ext
    rw [hσJ]
    show g * a * g⁻¹ = a
    rw [Subgroup.mem_centralizer_singleton_iff.1 hga]
    group
  have hKc' := CFSG.Assembly.isComponentOf_iff_open.2 hKc
  have hKJ : K ≤ J := hKc'.1.trans inf_le_left
  set K' : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K₃ σ₀.toRingHom) :=
    (K.subgroupOf J).map ψ.toMonoidHom with hK'
  have hcentJ : (J ⊓ Subgroup.centralizer ({a} : Set Γ)).subgroupOf J =
      Subgroup.centralizer ({a'} : Set ↥J) := by
    ext j
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨j.2, congrArg Subtype.val h⟩
  have hKcJ : CFSG.Assembly.IsComponentOf (K.subgroupOf J) (Subgroup.centralizer ({a'} : Set ↥J)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hcentJ]
      exact Subgroup.comap_mono hKc'.1
    · rw [← hcentJ]
      exact hKc'.2.1.comap J.subtype
    · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKJ) hKc'.2.2
  have hK'c : CFSG.Assembly.IsComponentOf K'
      (Subgroup.centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K₃ σ₀.toRingHom))) := by
    have h := tcent_isComponentOf_map ψ hKcJ
    rwa [tcent_map_centralizer] at h
  have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKJ hk⟩ ∈ K' := fun k hk =>
    ⟨⟨k, hKJ hk⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
  have hK'D : K' ≤ ⁅Subgroup.centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K₃ σ₀.toRingHom)),
      Subgroup.centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K₃ σ₀.toRingHom))⁆ := by
    have hperf : ⁅K', K'⁆ = K' := by
      have h1 : (commutator ↥K').map K'.subtype = ⁅K', K'⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [← h1, hK'c.2.2.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hperf]
    exact Subgroup.commutator_mono hK'c.1 hK'c.1
  have h3q : ¬ 3 ∣ 2 ^ lab.n := by
    intro h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  obtain ⟨g', hg' | hg'⟩ :=
    Sec11.KS11Lie6Proof.d4ThreeConj_holds K₃ (2 ^ lab.n) σ₀ hK₃ hσ₀ h3q x hx3 hx1
  ·
    rcases triD4J_model hn1 hK₃ hσ₀ hZ0 hx3 hx1 hg' hα3 hαout hαx with hcen | hab
    · left
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := hcen _ (hK'D (hψK k hk))
      rw [hαψ] at h1
      have h2 := congrArg Subtype.val (ψ.injective h1)
      rw [hσJ] at h2
      calc k * g = g * k * g⁻¹ * g := by rw [h2]
        _ = g * k := by group
    · right
      refine ⟨⟨fun u v => ?_⟩⟩
      have huK : (u : Γ) ∈ K := u.2.1
      have hvK : (v : Γ) ∈ K := v.2.1
      have hug : (u : Γ) * g = g * u := Subgroup.mem_centralizer_singleton_iff.1 u.2.2
      have hvg : (v : Γ) * g = g * v := Subgroup.mem_centralizer_singleton_iff.1 v.2.2
      have hfix : ∀ w : Γ, ∀ hwK : w ∈ K, w * g = g * w → α (ψ ⟨w, hKJ hwK⟩) = ψ ⟨w, hKJ hwK⟩ := by
        intro w hwK hwg
        rw [hαψ]
        congr 1
        apply Subtype.ext
        rw [hσJ]
        show g * w * g⁻¹ = w
        rw [← hwg]
        group
      have h1 := hab _ (hK'D (hψK u huK)) _ (hK'D (hψK v hvK)) (hfix u huK hug) (hfix v hvK hvg)
      rw [← map_mul, ← map_mul] at h1
      have h2 := congrArg Subtype.val (ψ.injective h1)
      exact Subtype.ext h2
  ·
    exfalso
    have hz3 : (g' * x * g'⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    have hz1 : g' * x * g'⁻¹ ≠ 1 := by
      intro h1
      apply hx1
      calc x = g'⁻¹ * (g' * x * g'⁻¹) * g' := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨hcomm, -⟩ :=
      Sec11.KS11Lie6Proof.d4ThreeBCent_holds K₃ (2 ^ lab.n) σ₀ hK₃ hσ₀ h3q (g' * x * g'⁻¹) hg' hz3 hz1
    have hSC : (Sec11.KS11Lie4Proof.d4ShortSL2 K₃ σ₀.toRingHom :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K₃ σ₀.toRingHom)) ≤
          Subgroup.centralizer ({g' * x * g'⁻¹} : Set _) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hg' s hs
    have hK''c := tcent_isComponentOf_map (MulAut.conj g') hK'c
    rw [tcent_map_centralizer, MulAut.conj_apply] at hK''c
    have hσ3 : σ₀ ^ 3 = 1 := by
      refine RingEquiv.ext fun c => ?_
      have := ringEquiv_cube_apply_eq hK₃ hσ₀ c
      simpa [pow_succ] using this
    have h8 : 8 ≤ 2 ^ lab.n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn3
    have hK4 : 4 ≤ Nat.card K₃ := by
      rw [hK₃]
      calc 4 ≤ 2 ^ lab.n := by omega
        _ ≤ (2 ^ lab.n) ^ 3 := Nat.le_self_pow (by norm_num) _
    have hSq := Sec11.KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4
    have hK''S := tcent_component_eq hK''c hSC hcomm hSq
    obtain ⟨eS⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
    set F := orbitField TwistTag.D4 K₃ σ₀.toRingHom Sec11.KS11Lie4Proof.d4Outer with hFdef
    haveI : Finite ↥F := Subtype.finite
    have hFcard : Nat.card ↥F = Nat.card K₃ := Sec11.KS11Lie4Proof.natCard_orbitField_d4Outer hσ3
    haveI : CharP ↥F 2 := charP_two_of_card (m := lab.n * 3) (by rw [hFcard, hK₃, pow_mul])
    obtain ⟨hsF, hnaF⟩ := ggL48TBVac_simple_linear_two (K := ↥F) (by rw [hFcard]; exact hK4)
    let eKS : ↥K ≃* CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) ↥F) :=
      (Subgroup.subgroupOfEquivOfLe hKJ).symm.trans
        (((K.subgroupOf J).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
          ((K'.equivMapOfInjective _ (MulAut.conj g').injective).trans
            ((MulEquiv.subgroupCongr hK''S).trans (eS.symm.trans (projEquiv ↥F).symm))))
    have hZK : Subgroup.center ↥K = ⊥ :=
      tcent_center_bot_of_equiv eKS (tcent_center_eq_bot_of_simple hsF hnaF)
    have hcardK : Nat.card ↥K = Nat.card K₃ * (Nat.card K₃ ^ 2 - 1) := by
      rw [← Sec11.KS11Lie4Proof.card_d4ShortSL2 hσ3, ← hK''S]
      exact Nat.card_congr
        ((Subgroup.subgroupOfEquivOfLe hKJ).symm.trans
          (((K.subgroupOf J).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
            (K'.equivMapOfInjective _ (MulAut.conj g').injective))).toEquiv
    obtain ⟨-, lab', -, hraw⟩ := hKlab
    obtain ⟨R₀, _, I, F', -, -, θK, hlabeq⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    subst hlabeq
    dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
    obtain ⟨Fu, _, _, hFu, -, -, θu, -⟩ := hraw
    have h1 : Nat.card ↥K = Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ lab.n) Fu)) :=
      calc Nat.card ↥K = Nat.card (↥K ⧸ Subgroup.center ↥K) :=
            Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZK).trans
              QuotientGroup.quotientBot).toEquiv.symm
        _ = _ := Nat.card_congr θu.toEquiv
    have h2 := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd Nat.prime_two hn1 hFu
    have hg3' : Nat.gcd 3 (2 ^ lab.n + 1) = 3 :=
      Nat.gcd_eq_left ((gffa2_three_dvd_pow_add_one_iff lab.n).2 hodd)
    rw [hg3', ← h1, hcardK, hK₃] at h2
    have hq0 : 0 < (2 ^ lab.n) ^ 3 := by positivity
    have e6 : ((2 ^ lab.n) ^ 3) ^ 2 = (2 ^ lab.n) ^ 6 := (pow_mul (2 ^ lab.n) 3 2).symm
    have h3 : (2 ^ lab.n) ^ 3 * (3 * ((2 ^ lab.n) ^ 6 - 1)) =
        (2 ^ lab.n) ^ 3 * (((2 ^ lab.n) ^ 2 - 1) * ((2 ^ lab.n) ^ 3 + 1)) := by
      rw [← h2, e6, mul_assoc, mul_comm 3]
    exact triD4J_card_ne (show 2 ≤ 2 ^ lab.n by omega) (Nat.eq_of_mul_eq_mul_left hq0 h3)

end Holds

end CFSG.LocalAnalysis.GLTheoremA

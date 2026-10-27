module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOSign
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOPc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCases

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {d : ℕ}

@[expose] def B3Data {R : GL (Fin d) K} (x : StatedProj (matrixDerived (oQ R)))
    (R₁ R₂ : Subgroup (StatedProj (matrixDerived (oQ R)))) : Prop :=
  ∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (S : GL (Fin d) K)
    (hS : ∀ v, oQ (diagGL hw) ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ((1 : Kˣ) : K) * oQ R v)
    (J I : Finset (Fin d)) (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))),
    oTransport S 1 hS x = projH _ ⟨signGL K J, hJ⟩ ∧ (I = J ∨ I = Jᶜ) ∧ I.card = 4 ∧
      R₂.map (oTransport S 1 hS).toMonoidHom ≤ blockP K hw I ∧
      R₁.map (oTransport S 1 hS).toMonoidHom ≤ blockP K hw Iᶜ

omit [Finite K] in
theorem sq_eq_scalar_of_orderOf (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hd : 0 < d) {A : matrixDerived (oQ R)}
    (hx : orderOf (projH _ A) = 2) :
    ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * ((A : GL (Fin d) K) : Matrix _ _ K) = 1 ∨
      ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((A : GL (Fin d) K) : Matrix _ _ K) = -1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have h1 : projH _ (A * A) = projH _ 1 := by
    rw [map_mul, ← pow_two, ← hx, pow_orderOf_eq_one, map_one]
  rw [projH_eq_projH_iff, mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  have hc' : (GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) =
      ((A : GL (Fin d) K) * A)⁻¹ := by
    rw [hc]
    simp
  have hA2 : (A : GL (Fin d) K) * A = GeneralLinearGroup.scalar (Fin d) c⁻¹ := by
    rw [map_inv, hc', inv_inv]
  set M := ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hM
  set a : K := ((c⁻¹ : Kˣ) : K) with ha
  have hMM : M * M = a • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hM, ← Units.val_mul, hA2, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  have hAI : (A : GL (Fin d) K) * A ∈ CatalogueBGraphForm.isometryGroup d K R := by
    have hAm := matrixDerived_le_isometries (oQ R) A.2
    rw [matrixIsometries_oQ h2 R hR] at hAm
    exact mul_mem hAm hAm
  rw [CatalogueBGraphForm.mem_isometryGroup, Units.val_mul, hMM, transpose_smul, transpose_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at hAI
  have hR0 : (R : Matrix (Fin d) (Fin d) K) ≠ 0 := by
    intro h0
    have hne : (1 : Matrix (Fin d) (Fin d) K) ≠ 0 := by
      have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      exact one_ne_zero
    apply hne
    rw [← Units.mul_inv R, h0, Matrix.zero_mul]
  have haa : a * a = 1 := by
    have : (a * a - 1) • (R : Matrix (Fin d) (Fin d) K) = 0 := by rw [sub_smul, hAI, one_smul,
      sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hR0)
  have hpm : a = 1 ∨ a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by linear_combination haa
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  rcases hpm with h | h
  · left; rw [hMM, h, one_smul]
  · right; rw [hMM, h, neg_one_smul]

theorem orth_reduce (hK : ringChar K ≠ 2) (hd : 7 ≤ d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {x : StatedProj (matrixDerived (oQ R))}
    {R₁ R₂ : Subgroup (StatedProj (matrixDerived (oQ R)))} {p n : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p n) :
    (d = 7 ∧ Nat.card K = p ^ n ∧ B3Data x R₁ R₂) ∨
      ∃ A : matrixDerived (oQ R), x = projH _ A ∧
        ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = -1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨A, rfl⟩ := projH_surjective x
  rcases sq_eq_scalar_of_orderOf hK hR (by omega) hC.orderOf_eq with hA2 | hA2
  swap
  · exact Or.inr ⟨A, rfl, hA2⟩
  left
  have hAI : (A : GL (Fin d) K) ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ A.2
  have hAR : ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ * R *
      ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = R := by
    have := hAI
    rw [matrixIsometries_oQ h2 R hR, CatalogueBGraphForm.mem_isometryGroup] at this
    exact this
  obtain ⟨hab, c, hcA, horth, hdiag, hNFM, hNFP⟩ := exists_split_nf hK hR hAR hA2
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hAI hab c hcA horth hdiag
  set J := famJ hab with hJdef
  have hSA : S * (A : GL (Fin d) K) * S⁻¹ = signGL K J := by
    have := congrArg (fun g : similarityPairs _ => g.val.left) heq
    simp only [transPair_left, linPair_right, map_one, MulAut.one_apply] at this
    exact this
  have hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)) := by
    rw [← hSA]
    exact (derivedTransport S 1 hS A).2
  have hxJ : oTransport S 1 hS (projH _ A) = projH _ ⟨signGL K J, hJ⟩ := by
    rw [oTransport_proj]
    congr 1
    exact Subtype.ext hSA
  have hC' := hC.map (oTransport S 1 hS)
  rw [hxJ] at hC'
  have hx1 : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ≠ 1 := by
    intro h1
    have := hC'.orderOf_eq
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hJne : J.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hJe
    apply hx1
    rw [← map_one (projH (matrixDerived (oQ (diagGL hw))))]
    congr 1
    apply Subtype.ext
    change signGL K J = 1
    rw [hJe]
    exact signGL_empty
  have hJcne : Jᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hJe
    apply hx1
    have hJu : J = Finset.univ := by rw [← compl_compl J, hJe, Finset.compl_empty]
    have hsc : signGL K J = GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) := by
      apply Units.ext
      rw [coe_signGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hJu]
      ext i j
      simp [signMat, diagonal_apply]
    rw [← map_one (projH (matrixDerived (oQ (diagGL hw)))), projH_eq_projH_iff, mem_subgroupOf]
    refine ⟨-1, ?_⟩
    change _ = (signGL K J)⁻¹ * 1
    rw [hsc, mul_one, ← map_inv, inv_neg_one]

  have hNF : 3 ≤ J.card → BlockNF (famW (R : Matrix (Fin d) (Fin d) K) hab c) J := by
    intro h3
    exact hNFM (by rw [hJdef, card_famJ] at h3; exact h3)
  have hNFc : 3 ≤ Jᶜ.card → BlockNF (famW (R : Matrix (Fin d) (Fin d) K) hab c) Jᶜ := by
    intro h3
    refine hNFP ?_
    have h1 := card_compl_add J
    have h2 := card_famJ hab
    rw [← hJdef] at h2
    omega
  obtain ⟨hd7, hcard, I, hI, hI4, hR₂I, hR₁I⟩ := orth_sign_propC hw hK hd J hJ hJne hJcne
    hNF hNFc hC'
  exact ⟨hd7, hcard, _, hw, S, hS, J, I, hJ, hxJ, hI, hI4, hR₂I, hR₁I⟩

theorem orth_propC_odd (hK : ringChar K ≠ 2) (hd : 7 ≤ d) (hodd : Odd d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {x : StatedProj (matrixDerived (oQ R))}
    {R₁ R₂ : Subgroup (StatedProj (matrixDerived (oQ R)))} {p n : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p n) : d = 7 ∧ Nat.card K = p ^ n ∧ B3Data x R₁ R₂ := by
  rcases orth_reduce hK hd hR hC with h | ⟨A, -, hA2⟩
  · exact h
  · exfalso
    have hdet := det_eq_one_of_mem_commutator (H := matrixIsometries (oQ R)) A.2
    have h1 := congrArg Matrix.det hA2
    rw [Matrix.det_mul, hdet, mul_one, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin,
      hodd.neg_one_pow] at h1
    exact Ring.two_ne_zero hK (by linear_combination h1)

theorem orth_propC_even (hK : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ f) {m : ℕ} (hm : 4 ≤ m) {R : GL (Fin (2 * m)) K}
    (hR : (R : Matrix (Fin (2 * m)) (Fin (2 * m)) K)ᵀ = R)
    {x : StatedProj (matrixDerived (oQ R))}
    {R₁ R₂ : Subgroup (StatedProj (matrixDerived (oQ R)))} {p n : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p n) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rcases orth_reduce hK (by omega) hR hC with ⟨hd7, -⟩ | ⟨A, rfl, hA2⟩
  · exfalso
    omega
  have hAI : (A : GL (Fin (2 * m)) K) ∈ matrixIsometries (oQ R) :=
    matrixDerived_le_isometries _ A.2
  have hARR : ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K)ᵀ * R *
      ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = R := by
    have := hAI
    rw [matrixIsometries_oQ h2 R hR, CatalogueBGraphForm.mem_isometryGroup] at this
    exact this
  have hA2' : ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) *
      ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = (-1 : K) • 1 := by
    rw [hA2, neg_one_smul]
  have hAR : ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K)ᵀ * R =
      (-1 : K) • ((R : Matrix (Fin (2 * m)) (Fin (2 * m)) K) *
        ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K)) := by
    set M := ((A : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) with hM
    calc Mᵀ * (R : Matrix (Fin (2 * m)) (Fin (2 * m)) K)
        = Mᵀ * (R : Matrix (Fin (2 * m)) (Fin (2 * m)) K) * (M * -M) := by
          rw [Matrix.mul_neg, hA2, neg_neg, Matrix.mul_one]
      _ = (-1 : K) • ((R : Matrix (Fin (2 * m)) (Fin (2 * m)) K) * M) := by
          rw [← Matrix.mul_assoc (Mᵀ * (R : Matrix (Fin (2 * m)) (Fin (2 * m)) K)) M (-M), hARR,
            Matrix.mul_neg, neg_one_smul]
  obtain ⟨H, hgram, hAH⟩ := exists_pc_basis hK hR (neg_ne_zero.2 one_ne_zero) hA2' hAR
    (fun _ => 1) (fun _ => one_ne_zero)
  obtain ⟨R₁', hR₁'⟩ : ∃ R₁', R₁' = CatalogueBGraphForm.glTranspose (2 * m) K H * R * H :=
    ⟨_, rfl⟩
  have hgramR : (H : Matrix (Fin (2 * m)) (Fin (2 * m)) K)ᵀ * R * H = R₁' := by
    rw [hR₁']
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁' : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = blkDiag m (wMat 1 (-(-1))) := by
    rw [← hgramR, hgram]
    simp only [one_smul]
    rfl
  obtain ⟨hS, -, -⟩ := exists_transport_of_gram hgramR (g := linPair _ hAI) rfl
  have hC' := hC.map (oTransport H⁻¹ 1 hS)
  rw [oTransport_proj] at hC'
  have hAm : (((derivedTransport H⁻¹ 1 hS A : matrixDerived (oQ R₁')) : GL (Fin (2 * m)) K) :
      Matrix (Fin (2 * m)) (Fin (2 * m)) K) = blkDiag m (jMat (-1)) := by
    rw [coe_derivedTransport, Units.val_mul, Units.val_mul, inv_inv]
    exact inv_mul_mul_eq hAH
  exact pc_propC hK hℓ hKc (neg_ne_zero.2 one_ne_zero) (by omega) hR₁m hAm hC'

end CFSG.ComponentClassification.Burgoyne.C

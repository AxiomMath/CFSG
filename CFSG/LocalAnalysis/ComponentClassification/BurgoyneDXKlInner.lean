module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlTrans
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrInner
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K]

theorem false_of_k2_inner [Finite K] (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ e) {n : ℕ} (hn : 5 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R) (hker : OKer (oQ R))
    {M : Subgroup (GL (Fin (2 * n)) K)} (hd : K2Data R M) {gs : similarityPairs (oQ R)}
    (hσ : gs.val.right = 1) (hss : oκ _ (gs * gs) = 1) (hs1 : oκ _ gs ≠ 1)
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ gs))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ gs)))) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set H := matrixDerived (oQ R) with hH
  set S := gs.val.left with hSdef
  set Sm := (S : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hSm
  set Rm := (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hRm
  obtain ⟨c, hc0, hS2, hε, -⟩ := inner_even_data h2 hR (by omega) hker hσ hss
  rcases hε with hε | hε
  swap
  · exact false_of_k2_skew hK hℓ hKc (by omega) hR hd hσ hc0 hS2 hε hQs hQc
  by_cases hsq : IsSquare c
  swap
  · exact false_of_k2_nonsq hK hn hR hd hσ hsq hS2 hε hQs hQc
  have hperfH : ⁅M.subgroupOf H, M.subgroupOf H⁆ = M.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hd.le, hd.perf]
  have hfixP : ∀ X ∈ M.subgroupOf H, oκ _ gs (projH H X) = projH H X :=
    fun X hX => hQs ⟨X, hX, rfl⟩
  have hSSi : Sm * ((S⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = 1 := by
    rw [hSm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hSiS : ((S⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * Sm = 1 := by
    rw [hSm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSM : ∀ X ∈ M, Sm * (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = X * Sm := by
    intro X hX
    have e := kappa_eq_of_fix gs hperfH hfixP (X := ⟨X, hd.le hX⟩) (mem_subgroupOf.2 hX)
    rw [hσ] at e
    have e2 : ((X : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map
        ⇑(1 : K ≃+* K) = X := by
      ext
      rfl
    change Sm * ((X : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map
      ⇑(1 : K ≃+* K) * ((S⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = X at e
    rw [e2] at e
    calc Sm * (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        (Sm * X * ((S⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) * Sm := by
          rw [Matrix.mul_assoc _ _ Sm, hSiS, Matrix.mul_one]
      _ = X * Sm := by rw [e]
  have hSR : Smᵀ * Rm * Sm = c • Rm := by
    rw [hε, one_smul, Matrix.mul_assoc, hS2, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨s₀, hs₀⟩ := hsq
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [hs₀, mul_zero])
  obtain ⟨S', hS'def⟩ : ∃ S' : GL (Fin (2 * n)) K,
      S' = GeneralLinearGroup.scalar (Fin (2 * n)) (Units.mk0 s₀ hs₀0)⁻¹ * S := ⟨_, rfl⟩
  have hS'c : (S' : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = s₀⁻¹ • Sm := by
    rw [hS'def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Units.val_inv_eq_inv_val, Units.val_mk0]
  have hS'R : (S' : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * Rm * S' = Rm := by
    rw [hS'c, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hSR,
      smul_smul, smul_smul, hs₀]
    rw [show s₀⁻¹ * s₀⁻¹ * (s₀ * s₀) = 1 by field_simp, one_smul]
  have hS'2 : (S' : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * S' = 1 := by
    rw [hS'c, Matrix.smul_mul, Matrix.mul_smul, hS2, smul_smul, smul_smul, hs₀]
    rw [show s₀⁻¹ * s₀⁻¹ * (s₀ * s₀) = 1 by field_simp, one_smul]
  have hS' : S' ∈ matrixIsometries (oQ R) :=
    (mem_matrixIsometries_oQ h2 R hR S').2
      ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hS'R)
  have hκ : oκ _ gs = oκ _ (linPair S' hS') := by
    refine oκ_eq_of_left_eq (c := Units.mk0 s₀ hs₀0) (by rw [hσ, linPair_right]) ?_
    rw [linPair_left, hS'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hκ] at hQs hQc hs1
  have hS'M : ∀ X ∈ M, X * S' = S' * X := by
    intro X hX
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hS'c, Matrix.mul_smul, Matrix.smul_mul, hSM X hX]
  obtain ⟨hab, cfr, hcA, horth, hdiag, -, -⟩ := exists_split_nf hK hR hS'R hS'2
  obtain ⟨hw, Str, hStr, heq⟩ := exists_transport_of_family h2 hS' hab cfr hcA horth hdiag
  set w := famW Rm hab cfr with hwdef
  set J := famJ hab with hJdef
  have hd' := hd.transport Str 1 hStr
  obtain ⟨-, hQc'⟩ := transport_comp hd.le Str 1 hStr hQs hQc
  rw [heq] at hQc'
  have hSJ : signGL K J = Str * S' * Str⁻¹ := by
    have e := congrArg (fun g : similarityPairs (oQ (diagGL hw)) => g.val.left) heq
    simp only [transPair_left, linPair_left, linPair_right, map_one, MulAut.one_apply] at e
    exact e.symm
  have hfix' : ∀ X ∈ M.map (MulAut.conj Str).toMonoidHom, X * signGL K J = signGL K J * X := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [hSJ]
    change Str * Y * Str⁻¹ * (Str * S' * Str⁻¹) = Str * S' * Str⁻¹ * (Str * Y * Str⁻¹)
    have e := hS'M Y hY
    calc Str * Y * Str⁻¹ * (Str * S' * Str⁻¹) = Str * (Y * S') * Str⁻¹ := by group
      _ = Str * (S' * Y) * Str⁻¹ := by rw [e]
      _ = Str * S' * Str⁻¹ * (Str * Y * Str⁻¹) := by group
  have hne : oκ _ (sgnPair h2 hw J) ≠ 1 := by
    rw [hJdef, ← heq, ← oTransport_kappa]
    intro h1
    apply hs1
    exact (MulAut.congr (oTransport Str 1 hStr)).injective (by rw [h1, map_one])
  have hJ : J.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h => hne (oκ_sgnPair_eq_one h2 hw (Or.inl h))
  have hJc : Jᶜ.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h =>
    hne (oκ_sgnPair_eq_one h2 hw (Or.inr (Finset.compl_eq_empty_iff _ |>.1 h)))
  have hJ : J.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h => hne (oκ_sgnPair_eq_one h2 hw (Or.inl h))
  have hJc : Jᶜ.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h =>
    hne (oκ_sgnPair_eq_one h2 hw (Or.inr (Finset.compl_eq_empty_iff _ |>.1 h)))
  exact false_of_k2_sign hK hw hd' hJ hJc hfix' hQc'

end CFSG.ComponentClassification.Burgoyne.DX.Kl

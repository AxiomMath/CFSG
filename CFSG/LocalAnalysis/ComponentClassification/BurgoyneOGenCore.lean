module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd diagGL coe_diagGL signMat signMat_eq
  signMat_mul_self commute_signMat_iff commute_compInd_compl compInd_compl
  isSubnormal_subgroupOf_of_normalizes mul_conj_mul_inv)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem commute_sign_of_odd (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (hd : 0 < d)
    (hker : OKer (oQ (diagGL hw))) (J' : Finset (Fin d)) {g : similarityPairs (oQ (diagGL hw))}
    (hodd : Odd (orderOf (oκ _ g)))
    (hc : oκ _ g * oκ _ (sgnPair h2 hw J') = oκ _ (sgnPair h2 hw J') * oκ _ g) :
    signMat K J' * (g.val.left : Matrix (Fin d) (Fin d) K) =
      (g.val.left : Matrix (Fin d) (Fin d) K) * signMat K J' := by
  set D := g.val.left with hD
  have hsgnI : signGL K J' ∈ matrixIsometries (oQ (diagGL hw)) :=
    (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) _).2 (signGL_mem hw J')
  have hτS : glFieldAut (Fin d) K g.val.right (signGL K J') = signGL K J' := by
    apply Units.ext
    rw [coe_glFieldAut, coe_signGL, map_signMat_field]
  have hcomm : oκ _ (g * sgnPair h2 hw J' * g⁻¹ * (sgnPair h2 hw J')⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨-, c, hcc⟩ := hker _ hcomm
  obtain ⟨hcl, -⟩ := commPair_val g (signGL K J') hsgnI hτS
  have e1 : D * signGL K J' * D⁻¹ * (signGL K J')⁻¹ = GeneralLinearGroup.scalar (Fin d) c := by
    rw [← hcl, hcc]
    rfl
  have e2 : D * signGL K J' * D⁻¹ = GeneralLinearGroup.scalar (Fin d) c * signGL K J' := by
    rw [← e1, inv_mul_cancel_right]
  have hc2 : c * c = 1 := by
    have e3 : (D * signGL K J' * D⁻¹) * (D * signGL K J' * D⁻¹) = 1 := by
      rw [show (D * signGL K J' * D⁻¹) * (D * signGL K J' * D⁻¹) =
        D * (signGL K J' * signGL K J') * D⁻¹ by group]
      rw [show signGL K J' * signGL K J' = 1 from Units.ext (signMat_mul_self J'), mul_one,
        mul_inv_cancel]
    rw [e2, show GeneralLinearGroup.scalar (Fin d) c * signGL K J' *
      (GeneralLinearGroup.scalar (Fin d) c * signGL K J') = GeneralLinearGroup.scalar (Fin d)
        (c * c) * (signGL K J' * signGL K J') by
          rw [map_mul]
          have := (commute_scalar c (signGL K J')).eq
          calc _ = GeneralLinearGroup.scalar (Fin d) c * (signGL K J' *
              GeneralLinearGroup.scalar (Fin d) c) * signGL K J' := by group
            _ = _ := by rw [this]; group,
      show signGL K J' * signGL K J' = 1 from Units.ext (signMat_mul_self J'), mul_one] at e3
    have := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩) e3
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
      Units.val_one, one_apply_eq] at this
    exact Units.ext this
  have hDm : (D : Matrix (Fin d) (Fin d) K) * signMat K J' =
      (c : K) • (signMat K J' * (D : Matrix (Fin d) (Fin d) K)) := by
    have e4 : D * signGL K J' = GeneralLinearGroup.scalar (Fin d) c * signGL K J' * D := by
      rw [← e2, inv_mul_cancel_right]
    have e5 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)) e4
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_signGL] at e5
    rw [e5, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul]
  have hc2' : (c : K) * c = 1 := by rw [← Units.val_mul, hc2, Units.val_one]
  rcases mul_self_eq_one_iff.1 hc2' with hc1 | hc1
  · rw [hDm, hc1, one_smul]
  exfalso
  have hDm' : (D : Matrix (Fin d) (Fin d) K) * signMat K J' =
      -(signMat K J' * (D : Matrix (Fin d) (Fin d) K)) := by rw [hDm, hc1, neg_one_smul]
  have hpow : ∀ k : ℕ, (((g ^ k).val.left : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      signMat K J' = (-1 : K) ^ k •
        (signMat K J' * (((g ^ k).val.left : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
    intro k
    induction k with
    | zero =>
      change ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * _ = _
      simp
    | succ k ih =>
      have e : (((g ^ (k + 1)).val.left : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          (((g ^ k).val.left : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            (D : Matrix (Fin d) (Fin d) K).map (g ^ k).val.right := by
        rw [pow_succ]
        change ((((g ^ k).val * g.val).left : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
        rw [SemidirectProduct.mul_left, Units.val_mul, coe_glFieldAut]
      have eS : (D : Matrix (Fin d) (Fin d) K).map (g ^ k).val.right * signMat K J' =
          -(signMat K J' * (D : Matrix (Fin d) (Fin d) K).map (g ^ k).val.right) := by
        have := congrArg ((g ^ k).val.right : K ≃+* K).toRingHom.mapMatrix hDm'
        rw [map_mul, map_neg, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_signMat_field] at this
        exact this
      rw [e, Matrix.mul_assoc, eS, Matrix.mul_neg, ← Matrix.mul_assoc, ih, Matrix.smul_mul,
        Matrix.mul_assoc, pow_succ, mul_smul, neg_one_smul, smul_neg]
  obtain ⟨-, l, hl⟩ := hker _ (by rw [map_pow]; exact pow_orderOf_eq_one (oκ _ g))
  have e := hpow (orderOf (oκ _ g))
  rw [← hl, hodd.neg_one_pow, neg_one_smul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one] at e
  have e' : ((2 : K) * l) • signMat K J' = 0 := by
    rw [mul_smul, two_smul]
    nth_rewrite 1 [e]
    rw [neg_add_cancel]
  have hS0 : signMat K J' ≠ 0 := by
    intro h0
    have := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨0, hd⟩ ⟨0, hd⟩) h0
    simp only [signMat, diagonal_apply_eq, Matrix.zero_apply] at this
    split_ifs at this <;> simp at this
  exact hS0 ((smul_eq_zero.1 e').resolve_left (mul_ne_zero h2 l.ne_zero))

theorem conj_mem_oIsoBlock_of {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J J' : Finset (Fin d)}
    {h : GL (Fin d) K} (hh : h ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hc : compInd K J * (h : Matrix (Fin d) (Fin d) K) =
      (h : Matrix (Fin d) (Fin d) K) * compInd K J')
    {g : GL (Fin d) K} (hg : g ∈ oIsoBlock K hw J') : h * g * h⁻¹ ∈ oIsoBlock K hw J := by
  obtain ⟨hgI, hg1, hg2⟩ := hg
  set H := (h : Matrix (Fin d) (Fin d) K) with hH
  set Hi := ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hHi
  set G := (g : Matrix (Fin d) (Fin d) K) with hG
  have e1 : H * Hi = 1 := by rw [hH, hHi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : Hi * H = 1 := by rw [hH, hHi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hhi : Hi * compInd K J = compInd K J' * Hi := by
    calc Hi * compInd K J = Hi * (compInd K J * H) * Hi := by
          rw [Matrix.mul_assoc Hi, Matrix.mul_assoc (compInd K J), e1, Matrix.mul_one]
      _ = Hi * (H * compInd K J') * Hi := by rw [hc]
      _ = compInd K J' * Hi := by rw [← Matrix.mul_assoc, e2, Matrix.one_mul]
  refine ⟨mul_mem (mul_mem hh hgI) (inv_mem hh), ?_, ?_⟩
  · change compInd K J * (H * G * Hi) = compInd K J
    calc compInd K J * (H * G * Hi) = H * (compInd K J' * G) * Hi := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc H (compInd K J') G]
      _ = compInd K J := by
          rw [hg1, Matrix.mul_assoc, ← hhi, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  · change (H * G * Hi) * compInd K J = compInd K J
    calc (H * G * Hi) * compInd K J = H * (G * compInd K J') * Hi := by
          rw [Matrix.mul_assoc, hhi, ← Matrix.mul_assoc, Matrix.mul_assoc H G (compInd K J')]
      _ = compInd K J := by rw [hg2, ← hc, Matrix.mul_assoc, e1, Matrix.mul_one]

theorem conj_mem_oBlock_of {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J J' : Finset (Fin d)}
    {h : GL (Fin d) K} (hh : h ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hc : compInd K J * (h : Matrix (Fin d) (Fin d) K) =
      (h : Matrix (Fin d) (Fin d) K) * compInd K J')
    {g : GL (Fin d) K} (hg : g ∈ oBlock K hw J') : h * g * h⁻¹ ∈ oBlock K hw J := by
  have hle : oBlock K hw J' ≤ (oBlock K hw J).comap (MulAut.conj h).toMonoidHom := by
    rw [oBlock, Subgroup.commutator_le]
    intro a ha b hb
    change h * ⁅a, b⁆ * h⁻¹ ∈ oBlock K hw J
    have e : h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by group
    rw [e]
    exact commutator_mem_commutator (conj_mem_oIsoBlock_of hw hh hc ha)
      (conj_mem_oIsoBlock_of hw hh hc hb)
  exact hle hg

theorem commute_of_mem_oIsoBlock_compl {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {I : Finset (Fin d)}
    {X Y : GL (Fin d) K} (hX : X ∈ oIsoBlock K hw I) (hY : Y ∈ oIsoBlock K hw Iᶜ) :
    X * Y = Y * X := by
  obtain ⟨-, hX1, hX2⟩ := hX
  obtain ⟨-, hY1, hY2⟩ := hY
  rw [compInd_compl] at hY1 hY2
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set P := compInd K I
  set Xm := (X : Matrix (Fin d) (Fin d) K)
  set Ym := (Y : Matrix (Fin d) (Fin d) K)
  have hY1' : P * Ym = Ym - 1 + P := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hY1
    calc P * Ym = Ym - (Ym - P * Ym) := by abel
      _ = Ym - (1 - P) := by rw [hY1]
      _ = Ym - 1 + P := by abel
  have hY2' : Ym * P = Ym - 1 + P := by
    rw [Matrix.mul_sub, Matrix.mul_one] at hY2
    calc Ym * P = Ym - (Ym - Ym * P) := by abel
      _ = Ym - (1 - P) := by rw [hY2]
      _ = Ym - 1 + P := by abel
  have eY : Ym = 1 - P + Ym * P := by rw [hY2']; abel
  calc Xm * Ym = Xm * (1 - P + Ym * P) := by rw [← eY]
    _ = Xm - P + Xm * (Ym * P) := by rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, hX2]
    _ = Xm - P + P * Ym := by
        rw [hY2', ← hY1', ← Matrix.mul_assoc, hX2]
    _ = (1 - P + Ym * P) * Xm := by
        rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hX1, hY2', hY1']
    _ = Ym * Xm := by rw [← eY]

end CFSG.ComponentClassification.Burgoyne.O

module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthThree

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_mul_self
  pow_eight_of_similitude_three embedVec embedVec_apply embedVec_single pow_mulVec_embedVec
  similitude_submatrix)

variable {K : Type} [Field K] {d : ℕ}

theorem pow_eight_of_blocks [Finite K] (h3 : Nat.card K = 3) {D : Matrix (Fin d) (Fin d) K}
    {a : Fin d → K} (ha : ∀ x, a x ≠ 0) {l : K} (hl : l ≠ 0)
    (hsim : D * diagonal a * Dᵀ = diagonal fun x => l * a x)
    (hT : ∀ x, ∃ T : Finset (Fin d), x ∈ T ∧ (T.card = 1 ∨ T.card = 2) ∧
      ∀ y z, (y ∈ T ↔ z ∉ T) → D y z = 0) : D ^ 8 = 1 := by
  have hcol : ∀ x, D ^ 8 *ᵥ Pi.single x 1 = Pi.single x 1 := by
    intro x
    obtain ⟨T, hxT, hcard, hTD⟩ := hT x
    set ι : Fin T.card → Fin d := fun u => (T.equivFin.symm u : Fin d) with hι
    have hιinj : Function.Injective ι := fun u v h => T.equivFin.symm.injective (Subtype.ext h)
    have hrange : ∀ z, z ∈ Set.range ι ↔ z ∈ T := by
      intro z
      constructor
      · rintro ⟨u, rfl⟩
        exact (T.equivFin.symm u).2
      · intro hz
        exact ⟨T.equivFin ⟨z, hz⟩, by simp [hι]⟩
    have hιT : ∀ u, ι u ∈ T := fun u => (hrange _).1 ⟨u, rfl⟩
    have hD : ∀ y u, y ∉ Set.range ι → D y (ι u) = 0 := by
      intro y u hy
      rw [hrange] at hy
      exact hTD y (ι u) ⟨fun h => absurd h hy, fun h => absurd (hιT u) h⟩
    have hD' : ∀ u z, z ∉ Set.range ι → D (ι u) z = 0 := by
      intro u z hz
      rw [hrange] at hz
      exact hTD (ι u) z ⟨fun _ => hz, fun _ => hιT u⟩
    have hX := pow_eight_of_similitude_three h3 hcard (fun u => ha (ι u)) hl
      (similitude_submatrix hιinj hsim hD')
    obtain ⟨u, rfl⟩ := (hrange x).2 hxT
    rw [← embedVec_single hιinj, pow_mulVec_embedVec hιinj hD, hX, one_mulVec]
  ext y x
  have e := congrFun (hcol x) y
  rw [mulVec_single_one, Matrix.col_apply] at e
  rw [e, Pi.single_apply, one_apply, eq_comm]

theorem ringEquiv_eq_one_of_card_three [Finite K] (h3 : Nat.card K = 3) (τ : K ≃+* K) :
    τ = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h3]
  set e := FiniteField.ringEquivOfCardEq hc
  have h1 : τ.toRingHom.comp e.symm.toRingHom = e.symm.toRingHom := RingHom.ext_zmod _ _
  refine RingEquiv.ext fun x => ?_
  have := congrArg (fun φ : ZMod 3 →+* K => φ (e x)) h1
  simpa using this

theorem sgnPair_mul (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (J J' : Finset (Fin d)) {J'' : Finset (Fin d)}
    (hJ : signMat K J * signMat K J' = signMat K J'') :
    sgnPair h2 hw J * sgnPair h2 hw J' = sgnPair h2 hw J'' := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change signGL K J * glFieldAut (Fin d) K 1 (signGL K J') = signGL K J''
    rw [map_one, MulAut.one_apply]
    exact Units.ext hJ
  · change (1 : K ≃+* K) * 1 = 1
    rw [mul_one]

theorem signMat_mul_comm (J J' : Finset (Fin d)) :
    signMat K J * signMat K J' = signMat K J' * signMat K J := by
  rw [signMat, signMat, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem signMat_empty : signMat K (∅ : Finset (Fin d)) = 1 := by
  simp [signMat]

theorem sgnPair_mul_self (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (J : Finset (Fin d)) : sgnPair h2 hw J * sgnPair h2 hw J = 1 := by
  rw [sgnPair_mul h2 hw J J ((signMat_mul_self J).trans signMat_empty.symm)]
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change signGL K (∅ : Finset (Fin d)) = 1
    apply Units.ext
    rw [coe_signGL, signMat_empty, Units.val_one]
  · rfl

theorem oκ_linPair_eq_conj {Q : QuadraticForm K (Fin d → K)} {X : GL (Fin d) K}
    (hX : X ∈ matrixIsometries Q) (hXH : X ∈ matrixDerived Q) :
    oκ Q (linPair X hX) = conjProjH (matrixDerived Q) ⟨X, hXH⟩ := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨Y, rfl⟩ := projH_surjective y
  rw [kappa_proj]
  change _ = projH _ ⟨X, hXH⟩ * projH _ Y * (projH _ ⟨X, hXH⟩)⁻¹
  rw [← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem commute_sign_of_commute (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hker : OKer (oQ (diagGL hw))) {J' : Finset (Fin d)} (hJd : 2 * J'.card ≠ d)
    {g : similarityPairs (oQ (diagGL hw))}
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
    have hd0 : 0 < d := by
      by_contra h0
      have hc0 : J'.card = 0 := by
        have := J'.card_le_univ
        rw [Fintype.card_fin] at this
        omega
      exact hJd (by omega)
    have := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K) ⟨0, hd0⟩ ⟨0, hd0⟩) e3
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
  · exfalso
    apply hJd
    refine two_mul_card_eq_of_anticommute h2 (h := D) ?_
    rw [hDm, hc1, neg_one_smul, neg_neg]

end CFSG.ComponentClassification.Burgoyne.O

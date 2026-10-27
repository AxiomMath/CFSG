module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOFix
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplit

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (compInd commute_compInd_iff diagGL coe_diagGL
  signMat
  signMat_mul_self commute_signMat_iff reflGL reflGL_mem rotGL rotGL_mem rotMat
  rotMat_neg_one_zero rotMat_apply_left commutatorElement_reflGL_rotGL eq_one_of_fix_circle)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem ClO.split_core [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {J : Finset (Fin d)} (hJd : 2 * J.card ≠ d) {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ)
    (hI3 : 3 ≤ I.card) (hIexc : ¬ (Nat.card K = 3 ∧ I.card ≤ 4))
    {I₀ : Finset (Fin d)} (hI₀ : I₀ ⊆ I) (hI₀3 : 3 ≤ I₀.card)
    (hI₀w : ∀ i ∈ I₀, ∀ j ∈ I₀, w i = w j)
    (hI₀c : ∀ x ∈ I, ∀ y ∈ I, x ∉ I₀ → y ∉ I₀ → x = y)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    {g : similarityPairs (oQ (diagGL hw))} (hy : oκ _ g ∈ Ro) :
    g.val.right = 1 ∧
      signMat K J * (g.val.left : Matrix (Fin d) (Fin d) K) =
        (g.val.left : Matrix (Fin d) (Fin d) K) * signMat K J ∧
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hHeq : matrixDerived (oQ (diagGL hw)) = ⁅CatalogueBGraphForm.isometryGroup d K (diagGL hw),
      CatalogueBGraphForm.isometryGroup d K (diagGL hw)⁆ :=
    matrixDerived_oQ h2 (diagGL hw) (diagGL_transpose hw)
  have hIH : oBlock K hw I ≤ matrixDerived (oQ (diagGL hw)) := by
    rw [hHeq]; exact oBlock_le hw I
  set D := g.val.left with hD
  set τ := g.val.right with hτ
  have hodd := ClSp.odd_orderOf_of_mem hRodd hy
  have hτm : τ ^ orderOf (oκ _ g) = 1 := hker.right_pow_eq_one (pow_orderOf_eq_one _)
  have hfix : ∀ X : matrixDerived (oQ (diagGL hw)), (X : GL (Fin d) K) ∈ oBlock K hw I →
      (D : Matrix (Fin d) (Fin d) K) * ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map τ *
        ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    fun X hX => ClO.block_fix_of_components hK hw hinj hJd hI hI3 hIexc hRodd hRi hRc hy hX
  have hfix' : ∀ X : GL (Fin d) K, X ∈ oBlock K hw I →
      (D : Matrix (Fin d) (Fin d) K) * (X : Matrix (Fin d) (Fin d) K).map τ *
        ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = X :=
    fun X hX => hfix ⟨X, hIH hX⟩ hX
  have hS : ∀ i ∈ I₀, ∀ j ∈ I₀, i ≠ j → (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} =
      signMat K {i, j} * D := by
    intro i hi j hj hij
    have e := hfix' _ (signGL_pair_mem_oBlock hw (hI₀ hi) (hI₀ hj) hij (hI₀w i hi j hj))
    rw [coe_signGL, map_signMat_field] at e
    calc (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} =
        (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} *
          (((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * D) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = signMat K {i, j} * D := by rw [← Matrix.mul_assoc, e]
  have hiso₀ : ∀ x y, x ≠ y → (x ∈ I₀ ∨ y ∈ I₀) → (D : Matrix (Fin d) (Fin d) K) x y = 0 :=
    fun x y hxy hxI => offDiag_eq_zero_of_commute_sign_on h2 hI₀3 hS hxy hxI
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ I₀, ∃ j ∈ I₀, i ≠ j := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < I₀.card)
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (by
      have := Finset.pred_card_le_card_erase (s := I₀) (a := i); omega : 0 < (I₀.erase i).card)
    exact ⟨i, hi, j, (Finset.mem_erase.1 hj).2, Ne.symm (Finset.mem_erase.1 hj).1⟩
  have hτ1 : τ = 1 := by
    refine eq_one_of_fix_circle hK fun a b hab => ?_
    have e := hfix' _ (comm_mem_oBlock hw (hI₀ hi) (hI₀ hj) hij (hI₀w i hi j hj) hab)
    have e' := congrFun (congrFun e i) i
    rw [conj_apply_diag_of_isolated (fun x hx => hiso₀ i x (Ne.symm hx) (Or.inl hi))
      (fun x hx => hiso₀ x i hx (Or.inr hi)), map_apply, commutatorElement_reflGL_rotGL,
      rotMat_apply_left hij] at e'
    have hb : b ^ 2 = 1 - a ^ 2 := by linear_combination hab
    rw [hb] at e'
    have hτa2 : τ (a ^ 2) = a ^ 2 := by
      have e2 : τ (2 * a ^ 2 - 1) = 2 * a ^ 2 - 1 := by
        have h3 : (2 * a ^ 2 - 1 : K) = a ^ 2 - (1 - a ^ 2) := by ring
        rw [h3]
        exact e'
      rw [map_sub, map_mul, map_one, map_ofNat] at e2
      have : (2 : K) * (τ (a ^ 2) - a ^ 2) = 0 := by linear_combination e2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2)
    rw [map_pow] at hτa2
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hτa2 with h | h
    · exact h
    · have hpow : ∀ m : ℕ, (τ ^ m) a = (-1) ^ m * a := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ]
          change (τ ^ m) (τ a) = _
          rw [h, map_neg, ih, pow_succ]
          ring
      have := hpow (orderOf (oκ _ g))
      rw [hτm, hodd.neg_one_pow] at this
      change a = -1 * a at this
      have ha0 : a = 0 := by
        have : (2 : K) * a = 0 := by linear_combination this
        exact (mul_eq_zero.1 this).resolve_left h2
      rw [h, ha0, neg_zero]
  have hsgnI : signGL K J ∈ matrixIsometries (oQ (diagGL hw)) :=
    (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) _).2 (signGL_mem hw J)
  have hτS : glFieldAut (Fin d) K τ (signGL K J) = signGL K J := by
    apply Units.ext
    rw [coe_glFieldAut, coe_signGL, map_signMat_field]
  have hcomm : oκ _ (g * sgnPair h2 hw J * g⁻¹ * (sgnPair h2 hw J)⁻¹) = 1 := by
    have hc := hRi _ hy
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨-, c, hc⟩ := hker _ hcomm
  obtain ⟨hcl, -⟩ := commPair_val g (signGL K J) hsgnI hτS
  have hDS : (D : Matrix (Fin d) (Fin d) K) * signMat K J = (c : K) • (signMat K J * D) := by
    have e1 : D * signGL K J * D⁻¹ * (signGL K J)⁻¹ = GeneralLinearGroup.scalar (Fin d) c := by
      rw [← hcl, hc]
      rfl
    have e2 : D * signGL K J = GeneralLinearGroup.scalar (Fin d) c * signGL K J * D := by
      rw [← e1]
      group
    have e3 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)) e2
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_signGL] at e3
    rw [e3, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul]
  have hDii : (D : Matrix (Fin d) (Fin d) K) i i ≠ 0 := by
    intro h0
    have hcol : (D : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single i 1 = 0 := by
      funext x
      rw [mulVec_single_one, col_apply, Pi.zero_apply]
      by_cases hx : x = i
      · rw [hx, h0]
      · exact hiso₀ x i hx (Or.inr hi)
    have := congrArg (fun v => ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) hcol
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
      mulVec_zero] at this
    have h1 := congrFun this i
    simp at h1
  have hc1 : (c : K) = 1 := by
    have e := congrFun (congrFun hDS i) i
    rw [Matrix.smul_apply, signMat, mul_diagonal, diagonal_mul, smul_eq_mul] at e
    have hsi : (if i ∈ J then (-1 : K) else 1) ≠ 0 := by split_ifs <;> simp
    have : ((D : Matrix (Fin d) (Fin d) K) i i * (if i ∈ J then (-1 : K) else 1)) *
        (1 - c) = 0 := by linear_combination e
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero hDii hsi)
    · exact (sub_eq_zero.1 h).symm
  have hDS' : signMat K J * (D : Matrix (Fin d) (Fin d) K) = (D : Matrix (Fin d) (Fin d) K) *
      signMat K J := by rw [hDS, hc1, one_smul]
  refine ⟨hτ1, hDS', ?_⟩
  have hblock := (commute_compInd_iff J _).1 ((commute_signMat_iff h2 J _).1 hDS')
  have hsep : ∀ x ∈ I, ∀ y ∉ I, (x ∈ J ↔ y ∉ J) ∧ (y ∈ J ↔ x ∉ J) := by
    intro x hxI y hyI
    rcases hI with hIJ | hIJ
    · rw [hIJ] at hxI hyI
      exact ⟨⟨fun _ => hyI, fun _ => hxI⟩, ⟨fun h => absurd h hyI, fun h => absurd hxI h⟩⟩
    · rw [hIJ, Finset.mem_compl] at hxI
      rw [hIJ, Finset.mem_compl, not_not] at hyI
      exact ⟨⟨fun h => absurd h hxI, fun h => absurd hyI h⟩, ⟨fun _ => hxI, fun _ => hyI⟩⟩
  intro x hx y hyx
  by_cases hx₀ : x ∈ I₀
  · exact ⟨hiso₀ x y (Ne.symm hyx) (Or.inl hx₀), hiso₀ y x hyx (Or.inr hx₀)⟩
  by_cases hy₀ : y ∈ I₀
  · exact ⟨hiso₀ x y (Ne.symm hyx) (Or.inr hy₀), hiso₀ y x hyx (Or.inl hy₀)⟩
  by_cases hyI : y ∈ I
  · exact absurd (hI₀c y hyI x hx hy₀ hx₀) hyx
  · exact ⟨hblock x y (hsep x hx y hyI).1, hblock y x (hsep x hx y hyI).2⟩

end CFSG.ComponentClassification.Foote5.OddLieCore

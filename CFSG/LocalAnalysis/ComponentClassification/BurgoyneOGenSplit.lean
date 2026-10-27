module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenFix

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd diagGL coe_diagGL signMat
  commute_signMat_iff commute_compInd_iff mem_of_mem_oddCoreIn eq_one_of_fix_circle
  commutatorElement_reflGL_rotGL rotMat_apply_left)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem split_core_gen (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    {J : Finset (Fin d)} {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ)
    (hI3 : 3 ≤ I.card) (hIexc : ¬ (Nat.card K = 3 ∧ I.card ≤ 4))
    {I₀ : Finset (Fin d)} (hI₀ : I₀ ⊆ I) (hI₀3 : 3 ≤ I₀.card)
    (hI₀w : ∀ i ∈ I₀, ∀ j ∈ I₀, w i = w j)
    {g : similarityPairs (oQ (diagGL hw))}
    (hy : oκ _ g ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J))) :
    g.val.right = 1 ∧
      signMat K J * (g.val.left : Matrix (Fin d) (Fin d) K) =
        (g.val.left : Matrix (Fin d) (Fin d) K) * signMat K J ∧
      (∀ x ∈ I₀, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0) ∧
      ∀ X : GL (Fin d) K, X ∈ oBlock K hw I →
        (g.val.left : Matrix (Fin d) (Fin d) K) * (X : Matrix (Fin d) (Fin d) K) =
          (X : Matrix (Fin d) (Fin d) K) * (g.val.left : Matrix (Fin d) (Fin d) K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hHeq : matrixDerived (oQ (diagGL hw)) = ⁅CatalogueBGraphForm.isometryGroup d K (diagGL hw),
      CatalogueBGraphForm.isometryGroup d K (diagGL hw)⁆ :=
    matrixDerived_oQ h2 (diagGL hw) (diagGL_transpose hw)
  have hIH : oBlock K hw I ≤ matrixDerived (oQ (diagGL hw)) := by
    rw [hHeq]; exact oBlock_le hw I
  set D := g.val.left with hD
  set τ := g.val.right with hτ
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hτm : τ ^ orderOf (oκ _ g) = 1 := hker.right_pow_eq_one (pow_orderOf_eq_one _)
  have hfix' : ∀ X : GL (Fin d) K, X ∈ oBlock K hw I →
      (D : Matrix (Fin d) (Fin d) K) * (X : Matrix (Fin d) (Fin d) K).map τ *
        ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = X :=
    fun X hX => block_fix_gen hK hw hinj hB hI hI3 hIexc hy (X := ⟨X, hIH hX⟩) hX
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
  have hd0 : 0 < d := by
    have := I.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  have hDS' : signMat K J * (D : Matrix (Fin d) (Fin d) K) = (D : Matrix (Fin d) (Fin d) K) *
      signMat K J := commute_sign_of_odd h2 hw hd0 hker J hodd
        (mem_centralizer_singleton_iff.1 (mem_of_mem_oddCoreIn hy).2)
  refine ⟨hτ1, hDS', fun x hx y hyx => ⟨hiso₀ x y (Ne.symm hyx) (Or.inl hx),
    hiso₀ y x hyx (Or.inr hx)⟩, fun X hX => ?_⟩
  have e := hfix' X hX
  rw [hτ1, show (X : Matrix (Fin d) (Fin d) K).map ⇑(1 : K ≃+* K) = X from by ext; rfl] at e
  have eG : D * X * D⁻¹ = X := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact e)
  have eG' : D * X = X * D := by
    calc D * X = D * X * D⁻¹ * D := by group
      _ = X * D := by rw [eG]
  rw [← Units.val_mul, ← Units.val_mul, eG']

end CFSG.ComponentClassification.Burgoyne.O

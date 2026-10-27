module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenMix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenSplit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd diagGL coe_diagGL signMat
  commute_signMat_iff commute_compInd_iff)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem iso_of_mix (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    {J : Finset (Fin d)} {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ) (hI3 : 3 ≤ I.card)
    {I₀ : Finset (Fin d)} (hI₀ : I₀ ⊆ I) (hI₀3 : 3 ≤ I₀.card)
    (hI₀w : ∀ i ∈ I₀, ∀ j ∈ I₀, w i = w j)
    (hns : ∀ x ∈ I, x ∉ I₀ → ∀ b ∈ I₀, ¬ IsSquare (w x / w b))
    {g : similarityPairs (oQ (diagGL hw))}
    (hy : oκ _ g ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J))) :
    g.val.right = 1 ∧
      signMat K J * (g.val.left : Matrix (Fin d) (Fin d) K) =
        (g.val.left : Matrix (Fin d) (Fin d) K) * signMat K J ∧
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hIexc : ¬ (Nat.card K = 3 ∧ I.card ≤ 4) := fun h => by omega
  obtain ⟨hτ, hDS, hiso₀, hfix⟩ := split_core_gen hK hw hker hinj hB hI hI3 hIexc hI₀ hI₀3 hI₀w hy
  set D := (g.val.left : Matrix (Fin d) (Fin d) K) with hD
  obtain ⟨b₀, hb₀⟩ := Finset.card_pos.1 (by omega : 0 < I₀.card)
  have hcol : ∀ x ∈ I, ∀ y, y ≠ x → D y x = 0 := by
    intro x hx y hyx
    by_cases hx₀ : x ∈ I₀
    · exact (hiso₀ x hx₀ y hyx).2
    have hbx : b₀ ≠ x := fun h => hx₀ (h ▸ hb₀)
    obtain ⟨l, m, hl, hm, hlm⟩ := exists_mix h2 hK5 (hns x hx hx₀ b₀ hb₀)
    have hcirc : w b₀ * l ^ 2 + w x * m ^ 2 = w b₀ := by
      have e : w x = w b₀ * (w x / w b₀) := by field_simp [hw b₀]
      rw [e]
      linear_combination w b₀ * hlm
    exact (col_eq_of_mix h2 hw hfix (hI₀ hb₀) hx hbx (fun z hz => (hiso₀ b₀ hb₀ z hz).symm) hl hm
      hcirc).1 y hyx
  have hblock := (commute_compInd_iff J _).1 ((commute_signMat_iff h2 J _).1 hDS)
  have hsep : ∀ x ∈ I, ∀ y ∉ I, (x ∈ J ↔ y ∉ J) ∧ (y ∈ J ↔ x ∉ J) := by
    intro x hxI y hyI
    rcases hI with hIJ | hIJ
    · rw [hIJ] at hxI hyI
      exact ⟨⟨fun _ => hyI, fun _ => hxI⟩, ⟨fun h => absurd h hyI, fun h => absurd hxI h⟩⟩
    · rw [hIJ, Finset.mem_compl] at hxI
      rw [hIJ, Finset.mem_compl, not_not] at hyI
      exact ⟨⟨fun h => absurd h hxI, fun h => absurd hyI h⟩, ⟨fun _ => hxI, fun _ => hyI⟩⟩
  refine ⟨hτ, hDS, fun x hx y hyx => ⟨?_, hcol x hx y hyx⟩⟩
  by_cases hyI : y ∈ I
  · exact hcol y hyI x (Ne.symm hyx)
  · exact hblock x y (hsep x hx y hyI).1

theorem exists_oIsoBlock_of_iso (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hker : OKer (oQ (diagGL hw)))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} (hJc : Jᶜ.Nonempty) {g : similarityPairs (oQ (diagGL hw))}
    (hy : oκ _ g ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hτ : g.val.right = 1)
    (hiso : ∀ x ∈ Jᶜ, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
      (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0) :
    ∃ (R : GL (Fin d) K) (hR : R ∈ matrixIsometries (oQ (diagGL hw))),
      R ∈ oIsoBlock K hw J ∧ oκ _ g = oκ _ (linPair R hR) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 _ (diagGL_transpose hw) g.val).1 g.2
  rw [hτ, coe_diagGL] at hμ
  rw [show (diagonal w).map ⇑(1 : K ≃+* K) = diagonal w from by ext; rfl] at hμ
  set D := (g.val.left : Matrix (Fin d) (Fin d) K) with hD
  have hsq : ∀ x ∈ Jᶜ, D x x * D x x = μ := by
    intro x hx
    have e := congrFun (congrFun hμ x) x
    rw [Matrix.mul_apply, Finset.sum_eq_single x (fun k _ hk => by
      rw [(hiso x hx k hk).2, mul_zero]) (by simp), Matrix.mul_apply,
      Finset.sum_eq_single x (fun l _ hl => by rw [transpose_apply, (hiso x hx l hl).2,
        zero_mul]) (by simp), transpose_apply, diagonal_apply_eq, Matrix.smul_apply,
      diagonal_apply_eq, smul_eq_mul] at e
    have : w x * (D x x * D x x - μ) = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (hw x))
  have hm := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨-, c, hc⟩ := hker _ (by rw [map_pow]; exact pow_orderOf_eq_one (oκ _ g))
  obtain ⟨hlm, -⟩ := pow_left_of_right_eq_one hτ (orderOf (oκ _ g))
  have hpow : ∀ x ∈ Jᶜ, D x x ^ orderOf (oκ _ g) = c := by
    intro x hx
    have e := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K) x x) hc
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at e
    rw [e, hlm, Units.val_pow_eq_pow_val]
    exact (pow_apply_diag_of_col (fun k hk => (hiso x hx k hk).2) _).symm
  obtain ⟨x₀, hx₀⟩ := hJc
  have hD0 : D x₀ x₀ ≠ 0 := by
    intro h0
    have := hsq x₀ hx₀
    rw [h0, zero_mul] at this
    exact μ.ne_zero this.symm
  have hconst : ∀ x ∈ Jᶜ, D x x = D x₀ x₀ := by
    intro x hx
    have e1 : D x x * D x x = D x₀ x₀ * D x₀ x₀ := by rw [hsq x hx, hsq x₀ hx₀]
    rcases mul_self_eq_mul_self_iff.1 e1 with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hm
      have e2 := (hpow x hx).trans (hpow x₀ hx₀).symm
      rw [h, hk, Odd.neg_pow ⟨k, rfl⟩] at e2
      have : (2 : K) * D x₀ x₀ ^ (2 * k + 1) = 0 := by linear_combination -e2
      exact pow_ne_zero _ hD0 ((mul_eq_zero.1 this).resolve_left h2)
  set b : Kˣ := Units.mk0 _ hD0 with hb
  set R : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) b⁻¹ * g.val.left with hRdef
  have hRm : (R : Matrix (Fin d) (Fin d) K) = (D x₀ x₀)⁻¹ • D := by
    rw [hRdef, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hRI : R ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) := by
    rw [CatalogueBGraphForm.mem_isometryGroup, hRm, coe_diagGL, transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, hμ, smul_smul, smul_smul, ← hsq x₀ hx₀]
    rw [show (D x₀ x₀)⁻¹ * (D x₀ x₀)⁻¹ * (D x₀ x₀ * D x₀ x₀) = 1 by field_simp, one_smul]
  have hR : R ∈ matrixIsometries (oQ (diagGL hw)) :=
    (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) _).2 hRI
  refine ⟨R, hR, (mem_oIsoBlock_iff hw).2 ⟨hRI, fun x y hxy => ?_⟩, ?_⟩
  · rw [hRm, Matrix.smul_apply, smul_eq_mul]
    by_cases hxy' : x = y
    · subst hxy'
      have hx : x ∈ Jᶜ := by
        rcases hxy with h | h <;> exact Finset.mem_compl.2 h
      simp only [↓reduceIte]
      rw [hconst x hx, inv_mul_cancel₀ hD0]
    · simp only [hxy', ↓reduceIte]
      rcases hxy with hx | hy'
      · rw [(hiso x (Finset.mem_compl.2 hx) y (Ne.symm hxy')).1, mul_zero]
      · rw [(hiso y (Finset.mem_compl.2 hy') x hxy').2, mul_zero]
  · refine oκ_eq_of_left_eq (c := b) (by rw [hτ]; rfl) ?_
    rw [linPair_left, hRdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem eq_one_of_iso (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} {g : similarityPairs (oQ (diagGL hw))}
    (hy : oκ _ g ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hτ : g.val.right = 1)
    (hdiag : ∀ x y, x ≠ y → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0) :
    oκ _ g = 1 :=
  eq_one_of_odd_of_sq (odd_orderOf_of_mem_oddCoreIn hy)
    (kappa_sq_eq_one_of_diag (Ring.two_ne_zero hK) hw hτ hdiag)

end CFSG.ComponentClassification.Burgoyne.O

module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSurjCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd commute_compInd_iff diagGL coe_diagGL
  signMat commute_signMat_iff mem_of_mem_oddCoreIn)

variable {K : Type} [Field K] {d : ℕ}

theorem oκ_eq_of_left_eq {Q : QuadraticForm K (Fin d → K)} {g g' : similarityPairs Q}
    (hr : g.val.right = g'.val.right) {c : Kˣ}
    (hl : g.val.left = GeneralLinearGroup.scalar (Fin d) c * g'.val.left) : oκ Q g = oκ Q g' := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨X, rfl⟩ := projH_surjective x
  rw [kappa_proj, kappa_proj]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_val, matrixDerivedConjugation_val, hl, hr]
  have hc : ∀ M : GL (Fin d) K, GeneralLinearGroup.scalar (Fin d) c * M *
      (GeneralLinearGroup.scalar (Fin d) c)⁻¹ = M := fun M => by
    rw [← (commute_scalar c M).eq, mul_inv_cancel_right]
  calc GeneralLinearGroup.scalar (Fin d) c * g'.val.left *
        glFieldAut (Fin d) K g'.val.right X * (GeneralLinearGroup.scalar (Fin d) c *
          g'.val.left)⁻¹ =
      GeneralLinearGroup.scalar (Fin d) c * (g'.val.left * glFieldAut (Fin d) K g'.val.right X *
        g'.val.left⁻¹) * (GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by group
    _ = _ := hc _

theorem pow_left_of_right_eq_one {Q : QuadraticForm K (Fin d → K)} {g : similarityPairs Q}
    (hg : g.val.right = 1) (m : ℕ) : (g ^ m).val.left = g.val.left ^ m ∧ (g ^ m).val.right = 1 := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    rw [pow_succ]
    change (g ^ m * g).val.left = _ ∧ (g ^ m * g).val.right = 1
    rw [Subgroup.coe_mul, SemidirectProduct.mul_left, SemidirectProduct.mul_right, ih.1, ih.2,
      hg, map_one, MulAut.one_apply, pow_succ, mul_one]
    exact ⟨rfl, rfl⟩

theorem kappa_sq_eq_one_of_diag (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {g : similarityPairs (oQ (diagGL hw))} (hg : g.val.right = 1)
    (hdiag : ∀ x y, x ≠ y → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0) :
    oκ _ g ^ 2 = 1 := by
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 _ (diagGL_transpose hw) g.val).1 g.2
  rw [hg, coe_diagGL] at hμ
  rw [show (diagonal w).map ⇑(1 : K ≃+* K) = diagonal w from by ext; rfl] at hμ
  set D := (g.val.left : Matrix (Fin d) (Fin d) K) with hD
  have hDd : D = diagonal fun x => D x x := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq]
    · rw [hdiag x y hxy, diagonal_apply_ne _ hxy]
  have hsq : ∀ x, D x x * D x x = μ := by
    intro x
    have e := congrFun (congrFun hμ x) x
    rw [hDd, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_apply_eq,
      Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul] at e
    have : w x * (D x x * D x x - μ) = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (hw x))
  obtain ⟨hl2, hr2⟩ := pow_left_of_right_eq_one hg 2
  rw [← map_pow]
  have e : oκ _ (g ^ 2) = oκ _ (1 : similarityPairs (oQ (diagGL hw))) := by
    refine oκ_eq_of_left_eq (c := μ) (by rw [hr2]; rfl) ?_
    rw [hl2]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul, GeneralLinearGroup.coe_scalar]
    change D ^ 2 = Matrix.scalar (Fin d) (μ : K) * 1
    rw [Matrix.mul_one, Matrix.scalar_apply, pow_two, hDd, diagonal_mul_diagonal]
    congr 1
    ext x
    exact hsq x
  rw [e, map_one]

theorem eq_one_of_odd_of_sq {G : Type*} [Group G] {y : G} (hodd : Odd (orderOf y))
    (hy : y ^ 2 = 1) : y = 1 := by
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with e | e
  · exact orderOf_eq_one_iff.1 e
  · rw [e] at hodd
    exact absurd hodd (by decide)

variable (K) in
@[expose] def BlockOK (w : Fin d → K) (I : Finset (Fin d)) : Prop :=
  3 ≤ I.card ∧ ¬ (Nat.card K = 3 ∧ I.card ≤ 4) ∧ ∃ I₀ ⊆ I, 3 ≤ I₀.card ∧
    (∀ i ∈ I₀, ∀ j ∈ I₀, w i = w j) ∧ ∀ x ∈ I, ∀ y ∈ I, x ∉ I₀ → y ∉ I₀ → x = y

theorem pow_apply_diag_of_col {D : Matrix (Fin d) (Fin d) K} {x : Fin d}
    (hc : ∀ k, k ≠ x → D k x = 0) (m : ℕ) : (D ^ m) x x = D x x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single x (fun k _ hk => by rw [hc k hk,
      mul_zero]) (by simp), ih, pow_succ]

variable [Finite K]

theorem split_oddCoreIn_eq_bot (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hJd : 2 * J.card ≠ d)
    (hJ : BlockOK K w J ∨ J.card ≤ 1) (hJc : BlockOK K w Jᶜ ∨ Jᶜ.card ≤ 1)
    (hone : BlockOK K w J ∨ BlockOK K w Jᶜ) :
    oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  obtain ⟨g, rfl⟩ := hsurj y hy
  have hcore : ∀ I, (I = J ∨ I = Jᶜ) → BlockOK K w I → g.val.right = 1 ∧
      signMat K J * (g.val.left : Matrix (Fin d) (Fin d) K) =
        (g.val.left : Matrix (Fin d) (Fin d) K) * signMat K J ∧
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0 := by
    rintro I hI ⟨hI3, hIexc, I₀, hI₀, hI₀3, hI₀w, hI₀c⟩
    exact split_core hK hw hker hinj hB hJd hI hI3 hIexc hI₀ hI₀3 hI₀w hI₀c hy
  obtain ⟨hτ, hDS, -⟩ : g.val.right = 1 ∧
      signMat K J * (g.val.left : Matrix (Fin d) (Fin d) K) =
        (g.val.left : Matrix (Fin d) (Fin d) K) * signMat K J ∧ True := by
    rcases hone with h | h
    · obtain ⟨a, b, -⟩ := hcore J (Or.inl rfl) h
      exact ⟨a, b, trivial⟩
    · obtain ⟨a, b, -⟩ := hcore Jᶜ (Or.inr rfl) h
      exact ⟨a, b, trivial⟩
  have hblock := (commute_compInd_iff J _).1 ((commute_signMat_iff h2 J _).1 hDS)
  have hisoI : ∀ I, (I = J ∨ I = Jᶜ) → (BlockOK K w I ∨ I.card ≤ 1) → ∀ x ∈ I, ∀ y, y ≠ x →
      (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0 := by
    intro I hI hIok x hx y hyx
    rcases hIok with hok | hle
    · exact (hcore I hI hok).2.2 x hx y hyx
    · have hyI : y ∉ I := by
        intro hyI
        exact hyx (Finset.card_le_one.1 hle y hyI x hx)
      have hsep : (x ∈ J ↔ y ∉ J) ∧ (y ∈ J ↔ x ∉ J) := by
        rcases hI with rfl | rfl
        · exact ⟨⟨fun _ => hyI, fun _ => hx⟩, ⟨fun h => absurd h hyI, fun h => absurd hx h⟩⟩
        · rw [Finset.mem_compl] at hx
          rw [Finset.mem_compl, not_not] at hyI
          exact ⟨⟨fun h => absurd h hx, fun h => absurd hyI h⟩, ⟨fun _ => hx, fun _ => hyI⟩⟩
      exact ⟨hblock x y hsep.1, hblock y x hsep.2⟩
  have hdiag : ∀ x y, x ≠ y → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 := by
    intro x y hxy
    by_cases hx : x ∈ J
    · exact (hisoI J (Or.inl rfl) hJ x hx y (Ne.symm hxy)).1
    · exact (hisoI Jᶜ (Or.inr rfl) hJc x (Finset.mem_compl.2 hx) y (Ne.symm hxy)).1
  exact eq_one_of_odd_of_sq (odd_orderOf_of_mem_oddCoreIn hy)
    (kappa_sq_eq_one_of_diag h2 hw hτ hdiag)

theorem split_two_oddCoreIn (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hJd : 2 * J.card ≠ d) (hJc : BlockOK K w Jᶜ)
    {y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hy : y ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J))) :
    ∃ (R : GL (Fin d) K) (hR : R ∈ matrixIsometries (oQ (diagGL hw))),
      R ∈ oIsoBlock K hw J ∧ y = oκ _ (linPair R hR) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨g, rfl⟩ := hsurj y hy
  obtain ⟨hI3, hIexc, I₀, hI₀, hI₀3, hI₀w, hI₀c⟩ := hJc
  obtain ⟨hτ, hDS, hiso⟩ := split_core hK hw hker hinj hB hJd (Or.inr rfl) hI3 hIexc hI₀ hI₀3
    hI₀w hI₀c hy
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 _ (diagGL_transpose hw) g.val).1 g.2
  rw [hτ, coe_diagGL] at hμ
  rw [show (diagonal w).map ⇑(1 : K ≃+* K) = diagonal w from by ext; rfl] at hμ
  set D := (g.val.left : Matrix (Fin d) (Fin d) K) with hD
  have hblock := (commute_compInd_iff J _).1 ((commute_signMat_iff h2 J _).1 hDS)
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
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ Jᶜ := Finset.card_pos.1 (by omega)
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

end CFSG.ComponentClassification.Burgoyne.O

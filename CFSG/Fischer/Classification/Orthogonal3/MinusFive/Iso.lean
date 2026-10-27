module

public import CFSG.Fischer.Classification.Orthogonal3.MinusFive.Data
public import CFSG.Fischer.Classification.Orthogonal2.Pair
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace MinusFive

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Fischer.Classification.Orth2
open CFSG.Fischer.Classification.Beta CFSG.Fischer CFSG.Fischer.Classification.F3

@[expose] noncomputable def betaM : LinearMap.BilinForm (ZMod 2) (Fin (2 * 3) → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5 +
      x 0 * y 2 + x 2 * y 3 + x 3 * y 4 + x 4 * y 5 + x 1 * y 3)
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[expose] noncomputable def qMinusSix : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2) :=
  LinearMap.BilinMap.toQuadraticMap betaM

theorem polar_qMinusSix (x y : Fin (2 * 3) → ZMod 2) : polar qMinusSix x y = polM x y :=
  rfl

theorem vec6_eq (x : Fin 6 → ZMod 2) : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
  ext i
  fin_cases i <;> rfl

theorem polar_qMinusSix_nondegenerate :
    ∀ x, (∀ y, QuadraticMap.polar qMinusSix x y = 0) → x = 0 := by
  intro x hx
  rw [vec6_eq x]
  refine polar_nondeg _ _ _ _ _ _ fun a b c d e f => ?_
  have := hx ![a, b, c, d, e, f]
  rwa [polar_qMinusSix, vec6_eq x] at this

theorem polarBilin_qMinusSix_nondegenerate : (polarBilin qMinusSix).Nondegenerate :=
  ⟨fun x hx => polar_qMinusSix_nondegenerate x fun y => by simpa using hx y,
    fun y hy => polar_qMinusSix_nondegenerate y fun x => by
      rw [polar_comm]; simpa using hy x⟩

theorem finrank_six : 5 ≤ finrank (ZMod 2) (Fin (2 * 3) → ZMod 2) := by
  rw [Module.finrank_fin_fun]
  norm_num

theorem qMinusSix_mPt (i : Fin 36) : qMinusSix (mPt i) = 1 :=
  qM_mPt i

@[expose] noncomputable def mElt (i : Fin 36) : reflClass qMinusSix :=
  ⟨reflO qMinusSix (mPt i), mPt i, qMinusSix_mPt i, rfl⟩

theorem coe_mElt (i : Fin 36) :
    (mElt i : TauCeti.QuadraticMap.orthogonalGroup qMinusSix) = reflO qMinusSix (mPt i) :=
  rfl

theorem mPt_mIdx' {x : Fin (2 * 3) → ZMod 2} (hx : qMinusSix x = 1) : mPt (mIdx x) = x := by
  rw [vec6_eq x] at hx ⊢
  exact mPt_mIdx _ _ _ _ _ _ hx

theorem mElt_bijective : Function.Bijective mElt := by
  refine ⟨fun i j hij => ?_, fun q => ?_⟩
  · have h : reflect qMinusSix (mPt i) = reflect qMinusSix (mPt j) :=
      congrArg (fun t : reflClass qMinusSix =>
        ((t : TauCeti.QuadraticMap.orthogonalGroup qMinusSix) :
          (Fin (2 * 3) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * 3) → ZMod 2))) hij
    have := eq_of_reflect_eq polarBilin_qMinusSix_nondegenerate (qMinusSix_mPt i) h
      (qMinusSix_mPt j)
    rw [← mIdx_mPt i, this, mIdx_mPt j]
  · obtain ⟨v, hv, hq⟩ := q.2
    refine ⟨mIdx v, Subtype.ext (Subtype.ext ?_)⟩
    change reflect qMinusSix (mPt (mIdx v)) = _
    rw [mPt_mIdx' hv, hq]

theorem tM_eq (a b : Fin (2 * 3) → ZMod 2) (ha : qMinusSix a = 1) :
    reflect qMinusSix a b = tM a b := by
  rw [reflect_apply_of_map_eq_one ha]
  rfl

theorem mElt_tau (i j : Fin 36) :
    tauE (pair_reflClass polarBilin_qMinusSix_nondegenerate finrank_six) (mElt i) (mElt j) =
      mElt (mIdx (tM (mPt i) (mPt j))) := by
  apply Subtype.ext
  change reflO qMinusSix (mPt i) * reflO qMinusSix (mPt j) * reflO qMinusSix (mPt i) = _
  have hinv : reflO qMinusSix (mPt i) = (reflO qMinusSix (mPt i))⁻¹ :=
    (inv_eq_of_mul_eq_one_right (Subtype.ext (reflect_mul_self qMinusSix (mPt i)))).symm
  conv_lhs => rw [show reflO qMinusSix (mPt i) * reflO qMinusSix (mPt j) *
      reflO qMinusSix (mPt i) = reflO qMinusSix (mPt i) * reflO qMinusSix (mPt j) *
      (reflO qMinusSix (mPt i))⁻¹ by rw [← hinv]]
  rw [conj_reflO, coe_mElt]
  change reflO qMinusSix (reflect qMinusSix (mPt i) (mPt j)) = _
  rw [tM_eq _ _ (qMinusSix_mPt i)]
  have hx : qMinusSix (tM (mPt i) (mPt j)) = 1 := by
    rw [← tM_eq _ _ (qMinusSix_mPt i)]
    rw [map_of_mem (reflect_mem_orthogonalGroup qMinusSix (mPt i)), qMinusSix_mPt j]
  rw [mPt_mIdx' hx]

theorem act_refl_diagF3_five_two {w : Fin 5 → ZMod 3} (hw : diagF3 5 2 w w = 1)
    (v : Fin 5 → ZMod 3) : act (refl (diagF3 5 2) w) v = rQ w v := by
  rw [act_refl hw, diagF3_five_apply, rQ]

theorem qElt_tau (i j : Fin 36) :
    tauE (pair_R3 (isF3Form_diagF3 (by decide)) (by norm_num)) (qElt i) (qElt j) =
      qElt (mIdx (tM (mPt i) (mPt j))) := by
  apply Subtype.ext
  show reflBar (diagF3 5 2) (qPt i) * reflBar (diagF3 5 2) (qPt j) *
    reflBar (diagF3 5 2) (qPt i) = _
  rw [reflBar_conj (isF3Form_diagF3 (by decide)),
    act_refl_diagF3_five_two (by rw [diagF3_five_apply]; exact dot5_qPt i)]
  change _ = reflBar (diagF3 5 2) (qPt (mIdx (tM (mPt i) (mPt j))))
  rcases qPt_mIdx_tM i j with h | h <;> rw [h]
  exact (reflBar_neg _).symm

@[expose] noncomputable def gammaEquiv : reflClass qMinusSix ≃ D3 (diagF3 5 2) :=
  (Equiv.ofBijective mElt mElt_bijective).symm.trans (Equiv.ofBijective qElt qElt_bijective)

theorem gammaEquiv_mElt (i : Fin 36) : gammaEquiv (mElt i) = qElt i := by
  rw [gammaEquiv, Equiv.trans_apply, Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_apply]

theorem gammaEquiv_tau (e f : reflClass qMinusSix) :
    gammaEquiv (tauE (pair_reflClass polarBilin_qMinusSix_nondegenerate finrank_six) e f) =
      tauE (pair_R3 (isF3Form_diagF3 (by decide)) (by norm_num)) (gammaEquiv e)
        (gammaEquiv f) := by
  obtain ⟨i, rfl⟩ := mElt_bijective.2 e
  obtain ⟨j, rfl⟩ := mElt_bijective.2 f
  rw [mElt_tau, gammaEquiv_mElt, gammaEquiv_mElt, gammaEquiv_mElt, qElt_tau]

end MinusFive

open MinusFive

theorem exists_mulEquiv_orthogonalGroup_R3_diagF3_five_two :
    ∃ Φ : R3 (diagF3 5 2) ≃* TauCeti.QuadraticMap.orthogonalGroup qMinusSix,
      Φ '' D3 (diagF3 5 2) = Orth2.reflClass qMinusSix := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_of_tau_eq
    (Orth2.pair_reflClass polarBilin_qMinusSix_nondegenerate finrank_six)
    (pair_R3 (isF3Form_diagF3 (by decide)) (by norm_num))
    (Orth2.center_orthogonalGroup_eq_bot polarBilin_qMinusSix_nondegenerate finrank_six)
    (center_R3_eq_bot (isF3Form_diagF3 (by decide)) (by norm_num)) gammaEquiv gammaEquiv_tau
  refine ⟨ψ.symm, ?_⟩
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨e, he⟩ := gammaEquiv.surjective ⟨p, hp⟩
    have h1 : ψ (e : TauCeti.QuadraticMap.orthogonalGroup qMinusSix) = p := by
      rw [hψ e, he]
    rw [← h1, MulEquiv.symm_apply_apply]
    exact e.2
  · intro hq
    refine ⟨ψ q, ?_, MulEquiv.symm_apply_apply ψ q⟩
    rw [hψ ⟨q, hq⟩]
    exact (gammaEquiv ⟨q, hq⟩).2

end CFSG.Fischer.Classification

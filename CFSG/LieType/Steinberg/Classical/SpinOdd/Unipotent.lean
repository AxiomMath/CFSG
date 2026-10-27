module

public import CFSG.LieType.Steinberg.Classical.SpinOdd.Basic
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Unipotent
public import CFSG.LieType.Steinberg.Classical.OrthogonalRoots
public import CFSG.LieType.Steinberg.Extras

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinOdd

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.Steinberg.Graded CFSG.LieType.RootSystem QuadraticMap Matrix

variable {n : ℕ} {K : Type} [Field K]

@[expose] def oddIdx (m : Fin n) : Bool → Fin n ⊕ Fin n ⊕ Unit
  | true => .inl m
  | false => .inr (.inl m)

@[expose] def zIdx : Fin n ⊕ Fin n ⊕ Unit := .inr (.inr ())

@[expose] def oddWt : Fin n ⊕ Fin n ⊕ Unit → Fin n → ℤ :=
  Sum.elim (fun m => Pi.single m 1) (Sum.elim (fun m => Pi.single m (-1)) fun _ => 0)

theorem oddWt_oddIdx (m : Fin n) (r : Bool) :
    oddWt (oddIdx m r) = Pi.single m (boolSign r) := by
  cases r <;> rfl

theorem oddWt_zIdx : oddWt (zIdx (n := n)) = 0 := rfl

theorem oddIdx_ne_zIdx (m : Fin n) (r : Bool) : oddIdx m r ≠ zIdx := by
  cases r <;> simp [oddIdx, zIdx]

theorem isCoordFrame_oddFrame : IsCoordFrame (oddFrame n K).toHypFrame oddIdx where
  vec_eq m r := by cases r <;> rfl
  polar_eq v m r := by
    cases r
    · exact polar_quadOdd_single_inr_inl n K v m
    · exact polar_quadOdd_single_inl n K v m

variable (K) in
@[expose] def shortMatOne (i : Fin n) (s : Bool) :
    Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K :=
  (boolSign s : K) • (Matrix.single zIdx (oddIdx i (!s)) 1 - Matrix.single (oddIdx i s) zIdx 2)

variable (K) in
@[expose] def shortMatTwo (i : Fin n) (s : Bool) :
    Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K :=
  -Matrix.single (oddIdx i s) (oddIdx i (!s)) 1

theorem coe_spinMatrix_shortRoot (i : Fin n) (s : Bool) (a : K) :
    (spinMatrix (quadOdd n K) ((oddFrame n K).shortRoot i s (.ofAdd a)) :
        Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K) =
      1 + a • (Matrix.single zIdx (oddIdx i (!s)) 1 - Matrix.single (oddIdx i s) zIdx 2) -
        a ^ 2 • Matrix.single (oddIdx i s) (oddIdx i (!s)) 1 := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [spinMatrix_mulVec, OddFrame.spinAction_shortRoot, isCoordFrame_oddFrame.polar_eq,
    isCoordFrame_oddFrame.vec_eq, oddFrame_z, oddZ, polar_quadOdd_single_inr_inr,
    Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq,
    Matrix.single_mulVec_eq]
  simp only [zIdx]
  module

open _root_.Classical in
@[expose] def shortMat₁ (e : Fin n → ℤ) : Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K :=
  if h : ∃ p : Fin n × Bool, e = Pi.single p.1 (boolSign p.2) then
    shortMatOne K h.choose.1 h.choose.2
  else 0

open _root_.Classical in
@[expose] def shortMat₂ (e : Fin n → ℤ) : Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K :=
  if h : ∃ p : Fin n × Bool, e = Pi.single p.1 (boolSign p.2) then
    shortMatTwo K h.choose.1 h.choose.2
  else 0

theorem shortMat₁_eq {e : Fin n → ℤ} {i : Fin n} {s : Bool} (he : e = Pi.single i (boolSign s)) :
    shortMat₁ e = shortMatOne K i s := by
  have hex : ∃ p : Fin n × Bool, e = Pi.single p.1 (boolSign p.2) := ⟨(i, s), he⟩
  rw [shortMat₁, dite_eq_left hex]
  obtain ⟨h1, h2⟩ := eq_of_single_eq_single (hex.choose_spec.symm.trans he)
  rw [h1, h2]

theorem shortMat₂_eq {e : Fin n → ℤ} {i : Fin n} {s : Bool} (he : e = Pi.single i (boolSign s)) :
    shortMat₂ e = shortMatTwo K i s := by
  have hex : ∃ p : Fin n × Bool, e = Pi.single p.1 (boolSign p.2) := ⟨(i, s), he⟩
  rw [shortMat₂, dite_eq_left hex]
  obtain ⟨h1, h2⟩ := eq_of_single_eq_single (hex.choose_spec.symm.trans he)
  rw [h1, h2]

theorem shortMat₁_of_not {e : Fin n → ℤ} (he : ¬IsShort e) : shortMat₁ e = (0 : Matrix _ _ K) := by
  rw [shortMat₁, dite_eq_right fun ⟨p, hp⟩ => he ⟨p.1, p.2, hp⟩]

theorem shortMat₂_of_not {e : Fin n → ℤ} (he : ¬IsShort e) : shortMat₂ e = (0 : Matrix _ _ K) := by
  rw [shortMat₂, dite_eq_right fun ⟨p, hp⟩ => he ⟨p.1, p.2, hp⟩]

theorem coe_spinMatrix_shortElt_of_eq {e : Fin n → ℤ} {i : Fin n} {s : Bool}
    (he : e = Pi.single i (boolSign s)) (c : K) :
    (spinMatrix (quadOdd n K) (shortElt (oddFrame n K) e c) :
        Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K) =
      1 + c • shortMatOne K i s + c ^ 2 • shortMatTwo K i s := by
  rw [shortElt_eq _ he, coe_spinMatrix_shortRoot, shortMatOne, shortMatTwo]
  have hs := intCast_mul_self_of_sq (K := K) (boolSign_eq_one_or_eq_neg_one s)
  have h2 : ((boolSign s : K) * c) ^ 2 = c ^ 2 := by rw [mul_pow, sq (boolSign s : K), hs, one_mul]
  rw [h2]
  module

theorem shifts_shortMatOne (i : Fin n) (s : Bool) :
    Shifts oddWt (shortMatOne K i s) (Pi.single i (boolSign s)) := by
  intro a b hab
  simp only [shortMatOne, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    smul_eq_mul] at hab
  by_cases h1 : zIdx = a ∧ oddIdx i (!s) = b
  · obtain ⟨rfl, rfl⟩ := h1
    rw [oddWt_zIdx, oddWt_oddIdx, boolSign_not, Pi.single_neg, zero_sub, neg_neg]
  · by_cases h2 : oddIdx i s = a ∧ zIdx = b
    · obtain ⟨rfl, rfl⟩ := h2
      rw [oddWt_zIdx, oddWt_oddIdx, sub_zero]
    · rw [ite_eq_right h1, ite_eq_right h2, sub_self, mul_zero] at hab
      exact absurd rfl hab

theorem shifts_shortMatTwo (i : Fin n) (s : Bool) :
    Shifts oddWt (shortMatTwo K i s) (2 • Pi.single i (boolSign s)) := by
  intro a b hab
  simp only [shortMatTwo, Matrix.neg_apply, Matrix.single_apply] at hab
  by_cases h1 : oddIdx i s = a ∧ oddIdx i (!s) = b
  · obtain ⟨rfl, rfl⟩ := h1
    rw [oddWt_oddIdx, oddWt_oddIdx, boolSign_not, Pi.single_neg, sub_neg_eq_add, two_nsmul]
  · rw [ite_eq_right h1, neg_zero] at hab
    exact absurd rfl hab

theorem shortMatOne_ne_zero (i : Fin n) (s : Bool) : shortMatOne K i s ≠ 0 := by
  intro h
  have h' := congrFun (congrFun h zIdx) (oddIdx i (!s))
  simp only [shortMatOne, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, and_self,
    ite_true, Matrix.zero_apply, smul_eq_mul] at h'
  rw [ite_eq_right (fun h => oddIdx_ne_zIdx i s h.1), sub_zero, mul_one] at h'
  exact intCast_ne_zero_of_sq (boolSign_eq_one_or_eq_neg_one s) h'

open _root_.Classical in
@[expose] def xMat (γ : Fin n → ℤ) (k : ℕ) :
    Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K :=
  if IsLong (toStdB n γ) then
    (if k = 1 then rootMat (oddFrame n K).toHypFrame (toStdB n γ) else 0)
  else if k = 1 then shortMat₁ (toStdB n γ) else if k = 2 then shortMat₂ (toStdB n γ) else 0

theorem elt_two_eq (D : ℕ → Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K) (c : K) :
    Graded.elt 2 D c = 1 + c • D 1 + c ^ 2 • D 2 := by
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [Graded.elt, hIcc, Finset.sum_pair (by decide), pow_one, add_assoc]

theorem coe_spinMatrix_x (γ : Fin n → ℤ) (c : K) :
    (spinMatrix (quadOdd n K) (x n K γ c) :
        Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K) = Graded.elt 2 (xMat γ) c := by
  rw [elt_two_eq]
  by_cases hl : IsLong (toStdB n γ)
  · simp only [xMat, ite_eq_left hl, ite_true, ite_eq_right (show (2 : ℕ) ≠ 1 by decide),
      smul_zero, add_zero]
    rw [x, elt_of_isLong _ hl, coe_spinMatrix_rootElt isCoordFrame_oddFrame]
  · by_cases hs : IsShort (toStdB n γ)
    · obtain ⟨i, s, he⟩ := hs
      simp only [xMat, ite_eq_right hl, ite_true, ite_eq_right (show (2 : ℕ) ≠ 1 by decide)]
      rw [x, elt_of_isShort _ (he ▸ isShort_single i s), shortMat₁_eq he, shortMat₂_eq he,
        coe_spinMatrix_shortElt_of_eq he]
    · simp only [xMat, ite_eq_right hl, ite_true, ite_eq_right (show (2 : ℕ) ≠ 1 by decide),
        shortMat₁_of_not hs, shortMat₂_of_not hs, smul_zero, add_zero]
      rw [x, elt_of_not _ (fun h => h.elim hl hs), map_one, Units.val_one]

theorem shifts_xMat (γ : Fin n → ℤ) (k : ℕ) (hk : 1 ≤ k) :
    Shifts oddWt (xMat (K := K) γ k) (k • toStdB n γ) := by
  have hzero : ∀ δ : Fin n → ℤ, Shifts oddWt (0 : Matrix (Fin n ⊕ Fin n ⊕ Unit)
      (Fin n ⊕ Fin n ⊕ Unit) K) δ := fun δ a b hab => absurd rfl hab
  by_cases hl : IsLong (toStdB n γ)
  · simp only [xMat, ite_eq_left hl]
    split_ifs with h1
    · subst h1
      rw [one_nsmul]
      exact shifts_rootMat isCoordFrame_oddFrame oddWt oddWt_oddIdx _
    · exact hzero _
  · simp only [xMat, ite_eq_right hl]
    by_cases hs : IsShort (toStdB n γ)
    · obtain ⟨i, s, he⟩ := hs
      split_ifs with h1 h2
      · subst h1
        rw [one_nsmul, shortMat₁_eq he, he]
        exact shifts_shortMatOne i s
      · subst h2
        rw [shortMat₂_eq he, he]
        exact shifts_shortMatTwo i s
      · exact hzero _
    · rw [shortMat₁_of_not hs, shortMat₂_of_not hs]
      split_ifs <;> exact hzero _

theorem xMat_one_ne_zero {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) :
    xMat (K := K) γ 1 ≠ 0 := by
  rcases mem_roots_iff.mp hγ with hl | ⟨i, s, he⟩
  · simp only [xMat, ite_eq_left hl, ite_true]
    exact rootMat_ne_zero isCoordFrame_oddFrame hl
  · simp only [xMat, ite_eq_right (he ▸ isShort_single i s).not_isLong, ite_true]
    rw [shortMat₁_eq he]
    exact shortMatOne_ne_zero i s

theorem prodInjective (f : (Fin n → ℤ) →+ ℤ) (L : List (Fin n → ℤ)) (hL : L.Nodup)
    (hpos : ∀ γ ∈ L, γ ∈ roots (isFiniteType_cartanB n) ∅ ∧ 0 < f γ)
    (hsort : L.Pairwise fun γ δ => f γ ≤ f δ) :
    ProdInjectiveFor (oddRootGroup n K) L := by
  intro g g' hg hg' hgg
  obtain ⟨μ, hμ⟩ := exists_levelFun (Orthogonal.toStdBHom n) Orthogonal.toStdBHom_injective 1
    (fun a => ⟨ofStdB n (Pi.single a 1), by rw [one_smul]; exact toStdB_ofStdB n _⟩) f
  have hlev : ∀ γ, μ (toStdB n γ) = f γ := fun γ => by
    rw [← one_mul (f γ)]
    exact hμ γ
  have hcoef : ∀ e : (Fin n → ℤ) → spinGroup (quadOdd n K),
      (∀ γ ∈ L, e γ ∈ oddRootGroup n K γ) →
        ∃ c : (Fin n → ℤ) → K, ∀ γ ∈ L, x n K γ (c γ) = e γ := by
    intro e he
    have : ∀ γ, ∃ c : K, γ ∈ L → x n K γ c = e γ := by
      intro γ
      by_cases hγ : γ ∈ L
      · obtain ⟨c, hc⟩ := (((isParametrization (n := n) (K := K)) γ (hpos γ hγ).1).1
          (e γ)).mp (he γ hγ)
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h hγ⟩
    choose c hc using this
    exact ⟨c, fun γ hγ => hc γ hγ⟩
  obtain ⟨c, hc⟩ := hcoef g hg
  obtain ⟨d, hd⟩ := hcoef g' hg'
  have hprod : ∀ (e : (Fin n → ℤ) → spinGroup (quadOdd n K)) (c' : (Fin n → ℤ) → K),
      (∀ γ ∈ L, x n K γ (c' γ) = e γ) → (L.map e).prod = (L.map fun γ => x n K γ (c' γ)).prod :=
    fun e c' he => congrArg List.prod (List.map_congr_left fun γ hγ => (he γ hγ).symm)
  have hmat : ∀ c' : (Fin n → ℤ) → K,
      ((spinMatrix (quadOdd n K) (L.map fun γ => x n K γ (c' γ)).prod :
        GL (Fin n ⊕ Fin n ⊕ Unit) K) : Matrix (Fin n ⊕ Fin n ⊕ Unit) (Fin n ⊕ Fin n ⊕ Unit) K) =
        (L.map fun γ => Graded.elt 2 (xMat γ) (c' γ)).prod := by
    intro c'
    rw [map_list_prod, ← Units.coeHom_apply, map_list_prod, List.map_map, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun γ _ => coe_spinMatrix_x γ (c' γ))
  have hcd := Graded.eq_of_prod_eq (wt := oddWt) (by norm_num : 1 ≤ 2) (toStdB n) xMat μ
    (fun γ k hk => shifts_xMat γ k hk) L hL (fun γ _ δ _ h => toStdB_injective n h)
    (fun γ hγ => by rw [hlev]; exact (hpos γ hγ).2)
    (fun γ hγ => xMat_one_ne_zero (hpos γ hγ).1)
    (hsort.imp fun {γ δ} h => by rw [hlev, hlev]; exact h)
    (fun γ _ e => by rw [← coe_spinMatrix_x]; exact Units.isUnit _) c d
    (by rw [← hmat, ← hmat, ← hprod g c hc, ← hprod g' d hd, hgg])
  intro γ hγ
  rw [← hc γ hγ, ← hd γ hγ, hcd γ hγ]

end CFSG.LieType.Steinberg.SpinOdd

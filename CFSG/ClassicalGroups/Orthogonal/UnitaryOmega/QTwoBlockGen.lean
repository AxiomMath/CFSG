module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.QTwoRootBlocks
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {ω : K} (hω : IsTraceNormOne E ω)

section CastEichler

variable {k m : ℕ}

private noncomputable def qTwoFill (_h : k ≤ m) (v : (F × F) × (Fin k → K)) :
    (F × F) × (Fin m → K) :=
  (v.1, fun j => if hj : (j : ℕ) < k then v.2 ⟨(j : ℕ), hj⟩ else 0)

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem qTwoFill_add (h : k ≤ m) (u v : (F × F) × (Fin k → K)) :
    qTwoFill h (u + v) = qTwoFill h u + qTwoFill h v := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : (j : ℕ) < k <;> simp [qTwoFill, hj]

omit [Finite K] [CharP K 2] in
private theorem qTwoFill_smul (h : k ≤ m) (c : F) (v : (F × F) × (Fin k → K)) :
    qTwoFill h (c • v) = c • qTwoFill h v := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : (j : ℕ) < k <;> simp [qTwoFill, hj]

omit [Field F] [Algebra F K] [Finite K] [CharP K 2] in
private theorem castRestr_qTwoFill (h : k ≤ m) (v : (F × F) × (Fin k → K)) :
    castRestr h (qTwoFill h v) = v := by
  refine Prod.ext rfl (funext fun i => ?_)
  simp [castRestr, qTwoFill]

omit [Field F] [Algebra F K] [Finite K] [CharP K 2] in
private theorem qTwoFill_castRestr (h : k ≤ m) (v : (F × F) × (Fin m → K))
    (hv : ∀ j : Fin m, k ≤ (j : ℕ) → v.2 j = 0) :
    qTwoFill h (castRestr h v) = v := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp [castRestr, qTwoFill, hj]
  · have hjk : k ≤ (j : ℕ) := by omega
    simp [castRestr, qTwoFill, hj, hv j hjk]

private theorem normHypForm_qTwoFill (h : k ≤ m) (v : (F × F) × (Fin k → K)) :
    normHypForm E m (qTwoFill h v) = normHypForm E k v := by
  rw [normHypForm_eq_castRestr_add (E := E) h (qTwoFill h v), castRestr_qTwoFill]
  have hzero : (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k),
      normQuad E ((qTwoFill h v).2 j)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_filter] at hj
    simp [qTwoFill, hj.2]
  rw [hzero, add_zero]

private theorem polar_normHypForm_qTwoFill (h : k ≤ m) (u w : (F × F) × (Fin k → K)) :
    polar (normHypForm E m) (qTwoFill h u) (qTwoFill h w) =
      polar (normHypForm E k) u w := by
  rw [show polar (normHypForm E m) (qTwoFill h u) (qTwoFill h w) =
      normHypForm E m (qTwoFill h u + qTwoFill h w) - normHypForm E m (qTwoFill h u) -
        normHypForm E m (qTwoFill h w) from rfl,
    show polar (normHypForm E k) u w =
      normHypForm E k (u + w) - normHypForm E k u - normHypForm E k w from rfl,
    ← qTwoFill_add, normHypForm_qTwoFill, normHypForm_qTwoFill, normHypForm_qTwoFill]

private theorem polar_normHypForm_eq (h : k ≤ m) (x : (F × F) × (Fin m → K))
    (u : (F × F) × (Fin k → K)) :
    polar (normHypForm E m) x (qTwoFill h u) =
      polar (normHypForm E k) (castRestr h x) u := by
  set t : (F × F) × (Fin m → K) := x - qTwoFill h (castRestr h x) with ht
  have ht1 : t.1 = 0 := by
    rw [ht]
    change x.1 - (castRestr h x).1 = 0
    rw [show (castRestr h x).1 = x.1 from rfl]
    exact sub_self _
  have ht2 : ∀ j : Fin m, (j : ℕ) < k → t.2 j = 0 := by
    intro j hj
    simp [ht, qTwoFill, castRestr, hj]
  have hpolar : polar (normHypForm E m) t (qTwoFill h u) = 0 := by
    rw [normHypForm, polar_hypSum, polar_Qn]
    have h1 : t.1.1 * (qTwoFill h u).1.2 = 0 := by rw [ht1]; simp
    have h2 : (qTwoFill h u).1.1 * t.1.2 = 0 := by rw [ht1]; simp
    have h3 : (∑ j, polar (normQuad E) (t.2 j) ((qTwoFill h u).2 j)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (j : ℕ) < k
      · rw [ht2 j hj, polar_zero_left]
      · have h0 : (qTwoFill h u).2 j = 0 := by simp [qTwoFill, hj]
        rw [h0, polar_zero_right]
    rw [h1, h2, h3, add_zero, add_zero]
  have hx : x = qTwoFill h (castRestr h x) + t := by
    rw [ht]
    abel
  conv_lhs => rw [hx]
  rw [polar_add_left, polar_normHypForm_qTwoFill, hpolar, add_zero]

private theorem castLin_eichlerLin (h : k ≤ m) (u w : (F × F) × (Fin k → K))
    (x : (F × F) × (Fin m → K)) :
    castLin h (eichlerLin (normHypForm E k) u w) x =
      x + polar (normHypForm E k) (castRestr h x) u • qTwoFill h w -
        (polar (normHypForm E k) (castRestr h x) w +
          normHypForm E k w * polar (normHypForm E k) (castRestr h x) u) • qTwoFill h u := by
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun j => ?_)
  · rw [castLin_fst (h := h) (g := eichlerLin (normHypForm E k) u w) (v := x),
      eichlerLin_apply]
    simp [castRestr, qTwoFill]
  · rw [show (castLin h (eichlerLin (normHypForm E k) u w) x).1.2 =
        (eichlerLin (normHypForm E k) u w (castRestr h x)).1.2 from
      congrArg Prod.snd (castLin_fst (h := h) (g := eichlerLin (normHypForm E k) u w)
        (v := x)),
      eichlerLin_apply]
    simp [castRestr, qTwoFill]
  · by_cases hj : (j : ℕ) < k
    · rw [castLin_snd_of_lt (h := h) (g := eichlerLin (normHypForm E k) u w) (v := x) hj,
        eichlerLin_apply]
      have hcast : (Fin.castLE h ⟨(j : ℕ), hj⟩ : Fin m) = j := Fin.ext rfl
      simp [castRestr, qTwoFill, hj, hcast]
    · rw [castLin_snd_of_not_lt (h := h) (g := eichlerLin (normHypForm E k) u w) (v := x) hj]
      simp [qTwoFill, hj]

private theorem castEquiv_one (h : k ≤ m) :
    castEquiv h (1 : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K))) = 1 := by
  refine LinearEquiv.ext fun x => ?_
  rw [castEquiv_apply]
  have hone : ((1 : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K))) :
      ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K))) = LinearMap.id := rfl
  rw [hone, castLin_id]
  rfl

private theorem castEquiv_eichler (h : k ≤ m) (u w : (F × F) × (Fin k → K)) :
    castEquiv h (eichler (normHypForm E k) u w) =
      eichler (normHypForm E m) (qTwoFill h u) (qTwoFill h w) := by
  refine LinearEquiv.ext fun x => ?_
  by_cases hc : normHypForm E k u = 0 ∧ polar (normHypForm E k) u w = 0
  · have hcm : normHypForm E m (qTwoFill h u) = 0 ∧
        polar (normHypForm E m) (qTwoFill h u) (qTwoFill h w) = 0 := by
      rw [normHypForm_qTwoFill, polar_normHypForm_qTwoFill]
      exact hc
    have he : (eichler (normHypForm E k) u w).toLinearMap =
        eichlerLin (normHypForm E k) u w := by
      refine LinearMap.ext fun y => ?_
      change eichler (normHypForm E k) u w y = eichlerLin (normHypForm E k) u w y
      rw [eichler_apply hc.1 hc.2, eichlerLin_apply]
    rw [castEquiv_apply, he, castLin_eichlerLin, eichler_apply hcm.1 hcm.2,
      ← polar_normHypForm_eq, ← polar_normHypForm_eq, normHypForm_qTwoFill]
  · have hcm : ¬ (normHypForm E m (qTwoFill h u) = 0 ∧
        polar (normHypForm E m) (qTwoFill h u) (qTwoFill h w) = 0) := by
      rwa [normHypForm_qTwoFill, polar_normHypForm_qTwoFill]
    rw [eichler_of_not hc, eichler_of_not hcm, castEquiv_one]

end CastEichler

section FrameVectors

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem qTwoFill_qTwoVecTwo (h : 2 ≤ 4) (i : Fin 3) (s : Bool) :
    qTwoFill h (qTwoVecTwo F ω i s) = qTwoVec F ω ⟨i, by omega⟩ s := by
  fin_cases i <;> cases s <;>
    refine Prod.ext rfl (funext fun j => ?_) <;>
    fin_cases j <;> simp [qTwoVec, qTwoVecTwo, qTwoFill, normPlaneVec, normWVec, Pi.single_apply]

private def qTwoIdxW : Fin 3 → Fin 5 := ![2, 0, 1]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem qTwoFill_qTwoVecTwoW (h : 2 ≤ 4) (i : Fin 3) (s : Bool) :
    qTwoFill h (qTwoVecTwoW F ω i s) = qTwoVec F ω (qTwoIdxW i) s := by
  fin_cases i <;> cases s <;>
    refine Prod.ext rfl (funext fun j => ?_) <;>
    fin_cases j <;>
    simp [qTwoVec, qTwoVecTwoW, qTwoFill, qTwoIdxW, normPlaneVec, normWVec, Pi.single_apply]

end FrameVectors

section ElementActions

variable {ω : K} (hω : IsTraceNormOne E ω)

private theorem qTwoW0_mem_orthogonalGroup :
    (qTwoW0 E hω : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 4) :=
  (Subgroup.commutator_le_of_le
    (le_refl (TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 4)))
    (le_refl (TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 4)))) (qTwoW0 E hω).2

private theorem qTwoW0Lin_planeSum (x y : K) :
    qTwoW0Lin E (normPlaneVec F 0 x + normPlaneVec F 1 y) =
      normPlaneVec F 0 x + normPlaneVec F 1 y := by
  rw [map_add, qTwoW0Lin_planeVec E (by decide : (0 : Fin 4) ≠ 2) x,
    qTwoW0Lin_planeVec E (by decide : (1 : Fin 4) ≠ 2) y]

private theorem qTwoW0Lin_qTwoVec_zero_one {i : Fin 5} (hi : (i : ℕ) < 2) (s : Bool) :
    qTwoW0Lin E (qTwoVec F ω i s) = qTwoVec F ω i s := by
  fin_cases i
  · cases s
    · simpa [qTwoVec] using qTwoW0Lin_planeSum E ω 1
    · simpa [qTwoVec] using qTwoW0Lin_planeSum E 1 1
  · cases s
    · simpa [qTwoVec] using qTwoW0Lin_planeSum E (1 + ω) (1 + ω)
    · simpa [qTwoVec] using qTwoW0Lin_planeSum E (1 + ω) ω
  all_goals simp at hi

private theorem qTwoW0Lin_qTwoVec_two (s : Bool) :
    qTwoW0Lin E (qTwoVec F ω 2 s) = qTwoVec F ω 2 (!s) := by
  cases s
  · simpa [qTwoVec] using qTwoW0Lin_wVec E false
  · simpa [qTwoVec] using qTwoW0Lin_wVec E true

end ElementActions

section PlanePerm

private def qTwoPerm : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

private noncomputable def qTwoPermOmega (E : QuadExt F K (unitaryInvolution K 2 f)) :
    normOmega E 4 :=
  normPerm E (by norm_num : 3 ≤ 4) qTwoPerm

private theorem qTwoPerm_zero : qTwoPerm 0 = 3 := by decide

private theorem qTwoPerm_one : qTwoPerm 1 = 2 := by decide

private theorem qTwoPerm_two : qTwoPerm 2 = 1 := by decide

private theorem qTwoPerm_three : qTwoPerm 3 = 0 := by decide

private theorem qTwoPermOmega_apply (v : (F × F) × (Fin 4 → K)) :
    ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) v =
      (v.1, fun j => v.2 (qTwoPerm⁻¹ j)) :=
  normPerm_apply E (by norm_num : 3 ≤ 4) qTwoPerm v

private theorem qTwoPermOmega_planeVec (k : Fin 4) (x : K) :
    ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) (normPlaneVec F k x) =
      normPlaneVec F (qTwoPerm k) x := by
  rw [qTwoPermOmega_apply]
  refine Prod.ext rfl (funext fun j => ?_)
  simp only [normPlaneVec, Pi.single_apply]
  by_cases h : j = qTwoPerm k
  · subst h
    simp
  · have h' : qTwoPerm.symm j ≠ k :=
      fun hk => h ((Equiv.symm_apply_eq qTwoPerm).mp hk)
    simp [h, h']

private theorem qTwoPermOmega_wVec (s : Bool) :
    ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) (normWVec K 4 s) =
      normWVec K 4 s := by
  rw [qTwoPermOmega_apply]
  cases s <;> rfl

private theorem qTwoPermOmega_qTwoVec_zero (s : Bool) :
    ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) (qTwoVec F ω 0 s) =
      qTwoVec F ω 3 s := by
  cases s
  · change ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))
        (normPlaneVec F 0 ω + normPlaneVec F 1 1) =
      normPlaneVec F 3 ω + normPlaneVec F 2 1
    rw [map_add, qTwoPermOmega_planeVec, qTwoPermOmega_planeVec, qTwoPerm_zero, qTwoPerm_one]
  · change ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))
        (normPlaneVec F 0 1 + normPlaneVec F 1 1) =
      normPlaneVec F 3 1 + normPlaneVec F 2 1
    rw [map_add, qTwoPermOmega_planeVec, qTwoPermOmega_planeVec, qTwoPerm_zero, qTwoPerm_one]

private theorem qTwoPermOmega_qTwoVec_one (s : Bool) :
    ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) (qTwoVec F ω 1 s) =
      qTwoVec F ω 4 s := by
  cases s
  · change ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))
        (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω)) =
      normPlaneVec F 3 (1 + ω) + normPlaneVec F 2 (1 + ω)
    rw [map_add, qTwoPermOmega_planeVec, qTwoPermOmega_planeVec, qTwoPerm_zero, qTwoPerm_one]
  · change ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))
        (normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω) =
      normPlaneVec F 3 (1 + ω) + normPlaneVec F 2 ω
    rw [map_add, qTwoPermOmega_planeVec, qTwoPermOmega_planeVec, qTwoPerm_zero, qTwoPerm_one]

private theorem qTwoPermOmega_qTwoVec_two (s : Bool) :
    ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) (qTwoVec F ω 2 s) =
      qTwoVec F ω 2 s := by
  cases s
  · simpa [qTwoVec] using qTwoPermOmega_wVec E false
  · simpa [qTwoVec] using qTwoPermOmega_wVec E true

private theorem qTwoPermOmega_mem_orthogonalGroup :
    ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 4) :=
  (Subgroup.commutator_le_of_le
    (le_refl (TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 4)))
    (le_refl (TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 4)))) (qTwoPermOmega E).2

private theorem normBlock_zero_one_eq_range (h : 2 ≤ 4) :
    normBlock E 4 ({0, 1} : Finset (Fin 4)) = (normOmegaCast E h).range := by
  have hset : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin 4)) = {0, 1} := by
    ext j
    fin_cases j <;> simp
  change normBlock E 4 ({0, 1} : Finset (Fin 4)) = anchorBlock E h
  rw [anchorBlock_eq_normBlock, hset]

private theorem normBlock_two_three_eq_map (h : 2 ≤ 4) :
    normBlock E 4 ({2, 3} : Finset (Fin 4)) =
      (normOmegaCast E h).range.map (MulAut.conj (qTwoPermOmega E)).toMonoidHom := by
  have hset : ((({0, 1} : Finset (Fin 4)).image qTwoPerm) = {2, 3}) := by decide
  rw [← hset, ← map_normBlock_normPerm E (by norm_num : 3 ≤ 4) qTwoPerm {0, 1},
    normBlock_zero_one_eq_range (E := E) h]
  rfl

end PlanePerm

section RootCoefficients

variable {ω : K} (hω : IsTraceNormOne E ω)

private theorem coe_qTwoLambda_symm_rootD (k : Fin 5) (c : F) :
    (((qTwoLambda E hω).symm (rootD F (by norm_num : 3 ≤ 5) k (.ofAdd c)) :
      normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
      eichler (normHypForm E 4) (qTwoVec F ω (rootIdxD' 5 k) (rootSignD 5 k))
        (c • qTwoVec F ω (rootIdxD 5 k) true) :=
  coe_qTwoLambda_symm_longRoot E hω (rootIdxD_ne 5 (by norm_num) k) true
    (rootSignD 5 k) c

private theorem coe_qTwoLambda_symm_negRootD (k : Fin 5) (c : F) :
    (((qTwoLambda E hω).symm (negRootD F (by norm_num : 3 ≤ 5) k (.ofAdd c)) :
      normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
      eichler (normHypForm E 4) (qTwoVec F ω (rootIdxD 5 k) false)
        (c • qTwoVec F ω (rootIdxD' 5 k) (!rootSignD 5 k)) :=
  coe_qTwoLambda_symm_longRoot E hω (rootIdxD_ne 5 (by norm_num) k).symm
    (!rootSignD 5 k) false c

private theorem coe_qTwoLambdaTwo_symm_rootD (k : Fin 3) (c : F) :
    (((qTwoLambdaTwo E hω).symm (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)) :
      normOmega E 2) : ((F × F) × (Fin 2 → K)) ≃ₗ[F] ((F × F) × (Fin 2 → K))) =
      eichler (normHypForm E 2) (qTwoVecTwo F ω (rootIdxD' 3 k) (rootSignD 3 k))
        (c • qTwoVecTwo F ω (rootIdxD 3 k) true) := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  exact (coe_commutatorEquivSpinPlus_symm_longRoot (qTwoFrameTwo hω)
    (finrank_normHypForm E 2) (by norm_num : 3 ≤ 3) CharTwo.two_eq_zero
    (rootIdxD_ne 3 (by norm_num) k) true (rootSignD 3 k) c).trans
    ((qTwoFrameTwo hω).spinAction_longRoot_eq_eichler _ true _ c)

private theorem coe_qTwoLambdaTwo_symm_negRootD (k : Fin 3) (c : F) :
    (((qTwoLambdaTwo E hω).symm (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)) :
      normOmega E 2) : ((F × F) × (Fin 2 → K)) ≃ₗ[F] ((F × F) × (Fin 2 → K))) =
      eichler (normHypForm E 2) (qTwoVecTwo F ω (rootIdxD 3 k) false)
        (c • qTwoVecTwo F ω (rootIdxD' 3 k) (!rootSignD 3 k)) := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  exact (coe_commutatorEquivSpinPlus_symm_longRoot (qTwoFrameTwo hω)
    (finrank_normHypForm E 2) (by norm_num : 3 ≤ 3) CharTwo.two_eq_zero
    (rootIdxD_ne 3 (by norm_num) k).symm (!rootSignD 3 k) false c).trans
    ((qTwoFrameTwo hω).spinAction_longRoot_eq_eichler _ (!rootSignD 3 k) false c)

private theorem coe_qTwoLambdaTwoW_symm_rootD (k : Fin 3) (c : F) :
    (((qTwoLambdaTwoW E hω).symm (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)) :
      normOmega E 2) : ((F × F) × (Fin 2 → K)) ≃ₗ[F] ((F × F) × (Fin 2 → K))) =
      eichler (normHypForm E 2) (qTwoVecTwoW F ω (rootIdxD' 3 k) (rootSignD 3 k))
        (c • qTwoVecTwoW F ω (rootIdxD 3 k) true) := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  exact (coe_commutatorEquivSpinPlus_symm_longRoot (qTwoFrameTwoW hω)
    (finrank_normHypForm E 2) (by norm_num : 3 ≤ 3) CharTwo.two_eq_zero
    (rootIdxD_ne 3 (by norm_num) k) true (rootSignD 3 k) c).trans
    ((qTwoFrameTwoW hω).spinAction_longRoot_eq_eichler _ true _ c)

private theorem coe_qTwoLambdaTwoW_symm_negRootD (k : Fin 3) (c : F) :
    (((qTwoLambdaTwoW E hω).symm (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)) :
      normOmega E 2) : ((F × F) × (Fin 2 → K)) ≃ₗ[F] ((F × F) × (Fin 2 → K))) =
      eichler (normHypForm E 2) (qTwoVecTwoW F ω (rootIdxD 3 k) false)
        (c • qTwoVecTwoW F ω (rootIdxD' 3 k) (!rootSignD 3 k)) := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  exact (coe_commutatorEquivSpinPlus_symm_longRoot (qTwoFrameTwoW hω)
    (finrank_normHypForm E 2) (by norm_num : 3 ≤ 3) CharTwo.two_eq_zero
    (rootIdxD_ne 3 (by norm_num) k).symm (!rootSignD 3 k) false c).trans
    ((qTwoFrameTwoW hω).spinAction_longRoot_eq_eichler _ (!rootSignD 3 k) false c)

end RootCoefficients

section CastRoots

private theorem cast_qTwoLambdaTwo_symm_rootD_zero_one {k : Fin 3} (hk : (k : ℕ) < 2) (c : F) :
    normOmegaCast E (by norm_num : 2 ≤ 4)
        ((qTwoLambdaTwo E hω).symm (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) =
      (qTwoLambda E hω).symm
        (rootD F (by norm_num : 3 ≤ 5) ⟨k, by omega⟩ (.ofAdd c)) := by
  apply Subtype.ext
  rw [normOmegaCast_apply, coe_qTwoLambdaTwo_symm_rootD, coe_qTwoLambda_symm_rootD]
  fin_cases k
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwo, qTwoFill_smul]
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwo, qTwoFill_smul]
  · simp at hk

private theorem cast_qTwoLambdaTwo_symm_negRootD_zero_one {k : Fin 3} (hk : (k : ℕ) < 2) (c : F) :
    normOmegaCast E (by norm_num : 2 ≤ 4)
        ((qTwoLambdaTwo E hω).symm (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) =
      (qTwoLambda E hω).symm
        (negRootD F (by norm_num : 3 ≤ 5) ⟨k, by omega⟩ (.ofAdd c)) := by
  apply Subtype.ext
  rw [normOmegaCast_apply, coe_qTwoLambdaTwo_symm_negRootD, coe_qTwoLambda_symm_negRootD]
  fin_cases k
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwo, qTwoFill_smul]
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwo, qTwoFill_smul]
  · simp at hk

private theorem cast_qTwoLambdaTwo_symm_rootD_two (c : F) :
    normOmegaCast E (by norm_num : 2 ≤ 4)
        ((qTwoLambdaTwo E hω).symm (rootD F (by norm_num : 3 ≤ 3) 2 (.ofAdd c))) =
      qTwoW0 E hω * (qTwoLambda E hω).symm (rootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c)) *
        (qTwoW0 E hω)⁻¹ := by
  apply Subtype.ext
  change ((normOmegaCast E (by norm_num : 2 ≤ 4)
      ((qTwoLambdaTwo E hω).symm (rootD F (by norm_num : 3 ≤ 3) 2 (.ofAdd c))) :
        normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
    (qTwoW0 E hω : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) *
      (((qTwoLambda E hω).symm (rootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c)) :
        normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) *
      (qTwoW0 E hω : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))⁻¹
  rw [normOmegaCast_apply, coe_qTwoLambdaTwo_symm_rootD, coe_qTwoLambda_symm_rootD]
  norm_num [rootIdxD, rootIdxD', rootSignD]
  rw [castEquiv_eichler]
  simp [qTwoFill_qTwoVecTwo, qTwoFill_smul]
  rw [eichler_conj (qTwoW0_mem_orthogonalGroup E hω)]
  change eichler (normHypForm E 4) (qTwoVec F ω 2 true) (c • qTwoVec F ω 1 true) =
    eichler (normHypForm E 4) (qTwoW0Lin E (qTwoVec F ω 2 false))
      (qTwoW0Lin E (c • qTwoVec F ω 1 true))
  rw [map_smul, qTwoW0Lin_qTwoVec_two E false,
    qTwoW0Lin_qTwoVec_zero_one E (by norm_num : (1 : Fin 5) < 2) true]
  simp

private theorem cast_qTwoLambdaTwo_symm_negRootD_two (c : F) :
    normOmegaCast E (by norm_num : 2 ≤ 4)
        ((qTwoLambdaTwo E hω).symm (negRootD F (by norm_num : 3 ≤ 3) 2 (.ofAdd c))) =
      qTwoW0 E hω * (qTwoLambda E hω).symm (negRootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c)) *
        (qTwoW0 E hω)⁻¹ := by
  apply Subtype.ext
  change ((normOmegaCast E (by norm_num : 2 ≤ 4)
      ((qTwoLambdaTwo E hω).symm (negRootD F (by norm_num : 3 ≤ 3) 2 (.ofAdd c))) :
        normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
    (qTwoW0 E hω : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) *
      (((qTwoLambda E hω).symm (negRootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c)) :
        normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) *
      (qTwoW0 E hω : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))⁻¹
  rw [normOmegaCast_apply, coe_qTwoLambdaTwo_symm_negRootD, coe_qTwoLambda_symm_negRootD]
  norm_num [rootIdxD, rootIdxD', rootSignD]
  rw [castEquiv_eichler]
  simp [qTwoFill_qTwoVecTwo, qTwoFill_smul]
  rw [eichler_conj (qTwoW0_mem_orthogonalGroup E hω)]
  change eichler (normHypForm E 4) (qTwoVec F ω 1 false) (c • qTwoVec F ω 2 false) =
    eichler (normHypForm E 4) (qTwoW0Lin E (qTwoVec F ω 1 false))
      (qTwoW0Lin E (c • qTwoVec F ω 2 true))
  rw [map_smul, qTwoW0Lin_qTwoVec_zero_one E (by norm_num : (1 : Fin 5) < 2) false,
    qTwoW0Lin_qTwoVec_two E true]
  simp

end CastRoots

section ConjRoots

private theorem conj_qTwoPermOmega_cast_qTwoLambdaTwoW_symm_rootD (k : Fin 3) (c : F) :
    qTwoPermOmega E * normOmegaCast E (by norm_num : 2 ≤ 4)
        ((qTwoLambdaTwoW E hω).symm (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) *
      (qTwoPermOmega E)⁻¹ =
      (qTwoLambda E hω).symm
        (rootD F (by norm_num : 3 ≤ 5) ⟨(k : ℕ) + 2, by omega⟩ (.ofAdd c)) := by
  apply Subtype.ext
  change ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) *
      (((normOmegaCast E (by norm_num : 2 ≤ 4)
        ((qTwoLambdaTwoW E hω).symm (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) :
          normOmega E 4)) : ((F × F) × (Fin 4 → K)) ≃ₗ[F]
            ((F × F) × (Fin 4 → K))) *
      (((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))))⁻¹ =
    (((qTwoLambda E hω).symm
      (rootD F (by norm_num : 3 ≤ 5) ⟨(k : ℕ) + 2, by omega⟩ (.ofAdd c)) :
        normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F]
          ((F × F) × (Fin 4 → K)))
  rw [normOmegaCast_apply, coe_qTwoLambdaTwoW_symm_rootD, coe_qTwoLambda_symm_rootD]
  fin_cases k
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwoW, qTwoFill_smul, qTwoIdxW]
    rw [eichler_conj (qTwoPermOmega_mem_orthogonalGroup E)]
    rw [map_smul, qTwoPermOmega_qTwoVec_zero E false, qTwoPermOmega_qTwoVec_two E true]
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwoW, qTwoFill_smul, qTwoIdxW]
    rw [eichler_conj (qTwoPermOmega_mem_orthogonalGroup E)]
    rw [map_smul, qTwoPermOmega_qTwoVec_one E false, qTwoPermOmega_qTwoVec_zero E true]
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwoW, qTwoFill_smul, qTwoIdxW]
    rw [eichler_conj (qTwoPermOmega_mem_orthogonalGroup E)]
    rw [map_smul, qTwoPermOmega_qTwoVec_one E true, qTwoPermOmega_qTwoVec_zero E true]

private theorem conj_qTwoPermOmega_cast_qTwoLambdaTwoW_symm_negRootD (k : Fin 3) (c : F) :
    qTwoPermOmega E * normOmegaCast E (by norm_num : 2 ≤ 4)
        ((qTwoLambdaTwoW E hω).symm (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) *
      (qTwoPermOmega E)⁻¹ =
      (qTwoLambda E hω).symm
        (negRootD F (by norm_num : 3 ≤ 5) ⟨(k : ℕ) + 2, by omega⟩ (.ofAdd c)) := by
  apply Subtype.ext
  change ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) *
      (((normOmegaCast E (by norm_num : 2 ≤ 4)
        ((qTwoLambdaTwoW E hω).symm (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) :
          normOmega E 4)) : ((F × F) × (Fin 4 → K)) ≃ₗ[F]
            ((F × F) × (Fin 4 → K))) *
      (((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))))⁻¹ =
    (((qTwoLambda E hω).symm
      (negRootD F (by norm_num : 3 ≤ 5) ⟨(k : ℕ) + 2, by omega⟩ (.ofAdd c)) :
        normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F]
          ((F × F) × (Fin 4 → K)))
  rw [normOmegaCast_apply, coe_qTwoLambdaTwoW_symm_negRootD, coe_qTwoLambda_symm_negRootD]
  fin_cases k
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwoW, qTwoFill_smul, qTwoIdxW]
    rw [eichler_conj (qTwoPermOmega_mem_orthogonalGroup E)]
    rw [map_smul, qTwoPermOmega_qTwoVec_two E false, qTwoPermOmega_qTwoVec_zero E true]
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwoW, qTwoFill_smul, qTwoIdxW]
    rw [eichler_conj (qTwoPermOmega_mem_orthogonalGroup E)]
    rw [map_smul, qTwoPermOmega_qTwoVec_zero E false, qTwoPermOmega_qTwoVec_one E true]
  · norm_num [rootIdxD, rootIdxD', rootSignD]
    rw [castEquiv_eichler]
    simp [qTwoFill_qTwoVecTwoW, qTwoFill_smul, qTwoIdxW]
    rw [eichler_conj (qTwoPermOmega_mem_orthogonalGroup E)]
    rw [map_smul, qTwoPermOmega_qTwoVec_zero E false, qTwoPermOmega_qTwoVec_one E false]

end ConjRoots

section LeviMembership

private theorem mem_map_levi_zero_one_rootD {j : Fin 5}
    (hj : j ∈ ({0, 1} : Finset (Fin 5))) (c : F) :
    (qTwoLambda E hω).symm (rootD F (by norm_num : 3 ≤ 5) j (.ofAdd c)) ∈
      (levi (plusRootGroup 5 F (by norm_num)) {0, 1}).map
        (qTwoLambda E hω).symm.toMonoidHom :=
  Subgroup.mem_map_of_mem _ (rankOne_le_levi _ hj (by
    rw [rankOne_plusRootGroup_eq_sup (by norm_num : 3 ≤ 5)]
    exact Subgroup.mem_sup_left ⟨Multiplicative.ofAdd c, rfl⟩))

private theorem mem_map_levi_zero_one_negRootD {j : Fin 5}
    (hj : j ∈ ({0, 1} : Finset (Fin 5))) (c : F) :
    (qTwoLambda E hω).symm (negRootD F (by norm_num : 3 ≤ 5) j (.ofAdd c)) ∈
      (levi (plusRootGroup 5 F (by norm_num)) {0, 1}).map
        (qTwoLambda E hω).symm.toMonoidHom :=
  Subgroup.mem_map_of_mem _ (rankOne_le_levi _ hj (by
    rw [rankOne_plusRootGroup_eq_sup (by norm_num : 3 ≤ 5)]
    exact Subgroup.mem_sup_right ⟨Multiplicative.ofAdd c, rfl⟩))

private theorem mem_map_conj_w0_rootD (c : F) :
    qTwoW0 E hω * (qTwoLambda E hω).symm (rootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c)) *
        (qTwoW0 E hω)⁻¹ ∈
      ((rankOne (plusRootGroup 5 F (by norm_num)) 1).map
        (qTwoLambda E hω).symm.toMonoidHom).map
          (MulAut.conj (qTwoW0 E hω)).toMonoidHom := by
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ ?_)
  rw [rankOne_plusRootGroup_eq_sup (by norm_num : 3 ≤ 5)]
  exact Subgroup.mem_sup_left ⟨Multiplicative.ofAdd c, rfl⟩

private theorem mem_map_conj_w0_negRootD (c : F) :
    qTwoW0 E hω * (qTwoLambda E hω).symm (negRootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c)) *
        (qTwoW0 E hω)⁻¹ ∈
      ((rankOne (plusRootGroup 5 F (by norm_num)) 1).map
        (qTwoLambda E hω).symm.toMonoidHom).map
          (MulAut.conj (qTwoW0 E hω)).toMonoidHom := by
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ ?_)
  rw [rankOne_plusRootGroup_eq_sup (by norm_num : 3 ≤ 5)]
  exact Subgroup.mem_sup_right ⟨Multiplicative.ofAdd c, rfl⟩

end LeviMembership

theorem map_rankOne_le_normBlock_zero_one {j : Fin 5} (hj : (j : ℕ) < 2) :
    (rankOne (plusRootGroup 5 F (by norm_num)) j).map (qTwoLambda E hω).symm.toMonoidHom ≤
      normBlock E 4 {0, 1} := by
  rw [normBlock_zero_one_eq_range E (by norm_num : 2 ≤ 4)]
  rw [rankOne_plusRootGroup_eq_sup (by norm_num : 3 ≤ 5) j, Subgroup.map_sup]
  apply sup_le
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
    exact ⟨(qTwoLambdaTwo E hω).symm
        (rootD F (by norm_num : 3 ≤ 3) ⟨j, by omega⟩ (.ofAdd c)),
      cast_qTwoLambdaTwo_symm_rootD_zero_one E hω hj c⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
    exact ⟨(qTwoLambdaTwo E hω).symm
        (negRootD F (by norm_num : 3 ≤ 3) ⟨j, by omega⟩ (.ofAdd c)),
      cast_qTwoLambdaTwo_symm_negRootD_zero_one E hω hj c⟩

theorem map_rankOne_le_normBlock_two_three {j : Fin 5} (hj : 2 ≤ (j : ℕ)) :
    (rankOne (plusRootGroup 5 F (by norm_num)) j).map (qTwoLambda E hω).symm.toMonoidHom ≤
      normBlock E 4 {2, 3} := by
  rw [normBlock_two_three_eq_map E (by norm_num : 2 ≤ 4)]
  rw [rankOne_plusRootGroup_eq_sup (by norm_num : 3 ≤ 5) j, Subgroup.map_sup]
  apply sup_le
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
    refine ⟨normOmegaCast E (by norm_num : 2 ≤ 4) ((qTwoLambdaTwoW E hω).symm
        (rootD F (by norm_num : 3 ≤ 3) ⟨(j : ℕ) - 2, by omega⟩ (.ofAdd c))),
      ⟨(qTwoLambdaTwoW E hω).symm
        (rootD F (by norm_num : 3 ≤ 3) ⟨(j : ℕ) - 2, by omega⟩ (.ofAdd c)), rfl⟩, ?_⟩
    have hidx : (⟨((⟨(j : ℕ) - 2, by omega⟩ : Fin 3) : ℕ) + 2, by omega⟩ : Fin 5) = j := by
      apply Fin.ext
      exact Nat.sub_add_cancel hj
    have hconj := conj_qTwoPermOmega_cast_qTwoLambdaTwoW_symm_rootD E hω
      ⟨(j : ℕ) - 2, by omega⟩ c
    rw [hidx] at hconj
    exact hconj
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
    refine ⟨normOmegaCast E (by norm_num : 2 ≤ 4) ((qTwoLambdaTwoW E hω).symm
        (negRootD F (by norm_num : 3 ≤ 3) ⟨(j : ℕ) - 2, by omega⟩ (.ofAdd c))),
      ⟨(qTwoLambdaTwoW E hω).symm
        (negRootD F (by norm_num : 3 ≤ 3) ⟨(j : ℕ) - 2, by omega⟩ (.ofAdd c)), rfl⟩, ?_⟩
    have hidx : (⟨((⟨(j : ℕ) - 2, by omega⟩ : Fin 3) : ℕ) + 2, by omega⟩ : Fin 5) = j := by
      apply Fin.ext
      exact Nat.sub_add_cancel hj
    have hconj := conj_qTwoPermOmega_cast_qTwoLambdaTwoW_symm_negRootD E hω
      ⟨(j : ℕ) - 2, by omega⟩ c
    rw [hidx] at hconj
    exact hconj

private theorem mem_comap_conj_castHom_rootD
    (T : Subgroup (normOmega E 4)) (h24 : 2 ≤ 4) (k : Fin 3) (c : F)
    (hmem : ((qTwoLambda E hω).symm
      (rootD F (by norm_num : 3 ≤ 5) ⟨(k : ℕ) + 2, by omega⟩ (.ofAdd c)) :
        normOmega E 4) ∈ T) :
    spinAction (normHypForm E 2)
        ((qTwoFrameTwoW hω).longRoot (rootIdxD_ne 3 (by norm_num) k) true
          (rootSignD 3 k) (.ofAdd c)) ∈
      (T.map (normOmega E 4).subtype).comap
        (((MulAut.conj ((qTwoPermOmega E : normOmega E 4) :
          ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))).toMonoidHom).comp
          (castHom h24)) := by
  have hx : spinAction (normHypForm E 2)
      ((qTwoFrameTwoW hω).longRoot (rootIdxD_ne 3 (by norm_num) k) true
        (rootSignD 3 k) (.ofAdd c)) =
      ((qTwoLambdaTwoW E hω).symm
        (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)) : normOmega E 2) := by
    rw [(qTwoFrameTwoW hω).spinAction_longRoot_eq_eichler
      (rootIdxD_ne 3 (by norm_num) k) true (rootSignD 3 k) c,
      coe_qTwoLambdaTwoW_symm_rootD]
    rfl
  rw [hx, Subgroup.mem_comap]
  change (MulAut.conj ((qTwoPermOmega E : normOmega E 4) :
      ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))))
      (castEquiv h24 (((qTwoLambdaTwoW E hω).symm
        (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) : normOmega E 2)) ∈
    Subgroup.map (normOmega E 4).subtype T
  rw [show castEquiv h24 (((qTwoLambdaTwoW E hω).symm
        (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) : normOmega E 2) =
      (((normOmegaCast E h24 ((qTwoLambdaTwoW E hω).symm
        (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)))) : normOmega E 4) :
          ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) from
    (normOmegaCast_apply E h24 _).symm]
  have hC := conj_qTwoPermOmega_cast_qTwoLambdaTwoW_symm_rootD E hω k c
  rw [show (MulAut.conj ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))))
        (((normOmegaCast E h24 ((qTwoLambdaTwoW E hω).symm
          (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)))) : normOmega E 4) :
            ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
      (((qTwoLambda E hω).symm
        (rootD F (by norm_num : 3 ≤ 5) ⟨(k : ℕ) + 2, by omega⟩ (.ofAdd c)) :
          normOmega E 4) :
            ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) from by
    rw [MulAut.conj_apply]
    exact congrArg Subtype.val hC]
  exact Subgroup.mem_map_of_mem (normOmega E 4).subtype hmem

private theorem mem_comap_conj_castHom_negRootD
    (T : Subgroup (normOmega E 4)) (h24 : 2 ≤ 4) (k : Fin 3) (c : F)
    (hmem : ((qTwoLambda E hω).symm
      (negRootD F (by norm_num : 3 ≤ 5) ⟨(k : ℕ) + 2, by omega⟩ (.ofAdd c)) :
        normOmega E 4) ∈ T) :
    spinAction (normHypForm E 2)
        ((qTwoFrameTwoW hω).longRoot (rootIdxD_ne 3 (by norm_num) k).symm
          (!rootSignD 3 k) false (.ofAdd c)) ∈
      (T.map (normOmega E 4).subtype).comap
        (((MulAut.conj ((qTwoPermOmega E : normOmega E 4) :
          ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))).toMonoidHom).comp
          (castHom h24)) := by
  have hx : spinAction (normHypForm E 2)
      ((qTwoFrameTwoW hω).longRoot (rootIdxD_ne 3 (by norm_num) k).symm
        (!rootSignD 3 k) false (.ofAdd c)) =
      ((qTwoLambdaTwoW E hω).symm
        (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)) : normOmega E 2) := by
    rw [(qTwoFrameTwoW hω).spinAction_longRoot_eq_eichler
      (rootIdxD_ne 3 (by norm_num) k).symm (!rootSignD 3 k) false c,
      coe_qTwoLambdaTwoW_symm_negRootD]
    rfl
  rw [hx, Subgroup.mem_comap]
  change (MulAut.conj ((qTwoPermOmega E : normOmega E 4) :
      ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))))
      (castEquiv h24 (((qTwoLambdaTwoW E hω).symm
        (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) : normOmega E 2)) ∈
    Subgroup.map (normOmega E 4).subtype T
  rw [show castEquiv h24 (((qTwoLambdaTwoW E hω).symm
        (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) : normOmega E 2) =
      (((normOmegaCast E h24 ((qTwoLambdaTwoW E hω).symm
        (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)))) : normOmega E 4) :
          ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) from
    (normOmegaCast_apply E h24 _).symm]
  have hC := conj_qTwoPermOmega_cast_qTwoLambdaTwoW_symm_negRootD E hω k c
  rw [show (MulAut.conj ((qTwoPermOmega E : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))))
        (((normOmegaCast E h24 ((qTwoLambdaTwoW E hω).symm
          (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)))) : normOmega E 4) :
            ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
      (((qTwoLambda E hω).symm
        (negRootD F (by norm_num : 3 ≤ 5) ⟨(k : ℕ) + 2, by omega⟩ (.ofAdd c)) :
          normOmega E 4) :
            ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) from by
    rw [MulAut.conj_apply]
    exact congrArg Subtype.val hC]
  exact Subgroup.mem_map_of_mem (normOmega E 4).subtype hmem

private theorem normOmega_two_le_conj_castHom_comap
    (hω : IsTraceNormOne E ω) (h24 : 2 ≤ 4) :
    normOmega E 2 ≤
      (((levi (plusRootGroup 5 F (by norm_num)) {2, 3, 4}).map
        (qTwoLambda E hω).symm.toMonoidHom).map (normOmega E 4).subtype).comap
        (((MulAut.conj ((qTwoPermOmega E : normOmega E 4) :
          ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))).toMonoidHom).comp
          (castHom h24)) := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have hgen := commutator_eq_iSup_simpleRoot (qTwoFrameTwoW hω)
    (finrank_normHypForm E 2) le_rfl CharTwo.two_eq_zero
  rw [show normOmega E 2 =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 2),
        TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 2)⁆ from rfl, hgen]
  refine iSup_le fun k => sup_le ?_ ?_
  · rintro x ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
    exact mem_comap_conj_castHom_rootD E hω _ h24 k c
      (Subgroup.mem_map_of_mem (qTwoLambda E hω).symm.toMonoidHom
        (rankOne_le_levi (plusRootGroup 5 F (by norm_num))
          (J := ({2, 3, 4} : Finset (Fin 5)))
          (j := ⟨(k : ℕ) + 2, by omega⟩) (by fin_cases k <;> decide)
          (by
            rw [rankOne_plusRootGroup_eq_sup (by norm_num : 3 ≤ 5)]
            exact Subgroup.mem_sup_left ⟨Multiplicative.ofAdd c, rfl⟩)))
  · rintro x ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
    exact mem_comap_conj_castHom_negRootD E hω _ h24 k c
      (Subgroup.mem_map_of_mem (qTwoLambda E hω).symm.toMonoidHom
        (rankOne_le_levi (plusRootGroup 5 F (by norm_num))
          (J := ({2, 3, 4} : Finset (Fin 5)))
          (j := ⟨(k : ℕ) + 2, by omega⟩) (by fin_cases k <;> decide)
          (by
            rw [rankOne_plusRootGroup_eq_sup (by norm_num : 3 ≤ 5)]
            exact Subgroup.mem_sup_right ⟨Multiplicative.ofAdd c, rfl⟩)))

private theorem map_range_le_of_normOmega_le_comap
    (T : Subgroup (normOmega E 4)) (h24 : 2 ≤ 4)
    (χ : (((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) →*
      (((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))))
    (χ₀ : normOmega E 4 →* normOmega E 4)
    (hχ₀ : ∀ x : normOmega E 4,
      ((χ₀ x : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) = χ x)
    (hle : normOmega E 2 ≤
      (T.map (normOmega E 4).subtype).comap (χ.comp (castHom h24))) :
    (normOmegaCast E h24).range.map χ₀ ≤ T := by
  rintro x ⟨y, ⟨a, rfl⟩, rfl⟩
  have ha := hle a.2
  rw [Subgroup.mem_comap] at ha
  obtain ⟨t, ht, hta⟩ := ha
  have hkey : χ₀ (normOmegaCast E h24 a) = t := by
    apply Subtype.ext
    rw [hχ₀, normOmegaCast_apply]
    exact hta.symm
  rw [hkey]
  exact ht

theorem normBlock_two_three_le_map_levi :
    normBlock E 4 {2, 3} ≤
      (levi (plusRootGroup 5 F (by norm_num)) {2, 3, 4}).map
        (qTwoLambda E hω).symm.toMonoidHom := by
  set T : Subgroup (normOmega E 4) :=
    (levi (plusRootGroup 5 F (by norm_num)) {2, 3, 4}).map
      (qTwoLambda E hω).symm.toMonoidHom
  have h24 : 2 ≤ 4 := by norm_num
  rw [normBlock_two_three_eq_map E h24]
  exact map_range_le_of_normOmega_le_comap E T h24
    ((MulAut.conj ((qTwoPermOmega E : normOmega E 4) :
      ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))).toMonoidHom)
    ((MulAut.conj (qTwoPermOmega E)).toMonoidHom) (fun _ => rfl)
    (normOmega_two_le_conj_castHom_comap E hω h24)

private theorem fin5_mem_zero_one_of_lt_two {k : Fin 5} (hk : (k : ℕ) < 2) :
    k ∈ ({0, 1} : Finset (Fin 5)) := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  by_cases hk0 : (k : ℕ) = 0
  · left
    exact Fin.ext hk0
  · right
    exact Fin.ext (by omega)

private theorem mem_comap_castHom_rootD
    (T : Subgroup (normOmega E 4)) (h24 : 2 ≤ 4) (k : Fin 3) (c : F)
    (hmem_lt_two : (k : ℕ) < 2 →
      ((qTwoLambda E hω).symm
        (rootD F (by norm_num : 3 ≤ 5) ⟨k, by omega⟩ (.ofAdd c)) : normOmega E 4) ∈ T)
    (hmem_eq_two : k = 2 →
      (qTwoW0 E hω * (qTwoLambda E hω).symm
        (rootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c)) * (qTwoW0 E hω)⁻¹ :
          normOmega E 4) ∈ T) :
    spinAction (normHypForm E 2)
        ((qTwoFrameTwo hω).longRoot (rootIdxD_ne 3 (by norm_num) k) true
          (rootSignD 3 k) (.ofAdd c)) ∈
      (T.map (normOmega E 4).subtype).comap (castHom h24) := by
  have hx : spinAction (normHypForm E 2)
      ((qTwoFrameTwo hω).longRoot (rootIdxD_ne 3 (by norm_num) k) true
        (rootSignD 3 k) (.ofAdd c)) =
      ((qTwoLambdaTwo E hω).symm
        (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)) : normOmega E 2) := by
    rw [(qTwoFrameTwo hω).spinAction_longRoot_eq_eichler
      (rootIdxD_ne 3 (by norm_num) k) true (rootSignD 3 k) c,
      coe_qTwoLambdaTwo_symm_rootD]
    rfl
  rw [hx, Subgroup.mem_comap]
  change castEquiv h24 (((qTwoLambdaTwo E hω).symm
      (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) : normOmega E 2) ∈
    Subgroup.map (normOmega E 4).subtype T
  by_cases hk : (k : ℕ) < 2
  · have hA := cast_qTwoLambdaTwo_symm_rootD_zero_one E hω hk c
    have heq : castEquiv h24 (((qTwoLambdaTwo E hω).symm
          (rootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) : normOmega E 2) =
        (((qTwoLambda E hω).symm (rootD F (by norm_num : 3 ≤ 5)
          ⟨k, by omega⟩ (.ofAdd c)) : normOmega E 4) :
            ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) :=
      (normOmegaCast_apply E h24 _).symm.trans (congrArg Subtype.val hA)
    rw [heq]
    exact Subgroup.mem_map_of_mem (normOmega E 4).subtype (hmem_lt_two hk)
  · have hk2 : k = 2 := Fin.ext (by omega)
    subst hk2
    have hB := cast_qTwoLambdaTwo_symm_rootD_two E hω c
    have heq : castEquiv h24 (((qTwoLambdaTwo E hω).symm
          (rootD F (by norm_num : 3 ≤ 3) 2 (.ofAdd c))) : normOmega E 2) =
        (qTwoW0 E hω * (((qTwoLambda E hω).symm
          (rootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c))) : normOmega E 4) *
            (qTwoW0 E hω)⁻¹ :
              ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) :=
      (normOmegaCast_apply E h24 _).symm.trans (congrArg Subtype.val hB)
    rw [heq]
    exact Subgroup.mem_map_of_mem (normOmega E 4).subtype (hmem_eq_two rfl)

private theorem mem_comap_castHom_negRootD
    (T : Subgroup (normOmega E 4)) (h24 : 2 ≤ 4) (k : Fin 3) (c : F)
    (hmem_lt_two : (k : ℕ) < 2 →
      ((qTwoLambda E hω).symm
        (negRootD F (by norm_num : 3 ≤ 5) ⟨k, by omega⟩ (.ofAdd c)) : normOmega E 4) ∈ T)
    (hmem_eq_two : k = 2 →
      (qTwoW0 E hω * (qTwoLambda E hω).symm
        (negRootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c)) * (qTwoW0 E hω)⁻¹ :
          normOmega E 4) ∈ T) :
    spinAction (normHypForm E 2)
        ((qTwoFrameTwo hω).longRoot (rootIdxD_ne 3 (by norm_num) k).symm
          (!rootSignD 3 k) false (.ofAdd c)) ∈
      (T.map (normOmega E 4).subtype).comap (castHom h24) := by
  have hx : spinAction (normHypForm E 2)
      ((qTwoFrameTwo hω).longRoot (rootIdxD_ne 3 (by norm_num) k).symm
        (!rootSignD 3 k) false (.ofAdd c)) =
      ((qTwoLambdaTwo E hω).symm
        (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c)) : normOmega E 2) := by
    rw [(qTwoFrameTwo hω).spinAction_longRoot_eq_eichler
      (rootIdxD_ne 3 (by norm_num) k).symm (!rootSignD 3 k) false c,
      coe_qTwoLambdaTwo_symm_negRootD]
    rfl
  rw [hx, Subgroup.mem_comap]
  change castEquiv h24 (((qTwoLambdaTwo E hω).symm
      (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) : normOmega E 2) ∈
    Subgroup.map (normOmega E 4).subtype T
  by_cases hk : (k : ℕ) < 2
  · have hA := cast_qTwoLambdaTwo_symm_negRootD_zero_one E hω hk c
    have heq : castEquiv h24 (((qTwoLambdaTwo E hω).symm
          (negRootD F (by norm_num : 3 ≤ 3) k (.ofAdd c))) : normOmega E 2) =
        (((qTwoLambda E hω).symm (negRootD F (by norm_num : 3 ≤ 5)
          ⟨k, by omega⟩ (.ofAdd c)) : normOmega E 4) :
            ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) :=
      (normOmegaCast_apply E h24 _).symm.trans (congrArg Subtype.val hA)
    rw [heq]
    exact Subgroup.mem_map_of_mem (normOmega E 4).subtype (hmem_lt_two hk)
  · have hk2 : k = 2 := Fin.ext (by omega)
    subst hk2
    have hB := cast_qTwoLambdaTwo_symm_negRootD_two E hω c
    have heq : castEquiv h24 (((qTwoLambdaTwo E hω).symm
          (negRootD F (by norm_num : 3 ≤ 3) 2 (.ofAdd c))) : normOmega E 2) =
        (qTwoW0 E hω * (((qTwoLambda E hω).symm
          (negRootD F (by norm_num : 3 ≤ 5) 1 (.ofAdd c))) : normOmega E 4) *
            (qTwoW0 E hω)⁻¹ :
              ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) :=
      (normOmegaCast_apply E h24 _).symm.trans (congrArg Subtype.val hB)
    rw [heq]
    exact Subgroup.mem_map_of_mem (normOmega E 4).subtype (hmem_eq_two rfl)

private theorem normOmega_two_le_castHom_comap (h24 : 2 ≤ 4) :
    normOmega E 2 ≤
      (((levi (plusRootGroup 5 F (by norm_num)) {0, 1}).map
            (qTwoLambda E hω).symm.toMonoidHom ⊔
          ((rankOne (plusRootGroup 5 F (by norm_num)) 1).map
            (qTwoLambda E hω).symm.toMonoidHom).map
              (MulAut.conj (qTwoW0 E hω)).toMonoidHom).map
        (normOmega E 4).subtype).comap (castHom h24) := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have hgen := commutator_eq_iSup_simpleRoot (qTwoFrameTwo hω)
    (finrank_normHypForm E 2) le_rfl CharTwo.two_eq_zero
  rw [show normOmega E 2 =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 2),
        TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 2)⁆ from rfl, hgen]
  refine iSup_le fun k => sup_le ?_ ?_
  · rintro x ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
    exact mem_comap_castHom_rootD E hω _ h24 k c
      (fun hk => Subgroup.mem_sup_left (mem_map_levi_zero_one_rootD E hω
        (fin5_mem_zero_one_of_lt_two hk) c))
      (fun _ => Subgroup.mem_sup_right (mem_map_conj_w0_rootD E hω c))
  · rintro x ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
    exact mem_comap_castHom_negRootD E hω _ h24 k c
      (fun hk => Subgroup.mem_sup_left (mem_map_levi_zero_one_negRootD E hω
        (fin5_mem_zero_one_of_lt_two hk) c))
      (fun _ => Subgroup.mem_sup_right (mem_map_conj_w0_negRootD E hω c))

theorem normBlock_zero_one_le_map_levi :
    normBlock E 4 {0, 1} ≤
      (levi (plusRootGroup 5 F (by norm_num)) {0, 1}).map (qTwoLambda E hω).symm.toMonoidHom ⊔
        ((rankOne (plusRootGroup 5 F (by norm_num)) 1).map
          (qTwoLambda E hω).symm.toMonoidHom).map (MulAut.conj (qTwoW0 E hω)).toMonoidHom := by
  set T : Subgroup (normOmega E 4) :=
    (levi (plusRootGroup 5 F (by norm_num)) {0, 1}).map
        (qTwoLambda E hω).symm.toMonoidHom ⊔
      ((rankOne (plusRootGroup 5 F (by norm_num)) 1).map
        (qTwoLambda E hω).symm.toMonoidHom).map
          (MulAut.conj (qTwoW0 E hω)).toMonoidHom
  have h24 : 2 ≤ 4 := by norm_num
  rw [normBlock_zero_one_eq_range E h24]
  have hle := normOmega_two_le_castHom_comap E hω h24
  have hmap := map_range_le_of_normOmega_le_comap E T h24
    (MonoidHom.id _) (MonoidHom.id _) (fun _ => rfl) hle
  simpa only [Subgroup.map_id] using hmap

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

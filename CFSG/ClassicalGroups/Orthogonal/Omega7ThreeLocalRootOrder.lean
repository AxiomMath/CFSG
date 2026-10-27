module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRoot
import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type} [Field K]

@[expose] def vecOf (K : Type) [Field K] (xs ys : Fin 3 → K) (z : K) : Idx → K :=
  Sum.elim xs (Sum.elim ys fun _ => z)

@[simp] theorem vecOf_inl (xs ys : Fin 3 → K) (z : K) (i : Fin 3) :
    vecOf K xs ys z (.inl i) = xs i := rfl

@[simp] theorem vecOf_inr_inl (xs ys : Fin 3 → K) (z : K) (i : Fin 3) :
    vecOf K xs ys z (.inr (.inl i)) = ys i := rfl

@[simp] theorem vecOf_inr_inr (xs ys : Fin 3 → K) (z : K) :
    vecOf K xs ys z (.inr (.inr ())) = z := rfl

theorem vecOf_eq_iff (xs ys xs' ys' : Fin 3 → K) (z z' : K) :
    vecOf K xs ys z = vecOf K xs' ys' z' ↔ xs = xs' ∧ ys = ys' ∧ z = z' := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_, ?_⟩
    · simpa using congrFun h (.inl i)
    · simpa using congrFun h (.inr (.inl i))
    · simpa using congrFun h (.inr (.inr ()))
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem modelQuad_vecOf (a : K) (xs ys : Fin 3 → K) (z : K) :
    modelQuad K a (vecOf K xs ys z) =
      (xs 0 ^ 2 - xs 0 * ys 0 + ys 0 ^ 2) + (xs 1 ^ 2 - xs 1 * ys 1 + ys 1 ^ 2) +
        (xs 2 ^ 2 - xs 2 * ys 2 + ys 2 ^ 2) + a * z ^ 2 := by
  simp [modelQuad, Fin.sum_univ_three]

theorem modelPolar_vecOf (a : K) (xs ys xs' ys' : Fin 3 → K) (z z' : K) :
    modelPolar K a (vecOf K xs ys z) (vecOf K xs' ys' z') =
      (2 * xs 0 * xs' 0 - xs 0 * ys' 0 - ys 0 * xs' 0 + 2 * ys 0 * ys' 0) +
        (2 * xs 1 * xs' 1 - xs 1 * ys' 1 - ys 1 * xs' 1 + 2 * ys 1 * ys' 1) +
        (2 * xs 2 * xs' 2 - xs 2 * ys' 2 - ys 2 * xs' 2 + 2 * ys 2 * ys' 2) + 2 * a * z * z' := by
  simp [modelPolar, Fin.sum_univ_three]

theorem vecOf_eq_self (w : Idx → K) :
    vecOf K (fun i => w (.inl i)) (fun i => w (.inr (.inl i))) (w (.inr (.inr ()))) = w := by
  funext a
  rcases a with i | i | ⟨⟩ <;> rfl

theorem rotMat_mulVec_vecOf (v : Fin 3 → ZMod 3) (xs ys : Fin 3 → K) (z : K) :
    rotMat K v *ᵥ vecOf K xs ys z =
      vecOf K (fun i => planeRot K (v i) 0 0 * xs i + planeRot K (v i) 0 1 * ys i)
        (fun i => planeRot K (v i) 1 0 * xs i + planeRot K (v i) 1 1 * ys i) z := by
  funext a
  rcases a with i | i | ⟨⟩
  · rw [rotMat_mulVec_inl]
    rfl
  · rw [rotMat_mulVec_inr_inl]
    rfl
  · rw [rotMat_mulVec_inr_inr]
    rfl

theorem modelPolar_smul_right (a : K) (u w : Idx → K) (c : K) :
    modelPolar K a u (c • w) = c * modelPolar K a u w := by
  simp only [modelPolar, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem modelPolar_neg_right (a : K) (u w : Idx → K) :
    modelPolar K a u (-w) = -modelPolar K a u w := by
  simp only [modelPolar, Pi.neg_apply, Fin.sum_univ_three]
  ring

theorem omegaRoot_zero_right [Finite K] (F : Frame K) (u : Idx → K) : omegaRoot F u 0 = 1 := by
  apply Subtype.ext
  apply (toLinEquiv Idx K).injective
  show toLinEquiv Idx K (omegaRootGL F u 0) = toLinEquiv Idx K 1
  rw [toLinEquiv_omegaRootGL, map_zero, eichler_zero_right, map_one]

theorem omegaRoot_inv [Finite K] (F : Frame K) {u w : Idx → K} (hw : modelPolar K F.a u w = 0) :
    (omegaRoot F u w)⁻¹ = omegaRoot F u (-w) := by
  have hnw : modelPolar K F.a u (-w) = 0 := by rw [modelPolar_neg_right, hw, neg_zero]
  rw [inv_eq_iff_mul_eq_one, omegaRoot_mul F hw hnw, add_neg_cancel, omegaRoot_zero_right]

theorem omegaRoot_pow [Finite K] (F : Frame K) {u w : Idx → K} (hw : modelPolar K F.a u w = 0)
    (n : ℕ) : omegaRoot F u w ^ n = omegaRoot F u (n • w) := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, omegaRoot_zero_right]
  | succ n ih =>
    have hn : modelPolar K F.a u (n • w) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, modelPolar_smul_right, hw, mul_zero]
    rw [pow_succ, ih, omegaRoot_mul F hn hw, succ_nsmul]

theorem omegaRoot_zpow [Finite K] (F : Frame K) {u w : Idx → K} (hw : modelPolar K F.a u w = 0)
    (k : ℤ) : omegaRoot F u w ^ k = omegaRoot F u (k • w) := by
  cases k with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, omegaRoot_pow F hw, natCast_zsmul]
  | negSucc n =>
    have hn : modelPolar K F.a u ((n + 1) • w) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, modelPolar_smul_right, hw, mul_zero]
    rw [zpow_negSucc, omegaRoot_pow F hw, omegaRoot_inv F hn, negSucc_zsmul]

theorem commute_omegaRoot_same_center [Finite K] (F : Frame K) {u w₁ w₂ : Idx → K}
    (h₁ : modelPolar K F.a u w₁ = 0) (h₂ : modelPolar K F.a u w₂ = 0) :
    Commute (omegaRoot F u w₁) (omegaRoot F u w₂) := by
  show omegaRoot F u w₁ * omegaRoot F u w₂ = omegaRoot F u w₂ * omegaRoot F u w₁
  rw [omegaRoot_mul F h₁ h₂, omegaRoot_mul F h₂ h₁, add_comm]

theorem omegaRoot_eq_omegaRoot_iff [Finite K] (F : Frame K) {u w w' : Idx → K}
    (hu : modelQuad K F.a u = 0) (hu0 : u ≠ 0) (hw : modelPolar K F.a u w = 0)
    (hw' : modelPolar K F.a u w' = 0) :
    omegaRoot F u w = omegaRoot F u w' ↔ ∃ c : K, w' = w + c • u := by
  have hQ := nondegenerate_polarBilin_quadOdd 3 K (Ring.two_ne_zero F.hK)
  have hu' : quadOdd 3 K (F.lin u) = 0 := by rw [F.quadOdd_lin, hu]
  have hu0' : F.lin u ≠ 0 := fun h => hu0 (F.lin.injective (by rw [h, map_zero]))
  have hw₁ : polar (quadOdd 3 K) (F.lin u) (F.lin w) = 0 := by rw [F.polar_lin, hw]
  have hw₂ : polar (quadOdd 3 K) (F.lin u) (F.lin w') = 0 := by rw [F.polar_lin, hw']
  have e : omegaRoot F u w = omegaRoot F u w' ↔
      eichler (quadOdd 3 K) (F.lin u) (F.lin w) = eichler (quadOdd 3 K) (F.lin u) (F.lin w') := by
    rw [← toLinEquiv_omegaRootGL, ← toLinEquiv_omegaRootGL,
      (toLinEquiv Idx K).injective.eq_iff, Subtype.ext_iff]
    rfl
  rw [e, eichler_eq_eichler_iff hQ hu' hu0' hw₁ hw₂]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, F.lin.injective (by rw [hc, map_add, map_smul])⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, map_add, map_smul]⟩

theorem omegaRoot_ne_one_of_not_mem_span [Finite K] (F : Frame K) {u w : Idx → K}
    (hu : modelQuad K F.a u = 0) (hu0 : u ≠ 0) (hw : modelPolar K F.a u w = 0)
    (hwu : ∀ c : K, w ≠ c • u) : omegaRoot F u w ≠ 1 := by
  intro h1
  rw [← omegaRoot_zero_right F u, omegaRoot_eq_omegaRoot_iff F hu hu0 hw
    (by rw [show (0 : Idx → K) = (0 : K) • 0 from (smul_zero _).symm, modelPolar_smul_right,
      zero_mul])] at h1
  obtain ⟨c, hc⟩ := h1
  exact hwu (-c) (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hc.symm)

theorem orderOf_omegaRoot [Finite K] (F : Frame K) {u w : Idx → K} (h : omegaRoot F u w ≠ 1) :
    orderOf (omegaRoot F u w) = ringChar K := by
  haveI : Fact (ringChar K).Prime := ⟨CharP.prime_ringChar K⟩
  refine orderOf_eq_prime ?_ h
  apply Subtype.ext
  exact omegaRootGL_pow_ringChar F u w

theorem omegaRoot_not_mem_zpowers [Finite K] (F : Frame K) {u w w' : Idx → K}
    (hu : modelQuad K F.a u = 0) (hu0 : u ≠ 0) (hw : modelPolar K F.a u w = 0)
    (hw' : modelPolar K F.a u w' = 0) (h : ∀ (k : ℤ) (c : K), w' ≠ k • w + c • u) :
    omegaRoot F u w' ∉ Subgroup.zpowers (omegaRoot F u w) := by
  rintro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkw : modelPolar K F.a u (k • w) = 0 := by
    rw [← Int.cast_smul_eq_zsmul K, modelPolar_smul_right, hw, mul_zero]
  rw [omegaRoot_zpow F hw] at hk
  obtain ⟨c, hc⟩ := (omegaRoot_eq_omegaRoot_iff F hu hu0 hkw hw').mp hk
  exact h k c hc

theorem commute_omegaRoot_of_polar_eq_zero [Finite K] (F : Frame K) {u w t t' : Idx → K}
    (hut : modelPolar K F.a u t = 0) (hut' : modelPolar K F.a u t' = 0)
    (hwt : modelPolar K F.a w t = 0) (hwt' : modelPolar K F.a w t' = 0) :
    Commute (omegaRoot F u w) (omegaRoot F t t') := by
  show omegaRoot F u w * omegaRoot F t t' = omegaRoot F t t' * omegaRoot F u w
  apply Subtype.ext
  apply (toLinEquiv Idx K).injective
  show toLinEquiv Idx K (omegaRootGL F u w * omegaRootGL F t t') =
    toLinEquiv Idx K (omegaRootGL F t t' * omegaRootGL F u w)
  rw [map_mul, map_mul, toLinEquiv_omegaRootGL, toLinEquiv_omegaRootGL]
  have hg := eichler_mem_orthogonalGroup (quadOdd 3 K) (F.lin t) (F.lin t')
  have h := eichler_conj hg (F.lin u) (F.lin w)
  rw [eichler_apply_of_polar_eq_zero (by rw [F.polar_lin]; exact hut)
      (by rw [F.polar_lin]; exact hut'),
    eichler_apply_of_polar_eq_zero (by rw [F.polar_lin]; exact hwt)
      (by rw [F.polar_lin]; exact hwt')] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem two_le_pRank_ringChar_of_commute [Finite K] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ H) (hxp : orderOf x = ringChar K)
    (hyp : orderOf y = ringChar K) (hxy : Commute x y) (hyx : y ∉ Subgroup.zpowers x) :
    2 ≤ CFSG.Open.pRank (ringChar K) H := by
  haveI : Fact (ringChar K).Prime := ⟨CharP.prime_ringChar K⟩
  exact CFSG.GroupTheory.two_le_pRank_of_commute hx hy hxp hyp hxy hyx

theorem one_le_pRank_ringChar_of_orderOf_eq [Finite K] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {x : G} (hx : x ∈ H) (hxp : orderOf x = ringChar K) :
    1 ≤ CFSG.Open.pRank (ringChar K) H := by
  have hle : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hx
  refine CFSG.SectionRank.le_pRank (CharP.prime_ringChar K).one_lt hle
    (CFSG.Open.isElemAbelian_zpowers ?_) (k := 1) ?_
  · rw [← hxp]
    exact pow_orderOf_eq_one x
  · rw [Nat.card_zpowers, hxp, pow_one]

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin412

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup CliffordAlgebra Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

namespace DA

section Frame

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {m : ℕ} (F : HypFrame Q m)

theorem coords_vec_of_ne {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (s t r : Bool) : (F.toFrame hij s t).coords (F.vec k r) = 0 := by
  have h1 : ∀ s', QuadraticMap.polar Q (F.vec k r) (F.vec i s') = 0 :=
    fun s' => F.polar_vec_of_ne hki r s'
  have h2 : ∀ t', QuadraticMap.polar Q (F.vec k r) (F.vec j t') = 0 :=
    fun t' => F.polar_vec_of_ne hkj r t'
  rw [Frame.coords_apply]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, h1, h2]

theorem longSL2_neg_one_not_mem_center [Finite K] (hodd : Odd (Nat.card K))
    (hZ : ∀ x ∈ center (spinGroup Q), ∃ c : K, ∀ v, spinAction Q x v = c • v)
    {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (s t : Bool) :
    F.longSL2 hij s t (-1) ∉ center (spinGroup Q) := by
  intro h
  obtain ⟨c, hc⟩ := hZ _ h
  have hv := hc (F.vec k true)
  rw [T1.spinAction_longSL2 F hij s t (-1),
    (F.toFrame hij s t).La_apply_of_coords_eq_zero (-1)
      (coords_vec_of_ne F hij hki hkj s t true)] at hv
  have hne : F.vec k true ≠ 0 := fun h0 => by
    have h1 := F.polar_vec_not k true
    rw [h0, QuadraticMap.polar_zero_left] at h1
    exact zero_ne_one h1
  have hc1 : c = 1 := by
    have h1 : (c - 1) • F.vec k true = 0 := by rw [sub_smul, one_smul, ← hv, sub_self]
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd h2 hne
  refine T1.spinAction_longSL2_neg_one_ne_one F hij hodd s t (LinearEquiv.ext fun v => ?_)
  rw [hc v, hc1, one_smul]
  rfl

include F in
theorem conclZ_of_frame [Finite K] (hm : 3 ≤ m) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (hrange : (spinAction Q).range ≤ elementaryGroup Q)
    (hZ : ∀ x ∈ center (spinGroup Q), ∃ c : K, ∀ v, spinAction Q x v = c • v) (hQ : Q ≠ 0)
    {t : spinGroup Q} (ht : (t : CliffordAlgebra Q) = -1) : ConclZ p f (spinGroup Q) t := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  have hij : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hki : (⟨2, by omega⟩ : Fin m) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have hkj : (⟨2, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have htZ : t ∈ center (spinGroup Q) := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ht, mul_neg_one, neg_one_mul]
  set u := F.longSL2 hij true true (-1) with hu
  have hx : F.longSL2 hij true false (-1) = t * u := by
    have h1 : F.longSL2 hij true false (-1) = spinGroup.negOne Q hQ * u :=
      T1.longSL2_neg_one_not F hij hQ true true
    have h2 : spinGroup.negOne Q hQ = t := Subtype.ext (by rw [spinGroup.coe_negOne, ht])
    rw [h1, h2]
  have hu2 : orderOf u = 2 := T1.orderOf_longSL2_neg_one F hij hodd true true
  have hx2 : orderOf (t * u) = 2 := hx ▸ T1.orderOf_longSL2_neg_one F hij hodd true false
  have huZ : u ∉ center (spinGroup Q) :=
    longSL2_neg_one_not_mem_center F hodd hZ hij hki hkj true true
  have hxZ : t * u ∉ center (spinGroup Q) :=
    hx ▸ longSL2_neg_one_not_mem_center F hodd hZ hij hki hkj true false
  have hCt : centralizer ({F.longSL2 hij true false (-1)} : Set (spinGroup Q)) =
      centralizer {u} := by
    rw [hx]
    exact T1.centralizer_mul_of_mem_center htZ
  have := T1.finite_range_longSL2 F hij true true
  have := T1.finite_range_longSL2 F hij true false
  have hs₁ := T1.isSLTwoOver_range_longSL2 F hij hK true true
  have hs₂ := T1.isSLTwoOver_range_longSL2 F hij hK true false
  have hZ₁ : (center ↥(F.longSL2 hij true true).range).map
      (F.longSL2 hij true true).range.subtype = zpowers u :=
    T1.map_center_range_longSL2 F hij hp hp2 hK h5 true true
  have hZ₂ : (center ↥(F.longSL2 hij true false).range).map
      (F.longSL2 hij true false).range.subtype = zpowers (t * u) := by
    rw [← hx]
    exact T1.map_center_range_longSL2 F hij hp hp2 hK h5 true false
  have hxJ : t * u ∈ (F.longSL2 hij true false).range := by
    rw [← hx]
    exact MonoidHom.mem_range.mpr ⟨-1, rfl⟩
  refine ⟨u, hu2, huZ, (F.longSL2 hij true true).range, (F.longSL2 hij true false).range,
    T1.isTwoComponentIn_range_longSL2 F hij hp hp2 hK h5 hrange true true,
    hCt ▸ T1.isTwoComponentIn_range_longSL2 F hij hp hp2 hK h5 hrange true false,
    fun h => ?_, MonoidHom.mem_range.mpr ⟨-1, rfl⟩, ?_, hs₁,
    (isQuasisimple_of_isSLTwoOver hp hp2 h5 hs₂).1, ⟨t * u, hxJ, hx2, hxZ⟩,
    ⟨.PSL, 2, (Lemma47.sl2_facts hp hp2 hf h5 hs₂).2.2.1⟩, .inr hxJ⟩
  ·
    rw [h, hZ₂] at hZ₁
    have h1 : u ∈ zpowers (t * u) := hZ₁ ▸ mem_zpowers u
    rcases eq_one_or_eq_of_mem_zpowers hx2 h1 with h2 | h2
    · rw [h2, orderOf_one] at hu2
      exact absurd hu2 (by norm_num)
    · have h3 : (1 : spinGroup Q) = t := mul_right_cancel ((one_mul u).trans h2)
      have h2' : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
      have : Invertible (2 : K) := invertibleOfNonzero h2'
      exact spinGroup.negOne_ne_one Q hQ
        (Subtype.ext (by rw [spinGroup.coe_negOne, ← ht, ← h3]))
  ·
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf] at ha
    have h1 : a ∈ (center ↥(F.longSL2 hij true true).range).map
        (F.longSL2 hij true true).range.subtype :=
      Subgroup.mem_map.mpr ⟨⟨a, ha.1⟩,
        mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp ha.2 g), rfl⟩
    rw [hZ₁] at h1
    rcases eq_one_or_eq_of_mem_zpowers hu2 h1 with h2 | h2
    · rw [h2]
      exact one_mem _
    · exact absurd (h2 ▸ ha.2) huZ

end Frame

theorem smul_of_le_comap {K : Type} [Field K] {σ : Type} [Fintype σ] [DecidableEq σ]
    {Q : QuadraticForm K (σ → K)}
    (hZ : center (spinGroup Q) ≤ (StatedScalars σ K).comap (spinMatrix Q)) :
    ∀ x ∈ center (spinGroup Q), ∃ c : K, ∀ v, spinAction Q x v = c • v := by
  intro x hx
  obtain ⟨c, hc⟩ := hZ hx
  refine ⟨c, fun v => ?_⟩
  rw [← spinMatrix_mulVec, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
  ext a
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

end DA

theorem rowDA : RowDA := by
  constructor
  · intro K _ _ m p f hp hp2 hK h5 hm t ht
    have : NeZero m := ⟨by omega⟩
    obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := K) (by omega : 3 ≤ m)
    exact DA.conclZ_of_frame (plusFrame m K (by omega)) (by omega) hp hp2 hK h5
      (range_spinAction_quadPlus (by omega)).le (DA.smul_of_le_comap (hZ.symm.trans hcomap).le)
      (nondegenerate_quadPlus m K).ne_zero ht
  · intro K _ _ m p f b c hirr hp hp2 hK h5 hm t ht
    obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadMinus hm hirr
    exact DA.conclZ_of_frame (Twisted.minusFrame m b c).toHypFrame (by omega) hp hp2 hK h5
      (range_spinAction_quadMinus hm hirr).le (DA.smul_of_le_comap (hZ.symm.trans hcomap).le)
      (nondegenerate_quadMinus_of_finite m K hirr).ne_zero ht

end CFSG.ComponentClassification.HarrisLit.T1.P54

module

public import CFSG.ClassicalInvolution.RouteD.TWU1Cliff
public import CFSG.ClassicalInvolution.RouteD.TWU1Frame
public import CFSG.ClassicalInvolution.RouteD.GapsFrSpin

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.LieType.Universal.Spin CFSG.LieType.HighestRoot
  CliffordAlgebra
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}

theorem mem_orthogonalGroup_spinAction (x : spinGroup Q) :
    spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v

theorem spinAction_conj_longSL2 (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    (x : spinGroup Q) (A : SL(2, F)) :
    spinAction Q (MulAut.conj x (F₀.longSL2 hij s t A)) =
      ((F₀.toFrame hij s t).map (mem_orthogonalGroup_spinAction x)).La A := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Frame.map_La, spinAction_longSL2]

theorem conj_mem_map_range (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    (x : spinGroup Q) (A : SL(2, F)) :
    MulAut.conj x (F₀.longSL2 hij s t A) ∈
      (F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom :=
  ⟨_, ⟨A, rfl⟩, rfl⟩

theorem map_conj_longSL2_range (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    (x : spinGroup Q) :
    ((F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom).map (spinAction Q) =
      ((F₀.toFrame hij s t).map (mem_orthogonalGroup_spinAction x)).La.range := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    exact ⟨A, (spinAction_conj_longSL2 F₀ hij s t x A).symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, spinAction_conj_longSL2 F₀ hij s t x A⟩

theorem toFrame_map_true_false (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j)
    {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h : (imgPair F₀ i hg).Orth (swapPair (imgPair F₀ j hg))) :
    (F₀.toFrame hij true false).map hg =
      mkFrame (imgPair F₀ i hg) (swapPair (imgPair F₀ j hg)) h := by
  have hP1 : imgPair F₀ i hg = ((F₀.toFrame hij true false).map hg).P := hypPair_ext rfl rfl
  have hP2 : swapPair (imgPair F₀ j hg) = ((F₀.toFrame hij true false).map hg).P' :=
    hypPair_ext rfl rfl
  unfold mkFrame
  generalize (F₀.toFrame hij true false).map hg = Fr at hP1 hP2 ⊢
  cases Fr
  subst hP1 hP2
  rfl

theorem toFrame_map_true_true (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j)
    {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (F₀.toFrame hij true true).map hg = ((F₀.toFrame hij true false).map hg).swap := by
  rw [show (F₀.toFrame hij true true) = (F₀.toFrame hij true false).swap from
    toFrame_not F₀ hij true false]
  rfl


theorem imgPair_orth_of_ne (F₀ : HypFrame Q m) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {i j : Fin m} (hij : i ≠ j) :
    (imgPair F₀ i hg).Orth (imgPair F₀ j hg) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show polar Q (g (F₀.vec i true)) (g (F₀.vec j true)) = 0
    rw [polar_map_of_mem hg]
    exact F₀.polar_vec_of_ne hij true true
  · show polar Q (g (F₀.vec i true)) (g (F₀.vec j false)) = 0
    rw [polar_map_of_mem hg]
    exact F₀.polar_vec_of_ne hij true false
  · show polar Q (g (F₀.vec i false)) (g (F₀.vec j true)) = 0
    rw [polar_map_of_mem hg]
    exact F₀.polar_vec_of_ne hij false true
  · show polar Q (g (F₀.vec i false)) (g (F₀.vec j false)) = 0
    rw [polar_map_of_mem hg]
    exact F₀.polar_vec_of_ne hij false false

theorem diagI_mul_self_sl (i : F) (hi : i * i = -1) : diagI i hi * diagI i hi = -1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, diagI_mul_self, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one])

theorem diagM_mul_self_sl (i : F) (hi : i * i = -1) : diagM i hi * diagM i hi = -1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, diagM_mul_self, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one])

theorem spinAction_chain (F₀ : HypFrame Q m) (x : spinGroup Q) {i₀ i₁ i₂ i₃ : Fin m}
    (h01 : i₀ ≠ i₁) (h12 : i₁ ≠ i₂) (h23 : i₂ ≠ i₃) (i : F) (hi : i * i = -1) :
    spinAction Q (MulAut.conj x (F₀.longSL2 h01 true false (diagI i hi)) *
        MulAut.conj x (F₀.longSL2 h01 true true (diagM i hi)) *
        (MulAut.conj x (F₀.longSL2 h23 true false (diagI i hi)) *
          MulAut.conj x (F₀.longSL2 h23 true true (diagI i hi)))) =
      spinAction Q (MulAut.conj x (F₀.longSL2 h12 true false (-1))) := by
  have hg := mem_orthogonalGroup_spinAction x
  have o01 : (imgPair F₀ i₀ hg).Orth (swapPair (imgPair F₀ i₁ hg)) :=
    orth_swapPair (imgPair_orth_of_ne F₀ hg h01)
  have o12 : (imgPair F₀ i₁ hg).Orth (swapPair (imgPair F₀ i₂ hg)) :=
    orth_swapPair (imgPair_orth_of_ne F₀ hg h12)
  have o23 : (imgPair F₀ i₂ hg).Orth (swapPair (imgPair F₀ i₃ hg)) :=
    orth_swapPair (imgPair_orth_of_ne F₀ hg h23)
  simp only [map_mul, spinAction_conj_longSL2, toFrame_map_true_true]
  rw [toFrame_map_true_false F₀ h01 hg o01, toFrame_map_true_false F₀ h23 hg o23,
    toFrame_map_true_false F₀ h12 hg o12,
    La_neg_one_eq_twinInv_mul i hi (imgPair F₀ i₀ hg) (imgPair F₀ i₁ hg) (imgPair F₀ i₂ hg)
      (imgPair F₀ i₃ hg) o01 o12 o23 (imgPair_orth_of_ne F₀ hg h12)]
  rfl

theorem mul_negOne_comm (hQ : Q ≠ 0) (x : spinGroup Q) :
    x * spinGroup.negOne Q hQ = spinGroup.negOne Q hQ * x := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, spinGroup.coe_negOne, mul_neg_one, neg_one_mul]

theorem conj_negOne (hQ : Q ≠ 0) (x : spinGroup Q) :
    MulAut.conj x (spinGroup.negOne Q hQ) = spinGroup.negOne Q hQ := by
  rw [MulAut.conj_apply, mul_negOne_comm hQ x, mul_assoc, mul_inv_cancel, mul_one]

theorem conj_longSL2_neg_one_mul_twin (hQ : Q ≠ 0) (F₀ : HypFrame Q m) {i j : Fin m}
    (hij : i ≠ j) (s t : Bool) (x : spinGroup Q) :
    MulAut.conj x (F₀.longSL2 hij s t (-1)) * MulAut.conj x (F₀.longSL2 hij s (!t) (-1)) =
      spinGroup.negOne Q hQ := by
  rw [← map_mul, longSL2_neg_one_mul_twin hQ F₀ hij s t, conj_negOne hQ x]

theorem conj_longSL2_mul_self (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    (x : spinGroup Q) (A : SL(2, F)) :
    MulAut.conj x (F₀.longSL2 hij s t A) * MulAut.conj x (F₀.longSL2 hij s t A) =
      MulAut.conj x (F₀.longSL2 hij s t (A * A)) := by
  rw [← map_mul, ← map_mul]

theorem eq_conj_longSL2_neg_one (h2 : (2 : F) ≠ 0) (F₀ : HypFrame Q m) {i j : Fin m}
    (hij : i ≠ j) (s t : Bool) (x : spinGroup Q) {r : spinGroup Q}
    (hr : r ∈ (F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom)
    (hr2 : orderOf r = 2) : r = MulAut.conj x (F₀.longSL2 hij s t (-1)) := by
  obtain ⟨y, hy, rfl⟩ := hr
  have hy2 : orderOf y = 2 := by
    rw [← hr2]
    exact (orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective y).symm
  rw [eq_of_mem_range_longSL2_of_orderOf_eq_two F₀ hij s t h2 hy hy2]
  rfl

end CFSG.ClassicalInvolution.RouteD.TWU

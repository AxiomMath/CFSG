module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEmbed
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL compInd signMat
  commute_signMat_iff)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

structure OSliceW (hd : 4 ≤ d) (w : Fin d → K) (α a : K) : Prop where
  hα : α ≠ 0
  ha : a ≠ 0
  hw4 : ∀ i : Fin 4, w ⟨i, by omega⟩ = α * qW a i

theorem embed4_neg_one (hd : 4 ≤ d) : embed4 K hd (-1) = signMat K wSet := by
  ext i j
  rcases Nat.lt_or_ge (i : ℕ) 4 with hi | hi
  · rcases Nat.lt_or_ge (j : ℕ) 4 with hj | hj
    · rw [embed4_apply_lt hd _ hi hj, signMat, diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp [mem_wSet, hi]
      · have : (⟨i, hi⟩ : Fin 4) ≠ ⟨j, hj⟩ := fun h => hij (Fin.ext (by simpa using h))
        simp [hij, this]
    · rw [embed4_apply_of hd _ (Or.inr hj), signMat, diagonal_apply]
      have hij : i ≠ j := fun h => by rw [h] at hi; omega
      simp [hij]
  · rw [embed4_apply_of hd _ (Or.inl hi), signMat, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp [mem_wSet, show ¬ (i : ℕ) < 4 by omega]
    · simp [hij]

theorem commute_inv_of_commute {n : Type*} [Fintype n] [DecidableEq n]
    {H Hi E : Matrix n n K} (h1 : H * Hi = 1) (h2 : Hi * H = 1) (hc : H * E = E * H) :
    Hi * E = E * Hi := by
  calc Hi * E = Hi * E * (H * Hi) := by rw [h1, Matrix.mul_one]
    _ = Hi * (E * H) * Hi := by simp only [Matrix.mul_assoc]
    _ = Hi * (H * E) * Hi := by rw [hc]
    _ = E * Hi := by rw [← Matrix.mul_assoc Hi H E, h2, Matrix.one_mul]

theorem mem_commutator_of_perfect {G M : Type*} [Group G] [Group M] (hG : Group.IsPerfect G)
    (f : G →* M) {I : Subgroup M} (hf : ∀ g, f g ∈ I) (g : G) : f g ∈ ⁅I, I⁆ := by
  have h1 : (⊤ : Subgroup G).map f ≤ ⁅I, I⁆ := by
    rw [← hG.commutator_eq_top, _root_.commutator_def, map_commutator]
    exact commutator_mono (fun _ ⟨x, _, hx⟩ => hx ▸ hf x) (fun _ ⟨x, _, hx⟩ => hx ▸ hf x)
  exact h1 ⟨g, mem_top g, rfl⟩

variable (K) in
@[expose] def oSlice (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0) :
    SL(2, K) →* GL (Fin d) K :=
  (embedGL4 K hd).comp ((Subgroup.subtype _).comp (qLambda h2 ha))

theorem coe_oSlice (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0) (g : SL(2, K)) :
    ((oSlice K h2 hd ha g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      embed4 K hd (qLamMat h2 ha g) := rfl

theorem oSlice_injective (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0) :
    Function.Injective (oSlice K h2 hd ha) :=
  (embedGL4_injective hd).comp ((Subgroup.subtype_injective _).comp (qLambda_injective h2 ha))

theorem oSlice_mem_oIsoBlock (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) (g : SL(2, K)) :
    oSlice K h2 hd hW.ha g ∈ oIsoBlock K hw wSet := by
  rw [mem_oIsoBlock_iff]
  exact ⟨embedGL4_mem_iso hd hw hW.ha hW.hw4 (qLambda h2 hW.ha g).2,
    embed4_support hd _⟩

theorem oSlice_mem_oBlock [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) (g : SL(2, K)) :
    oSlice K h2 hd hW.ha g ∈ oBlock K hw wSet :=
  mem_commutator_of_perfect (CatalogueBGeneralLinear.specialLinear_perfect 2 K le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))) _ (oSlice_mem_oIsoBlock h2 hd hw hW) g

theorem oSlice_mem_derived [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) (g : SL(2, K)) :
    oSlice K h2 hd hW.ha g ∈ matrixDerived (oQ (diagGL hw)) := by
  rw [matrixDerived_oQ h2 _ (diagGL_transpose hw)]
  exact oBlock_le hw wSet (oSlice_mem_oBlock h2 hK4 hd hw hW g)

@[expose] def oSliceH [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) :
    SL(2, K) →* matrixDerived (oQ (diagGL hw)) :=
  (oSlice K h2 hd hW.ha).codRestrict _ (oSlice_mem_derived h2 hK4 hd hw hW)

theorem coe_oSliceH [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) (g : SL(2, K)) :
    ((oSliceH h2 hK4 hd hw hW g : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) =
      oSlice K h2 hd hW.ha g := rfl

theorem oSliceH_injective [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) :
    Function.Injective (oSliceH h2 hK4 hd hw hW) := fun _ _ h =>
  oSlice_injective h2 hd hW.ha (congrArg Subtype.val h)

theorem blk4_mem_iso (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {α a : K} (hW : OSliceW hd w α a) {h : GL (Fin d) K}
    (hh : h ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hc : (h : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * (h : Matrix (Fin d) (Fin d) K)) :
    ∃ X : CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero hW.ha)),
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blk4 hd h ∧
      ((X⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        blk4 hd ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have hhi : (h : Matrix (Fin d) (Fin d) K) * ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hih : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (h : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hci : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    commute_inv_of_commute hhi hih hc
  have e1 := (mul_embed4_mul h2 hd hhi hc hci 1).2
  have e2 := (mul_embed4_mul h2 hd hih hci hc 1).2
  have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 hh
  rw [coe_diagGL] at hiso
  refine ⟨⟨⟨blk4 hd h, blk4 hd ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K), e1, e2⟩, ?_⟩,
    rfl, rfl⟩
  rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL]
  exact blk4_isometry h2 hd hW.hα hW.hw4 hc hiso

theorem conj_oSlice_of_rho (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0)
    {h : GL (Fin d) K}
    (hc : (h : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * (h : Matrix (Fin d) (Fin d) K))
    {X : CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha))}
    (hX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blk4 hd h)
    (hXi : ((X⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk4 hd ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    {z : equalDeterminants K} (hz : qGamma h2 ha X = rho z) (g : SL(2, K)) :
    h * oSlice K h2 hd ha g * h⁻¹ = oSlice K h2 hd ha (conjSL z.val.1 g) := by
  have hhi : (h : Matrix (Fin d) (Fin d) K) * ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hih : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (h : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hci : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    commute_inv_of_commute hhi hih hc
  have key : X * qLambda h2 ha g * X⁻¹ = qLambda h2 ha (conjSL z.val.1 g) := by
    apply qGamma_injective h2 ha
    rw [map_mul, map_mul, map_inv, qGamma_qLambda, qGamma_qLambda, hz,
      rho_mul_leftMul_mul_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_oSlice, coe_oSlice,
    (mul_embed4_mul h2 hd hhi hc hci _).1, ← hX, ← hXi]
  congr 1
  have := congrArg (fun Y : CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha)) =>
    ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) key
  simpa only [Subgroup.coe_mul, Units.val_mul, coe_qLambda, Subgroup.coe_inv] using this

end CFSG.ComponentClassification.Burgoyne.O

module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceDef

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL compInd signMat
  commute_signMat_iff)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

theorem blk4_mul (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {h h' : Matrix (Fin d) (Fin d) K}
    (hc : h * embed4 K hd (-1) = embed4 K hd (-1) * h)
    (hc' : h' * embed4 K hd (-1) = embed4 K hd (-1) * h') :
    blk4 hd (h * h') = blk4 hd h * blk4 hd h' := by
  have e1 := eq_reindex_fromBlocks h2 hd hc
  have e2 := eq_reindex_fromBlocks h2 hd hc'
  conv_lhs => rw [e1, e2, ← map_mul, fromBlocks_multiply]
  rw [blk4, AlgEquiv.symm_apply_apply, toBlocks_fromBlocks₁₁]
  simp

theorem commute_embed4_of_mem (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {X : GL (Fin d) K} (hX : X ∈ oIsoBlock K hw wSet) :
    (X : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * (X : Matrix (Fin d) (Fin d) K) := by
  rw [embed4_neg_one]
  exact (commute_signMat_of_mem_oIsoBlock h2 hw (Or.inl rfl) hX).symm

theorem blk4_mul_inv (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {X : GL (Fin d) K} (hX : X ∈ oIsoBlock K hw wSet) :
    blk4 hd (X : Matrix (Fin d) (Fin d) K) *
      blk4 hd ((X⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
  rw [← blk4_mul h2 hd (commute_embed4_of_mem h2 hd hw hX)
    (commute_embed4_of_mem h2 hd hw (inv_mem hX)), ← Units.val_mul, mul_inv_cancel,
    Units.val_one, ← embed4_one hd, blk4_embed4]

theorem blk4_inv_mul (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {X : GL (Fin d) K} (hX : X ∈ oIsoBlock K hw wSet) :
    blk4 hd ((X⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      blk4 hd (X : Matrix (Fin d) (Fin d) K) = 1 := by
  rw [← blk4_mul h2 hd (commute_embed4_of_mem h2 hd hw (inv_mem hX))
    (commute_embed4_of_mem h2 hd hw hX), ← Units.val_mul, inv_mul_cancel,
    Units.val_one, ← embed4_one hd, blk4_embed4]

@[expose] def oBlkHom (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {α a : K} (hW : OSliceW hd w α a) :
    oIsoBlock K hw wSet →* CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero hW.ha)) where
  toFun X := ⟨⟨blk4 hd ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K),
      blk4 hd (((X : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K),
      blk4_mul_inv h2 hd hw X.2, blk4_inv_mul h2 hd hw X.2⟩, by
    rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL]
    have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
      (oIsoBlock_le hw wSet X.2)
    rw [coe_diagGL] at hiso
    exact blk4_isometry h2 hd hW.hα hW.hw4 (commute_embed4_of_mem h2 hd hw X.2) hiso⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change blk4 hd 1 = 1
    rw [← embed4_one hd, blk4_embed4]
  map_mul' X Y := by
    apply Subtype.ext
    apply Units.ext
    change blk4 hd (((X : GL (Fin d) K) * Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
    rw [Units.val_mul]
    exact blk4_mul h2 hd (commute_embed4_of_mem h2 hd hw X.2)
      (commute_embed4_of_mem h2 hd hw Y.2)

theorem coe_oBlkHom (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {α a : K} (hW : OSliceW hd w α a) (X : oIsoBlock K hw wSet) :
    ((oBlkHom h2 hd hw hW X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk4 hd ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := rfl

theorem coe_oBlkHom_inv (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {α a : K} (hW : OSliceW hd w α a) (X : oIsoBlock K hw wSet) :
    (((oBlkHom h2 hd hw hW X : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk4 hd (((X : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := rfl

theorem conj_oSlice_of_mem (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {α a : K} (hW : OSliceW hd w α a) (X : oIsoBlock K hw wSet) {z : equalDeterminants K}
    (hz : qGamma h2 hW.ha (oBlkHom h2 hd hw hW X) = rho z) (g : SL(2, K)) :
    (X : GL (Fin d) K) * oSlice K h2 hd hW.ha g * (X : GL (Fin d) K)⁻¹ =
      oSlice K h2 hd hW.ha (conjSL z.val.1 g) :=
  conj_oSlice_of_rho h2 hd hW.ha (commute_embed4_of_mem h2 hd hw X.2)
    (coe_oBlkHom h2 hd hw hW X) (coe_oBlkHom_inv h2 hd hw hW X) hz g

theorem oBlock_le_normalizer (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) :
    oBlock K hw wSet ≤ normalizer ((oSlice K h2 hd hW.ha).range : Set (GL (Fin d) K)) := by
  have hc : ∀ X ∈ oIsoBlock K hw wSet, ∀ Y ∈ oIsoBlock K hw wSet, ∀ g,
      ⁅X, Y⁆ * oSlice K h2 hd hW.ha g * ⁅X, Y⁆⁻¹ ∈ (oSlice K h2 hd hW.ha).range := by
    intro X hX Y hY g
    set X' : oIsoBlock K hw wSet := ⟨X, hX⟩
    set Y' : oIsoBlock K hw wSet := ⟨Y, hY⟩
    have hmem := commutator_mem_leftRightImage (qGamma h2 hW.ha (oBlkHom h2 hd hw hW X'))
      (qGamma h2 hW.ha (oBlkHom h2 hd hw hW Y'))
    rw [← map_commutatorElement, ← map_commutatorElement] at hmem
    obtain ⟨z, hz⟩ := hmem
    have e := conj_oSlice_of_mem h2 hd hw hW ⁅X', Y'⁆ hz.symm g
    exact ⟨_, e.symm⟩
  rw [oBlock, Subgroup.commutator_le]
  intro X hX Y hY
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, rfl⟩
    exact hc X hX Y hY x
  · intro hg
    obtain ⟨x, hx⟩ := hg
    have e := hc Y hY X hX x
    have e' : ⁅Y, X⁆ * oSlice K h2 hd hW.ha x * ⁅Y, X⁆⁻¹ = g := by
      rw [hx, ← commutatorElement_inv X Y]
      group
    rwa [e'] at e

theorem exists_rho_of_odd (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {α a : K} (hW : OSliceW hd w α a) (X : oIsoBlock K hw wSet) {m : ℕ} (hm : Odd m)
    (hXm : X ^ m = 1) : ∃ z, qGamma h2 hW.ha (oBlkHom h2 hd hw hW X) = rho z := by
  have h1 : qGamma h2 hW.ha (oBlkHom h2 hd hw hW X) ^ m = 1 := by
    rw [← map_pow, ← map_pow, hXm, map_one, map_one]
  obtain ⟨z, hz⟩ := mem_leftRightImage_of_odd hm h1
  exact ⟨z, hz.symm⟩

end CFSG.ComponentClassification.Burgoyne.O

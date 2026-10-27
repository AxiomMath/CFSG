module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three5
public import CFSG.RankThree.PartOne.KE6.E8T3Stab
public import CFSG.RankThree.PartOne.KE6.E8T3Check
public import CFSG.LocalAnalysis.StandardType.E8SevenLayerFamily
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TwoGroupExtension
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.GL83PartI.I_22_6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Norm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Quot
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Lift
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KLR
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec charVal charVal_mulVec charVal_smul_col
  mem_rootKernel)

open scoped Matrix MatrixGroups

section Certs

theorem weylMatrix_e8T3We_map_eq_smul {p : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ((weylMatrix (e8T3We ε)).map (Int.cast : ℤ → ZMod p)) =
      (ε : ZMod p) • ((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)) := by
  rw [weylMatrix_e8T3We hε]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem dualAction_e8T3We {p : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (z : Fin Tag.E8.rank → ZMod p) :
    ((weylMatrix (e8T3We ε)).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ z =
      (ε : ZMod p) • (((weylMatrix e8T3W).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ z) := by
  rw [weylMatrix_e8T3We_map_eq_smul hε, Matrix.transpose_smul, Matrix.smul_mulVec,
    weylMatrix_e8T3W]

theorem e8T3W_smul_mem_rootKernel {p : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0)
    {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ rootKernel (e8T3XColumn ε (q : ZMod p))) :
    e8T3W • α ∈ rootKernel (e8T3XColumn ε (q : ZMod p)) := by
  have hε2 : (ε : ZMod p) * (ε : ZMod p) = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨hαr, hα0⟩ := mem_rootKernel.1 hα
  have hWmap : ((weylMatrix e8T3W).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
      e8T3XColumn ε (q : ZMod p) =
      ((ε : ZMod p) * (q : ZMod p)) • e8T3XColumn ε (q : ZMod p) := by
    have h := e8T3XColumn_eigen (p := p) hε hq
    rw [dualAction_e8T3We hε] at h
    calc ((weylMatrix e8T3W).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
        e8T3XColumn ε (q : ZMod p)
        = (ε : ZMod p) • ((ε : ZMod p) • (((weylMatrix e8T3W).map
            (Int.cast : ℤ → ZMod p)).transpose *ᵥ e8T3XColumn ε (q : ZMod p))) := by
          rw [smul_smul, hε2, one_smul]
      _ = (ε : ZMod p) • ((q : ZMod p) • e8T3XColumn ε (q : ZMod p)) := by rw [h]
      _ = ((ε : ZMod p) * (q : ZMod p)) • e8T3XColumn ε (q : ZMod p) := by rw [smul_smul]
  refine mem_rootKernel.2 ⟨IsRoot.smul hαr _, ?_⟩
  have h1 : charVal (e8T3XColumn ε (q : ZMod p)) (e8T3W • α) =
      charVal (((weylMatrix e8T3W).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
        e8T3XColumn ε (q : ZMod p)) α := by
    rw [← weylMatrix_mulVec, ← charVal_mulVec]
  rw [h1, hWmap, charVal_smul_col, hα0, mul_zero]

theorem exists_conj_rootKernel_e8T3XColumn_eq_e6Nodes {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hpq : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * (q : ℤ) + 1) :
    ∃ u : WeylGroup Tag.E8,
      (fun γ => u • γ) '' rootKernel (e8T3XColumn ε (q : ZMod p)) =
        parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0 := by
    have h : (((q : ℤ) ^ 2 + ε * (q : ℤ) + 1 : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hpq
    push_cast at h
    exact h
  have hz0 : e8T3XColumn ε (q : ZMod p) ≠ 0 := e8T3XColumn_ne_zero hp
  have hU : ¬ p ∣ Nat.card (dualWeylStabilizer (e8T3XColumn ε (q : ZMod p))) :=
    e8T3_dualStab_prime hp hp3 hε hpq hz0 (e8T3XColumn_eigen hε hq)
  obtain ⟨u, J, hΦJ, hJne⟩ :=
    exists_smul_rootKernel_eq_parabolicRoots_of_card (e8T3XColumn ε (q : ZMod p)) hU
  set J' : Finset (Fin Tag.E8.rank) := Finset.univ.filter (fun i => i ∈ J) with hJ'def
  have hJJ' : (↑J' : Set (Fin Tag.E8.rank)) = J := by
    ext i
    simp [hJ'def]
  have hJ'ne : J' ≠ Finset.univ := fun h1 => hJne hz0 (by rw [← hJJ', h1]; simp)
  have hΦJ' : (fun γ => u • γ) '' rootKernel (e8T3XColumn ε (q : ZMod p)) =
      parabolicRoots Tag.E8 (↑J' : Set (Fin Tag.E8.rank)) := by
    rw [hJJ']
    exact hΦJ
  have hkerW : ∀ α ∈ rootKernel (e8T3XColumn ε (q : ZMod p)),
      e8T3W • α ∈ rootKernel (e8T3XColumn ε (q : ZMod p)) :=
    fun α hα => e8T3W_smul_mem_rootKernel (p := p) hε hq hα
  have hmaps : ∀ β ∈ parabolicRoots Tag.E8 (↑J' : Set (Fin Tag.E8.rank)),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (↑J' : Set (Fin Tag.E8.rank)) := by
    intro β hβ
    rw [← hΦJ'] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e8T3W • α, hkerW α hα, by rw [mul_smul, mul_smul, inv_smul_smul]⟩
  have hrel : ∀ x : Fin Tag.E8.rank → ℤ,
      (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0 :=
    fun x => rel_conj e8T3W_rel u x
  have hsupp : J' ∈ e8T3Supports := e8T3_supports hJ'ne hrel hmaps
  have hcardJ : e8PhiCard J' = 72 := by
    rw [← ncard_parabolicRoots_E8 J', ← hΦJ',
      Set.ncard_image_of_injective _ (MulAction.injective u)]
    exact ncard_rootKernel_e8T3XColumn hp hp3 hε hq
  rcases e8T3_supports_of_card_seven J' hsupp (Or.inr hcardJ) with h | h
  · exact ⟨u, by rw [hΦJ', h, e8T3_coe_e6]⟩
  · exfalso
    have h30 : e8PhiCard ({1, 2, 3, 4, 6, 7} : Finset (Fin Tag.E8.rank)) = 30 := by
      decide +kernel
    rw [h] at hcardJ
    omega

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

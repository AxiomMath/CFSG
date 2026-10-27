module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmM2
public import CFSG.ClassicalInvolution.Q3.TA3FrameU4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Out

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks UnitaryOut UnitaryConj
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem M2.twin_false_u4Ne3 {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hP : PerpHypS n Y R S t)
    (hF : SmallU4Ne3 ↥(genFittingFStar Y)) : False := by
  haveI := hP.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot hP.core.nonab
  obtain ⟨p, f, hp, hp2, hf, h8, h3, hm⟩ := hF
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psu hm
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨-, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
  have : Finite K := h.finite
  have htN : t ∈ genFittingFStar Y := M2.twin_mem_of_noQ8Outer hP hC
    (Q5U4.noQ8Outer_statedPSU h hp2 |> fun hO => noQ8Outer_of_mulEquiv e hO)
  have hz : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hP.core.datum.order
  have hsimple := Frame.FU4.isSimpleGroup_psu4 h.prime (by rw [h.card, ← pow_mul, mul_comm])
  rcases Q5U4.inv_split h hp2 h8 hz with ⟨X, hX, hXX, h1, hm1⟩ | ⟨hq, X, hX, hXX⟩
  · obtain ⟨Rf, s, hs0, -, hR, hXR⟩ := Q5U4.exists_frame_t2 h hp2 X hXX h1 hm1
    have h4 : 4 ≤ Nat.card h.fixedField := by rw [h.card_fixedField]; omega
    exact M2.twin_false_of_block hP e htN hX.symm h4
      ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)) (Frame.FU4.injective_inlU h hR)
      (Frame.FU4.injective_inrU h hR) (Q5U4.range_bdHomU_le_centralizer h hR hXR)
      (Subgroup.isPerfect_iff.mp (Q5U4.isPerfect_range_bdHomU h hR (by omega)))
      (fun M hM hMp => Q5U4.le_range_bdHomU_of_perfect h hR hp2 hs0 hXR hM hMp)
      (Q5U4.noQ8Fix_t2 h hp2 hs0 hR)
  · obtain ⟨P, l, hP', hl, -, hXP⟩ := Q5U4.exists_pair_frame h hp2 hq X hXX
    have hl0 : l ≠ 0 := by
      rintro rfl
      norm_num at hl
    let H₀ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)) :=
      ((QuotientGroup.mk' (scal p f K)).comp (Q5U4.pairHom h hP')).range
    have : IsSimpleGroup H₀ := Q5U4.isSimpleGroup_range_pairHom h hP'
    have : Group.IsPerfect H₀ := Q5U4.isPerfect_range_pairHom h hP'
    exact M2.twin_false_of_simple hP e htN hX.symm (H := H₀)
      (Q5U4.range_pairHom_le_centralizer h hP' hXP)
      (fun M hM hMp => Q5U4.le_range_pairHom_of_perfect h hP' hp2 hl0 hXP hM hMp)
      (Q5U4.noQ8Fix_pair h hP' hp2)

theorem leaf_u4Ne3 {n : ℕ} : TwinLeafS n SmallU4Ne3 :=
  TwinLeafS.of_no fun _ _ _ _ _ _ hP _ hF => M2.twin_false_u4Ne3 hP hF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

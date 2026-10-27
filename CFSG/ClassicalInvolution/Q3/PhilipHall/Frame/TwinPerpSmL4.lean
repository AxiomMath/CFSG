module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmM2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL HBlocks StabL
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem M2.twin_false_l4Ne3 {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypS n Y R S t)
    (hF : SmallL4Ne3 ↥(genFittingFStar Y)) : False := by
  haveI := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  obtain ⟨p, f, hp, hp2, hf, h8, h3, hm⟩ := hF
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psl hm
  let := Fintype.ofFinite K
  let e : ↥(genFittingFStar Y) ≃* projectiveSL 4 K := e₀.trans
    ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K))
  obtain ⟨hodd, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
  have hfo : Odd f := Q5L4.odd_of_pow_mod_eight_ne_one (hp.odd_of_ne_two hp2) h8
  have hKodd : Odd (Nat.card K) := hK ▸ hodd
  have hchar : ringChar K ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hKodd
    omega
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have h4' : 4 ≤ Nat.card K := by rw [hK]; omega
  have hcard : 4 ≤ Fintype.card K := by rw [← Nat.card_eq_fintype_card]; exact h4'
  have htN : t ∈ genFittingFStar Y := M2.twin_mem_of_noQ8Outer h hC
    (noQ8Outer_of_mulEquiv e (Q5L4.noQ8Outer_projectiveSL hp hK hfo))
  have hz : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact h.core.datum.order
  rcases Q5L4.inv_split hchar (by rw [hK]; exact h8) hz with ⟨X, hX, P, hXP⟩ | ⟨h4K, g, hg, hgg⟩
  · have := Q5L4.isPerfect_range_bdHom hcard P
    exact M2.twin_false_of_block h e htN hX.symm h4' ((proj 4 K).comp (bdHom P))
      (Frame.FL4.injective_inl P) (Frame.FL4.injective_inr P)
      (Q5L4.range_bdHom_le_centralizer P hXP) (Subgroup.isPerfect_iff.mp this)
      (fun M hM hMp => Q5L4.le_range_bdHom_of_perfect h2 P X hXP hM hMp)
      (Q5L4.noQ8Fix_t2 h4 hp hK hfo P)
  · obtain ⟨c, hc⟩ := Q5L4.exists_conj_to_k₀ h4K hgg
    let e' : ↥(genFittingFStar Y) ≃* projectiveSL 4 K := e.trans (MulAut.conj (proj 4 K c))
    have hu : e' ⟨t, htN⟩ = proj 4 K k₀ := by
      rw [show e' ⟨t, htN⟩ = MulAut.conj (proj 4 K c) (e ⟨t, htN⟩) from rfl, ← hg, hc]
    obtain ⟨hs, hpf⟩ := Q5L4.J₀_eq_L h4K
    exact M2.twin_false_of_simple h e' htN hu Q5L4.J₀_le_centralizer
      (fun M hM hMp => le_J₀ hM hMp) (Q5L4.noQ8Fix_Nc h4K hp hK)

theorem leaf_l4Ne3 {n : ℕ} : TwinLeafS n SmallL4Ne3 :=
  TwinLeafS.of_no fun _ _ _ _ _ _ hP _ hF => M2.twin_false_l4Ne3 hP hF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

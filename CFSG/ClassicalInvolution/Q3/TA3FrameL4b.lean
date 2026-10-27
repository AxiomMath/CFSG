module

public import CFSG.ClassicalInvolution.Q3.TA3FrameL4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL TBlocks HBlocks StabL
open scoped MatrixGroups

variable {K : Type} [Field K] [Fintype K] {p f : ℕ}

omit [Fintype K] in
theorem ringChar_ne_two_of_card (hp : p.Prime) (hp2 : p ≠ 2) [Finite K]
    (hK : Nat.card K = p ^ f) : ringChar K ≠ 2 := by
  let := Fintype.ofFinite K
  have hKodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  rw [Ne, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
  obtain ⟨k, hk⟩ := hKodd
  omega

theorem layerExcludesQ8_psl4_t2 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hf : Odd f) (h5 : 5 ≤ p ^ f) (P : GL (Fin 4) K) {Y : SL(4, K)}
    (hYP : (Y : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) :
    LayerExcludesQ8 (projectiveSL 4 K) (proj 4 K Y) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card hp hp2 hK)
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have h4' : 4 ≤ Nat.card K := by omega
  have hcard : 4 ≤ Fintype.card K := by rw [← Nat.card_eq_fintype_card]; exact h4'
  exact FL4.layerExcludesQ8_of_block (FL4.center_eq_bot h4') h4' ((proj 4 K).comp (bdHom P))
    (FL4.injective_inl P) (FL4.injective_inr P) (Q5L4.range_bdHom_le_centralizer P hYP)
    (Subgroup.isPerfect_iff.mp (Q5L4.isPerfect_range_bdHom hcard P))
    (fun M hM hMp => Q5L4.le_range_bdHom_of_perfect h2 P Y hYP hM hMp)
    (Q5L4.noQ8Fix_t2 h4 hp hK hf P)

theorem layerExcludesQ8_psl4_Nc (hF : Fintype.card K % 4 = 3) (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    LayerExcludesQ8 (projectiveSL 4 K) (proj 4 K k₀) := by
  obtain ⟨hs, hpf⟩ := Q5L4.J₀_eq_L hF
  exact FL4.layerExcludesQ8_of_simple (FL4.center_eq_bot (by omega)) Q5L4.J₀_le_centralizer
    (fun M hM hMp => le_J₀ hM hMp) (Q5L4.noQ8Fix_Nc hF hp hK)

theorem layerExcludesQ8_l4 {X : Type} [Group X] (hp : p.Prime) (hp2 : p ≠ 2)
    (h8 : p ^ f % 8 ≠ 1) (h5 : 5 ≤ p ^ f) (hm : LieModel X .PSL 4 p f) (t : X)
    (ht : orderOf t = 2) : LayerExcludesQ8 X t := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psl hm
  let := Fintype.ofFinite K
  let e : X ≃* projectiveSL 4 K := e₀.trans
    ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K))
  refine LayerExcludesQ8.of_mulEquiv e ?_
  have hfo : Odd f := Q5L4.odd_of_pow_mod_eight_ne_one (hp.odd_of_ne_two hp2) h8
  have hz : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  rcases Q5L4.inv_split (ringChar_ne_two_of_card hp hp2 hK) (by rw [hK]; exact h8) hz with
    ⟨Y, hY, P, hYP⟩ | ⟨h4K, g, hg, hgg⟩
  · rw [← hY]
    exact layerExcludesQ8_psl4_t2 hp hp2 hK hfo h5 P hYP
  · obtain ⟨h, hh⟩ := Q5L4.exists_conj_to_k₀ h4K hgg
    rw [← hg]
    refine LayerExcludesQ8.of_mulEquiv (MulAut.conj (proj 4 K h)) ?_
    rw [hh]
    exact layerExcludesQ8_psl4_Nc h4K hp hK h5

end CFSG.ClassicalInvolution.Q3.TA3.Frame

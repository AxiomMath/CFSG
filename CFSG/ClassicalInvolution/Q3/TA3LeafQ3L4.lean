module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4T2c
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL HBlocks StabL

theorem noQ8Datum_l43 : ∀ (F : Type) [Group F], LieModel F .PSL 4 3 1 → NoQ8Datum F := by
  intro F _ hm G _ _ N _ ⟨eN⟩ hC _ R S t hD _
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psl hm
  let := Fintype.ofFinite K
  let e : ↥N ≃* projectiveSL 4 K := eN.trans (e₀.trans
    ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K)))
  have hK3 : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK, pow_one]
  have hchar : ringChar K ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, hK3]
    decide
  have htN : t ∈ N := TightDatum.mem_of_noQ8Outer hD hC
    (noQ8Outer_of_mulEquiv e (Q5L4.noQ8Outer_projectiveSL Nat.prime_three hK odd_one))
  have hz : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hD.order
  rcases Q5L4.inv_split hchar (by rw [hK]; decide) hz with ⟨X, hX, P, hXP⟩ | ⟨h4K, g, hg, hgg⟩
  · exact Q3L4.false_t2_L43 hK3 hXP hD hC e htN hX.symm
  · obtain ⟨h, hh⟩ := Q5L4.exists_conj_to_k₀ h4K hgg
    let e' : ↥N ≃* projectiveSL 4 K := e.trans (MulAut.conj (proj 4 K h))
    have hu : e' ⟨t, htN⟩ = proj 4 K k₀ := by
      rw [show e' ⟨t, htN⟩ = MulAut.conj (proj 4 K h) (e ⟨t, htN⟩) from rfl, ← hg, hh]
    obtain ⟨-, hpf⟩ := Q5L4.J₀_eq_L h4K
    exact TightDatum.false_of_model hD hC e' htN hu (J₀ K) Q5L4.J₀_le_centralizer
      (fun M hM hMp => le_J₀ hM hMp) (Q5L4.noOddNormal_J₀ h4K)
      (Q5L4.noQ8Fix_Nc h4K Nat.prime_three hK)

theorem smallSimpleLeaf_l43 : SmallSimpleLeaf fun F _ => LieModel F .PSL 4 3 1 :=
  smallSimpleLeaf_of_noQ8Datum noQ8Datum_l43

end CFSG.ClassicalInvolution.Q3.TA3

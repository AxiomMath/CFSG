module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4T2c

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL HBlocks StabL

theorem noDatum4_l4Ne3 : ∀ (F : Type) [Group F], SmallL4Ne3 F → NoDatum4 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h8, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC _ R S t hD
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psl hm
  let := Fintype.ofFinite K
  let e : ↥N ≃* projectiveSL 4 K := eN.trans (e₀.trans
    ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K)))
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
  have hcard : 4 ≤ Fintype.card K := by rw [← Nat.card_eq_fintype_card, hK]; omega
  have htN : t ∈ N := TightDatum.mem_of_noQ8Outer hD hC
    (noQ8Outer_of_mulEquiv e (Q5L4.noQ8Outer_projectiveSL hp hK hfo))
  have hz : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hD.order
  rcases Q5L4.inv_split hchar (by rw [hK]; exact h8) hz with ⟨X, hX, P, hXP⟩ | ⟨h4K, g, hg, hgg⟩
  · have := Q5L4.isPerfect_range_bdHom hcard P
    exact TightDatum.false_of_model hD hC e htN hX.symm ((proj 4 K).comp (bdHom P)).range
      (Q5L4.range_bdHom_le_centralizer P hXP)
      (fun M hM hMp => Q5L4.le_range_bdHom_of_perfect h2 P X hXP hM hMp)
      (Q5L4.noOddNormal_range_bdHom ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hK⟩ P)
      (Q5L4.noQ8Fix_t2 h4 hp hK hfo P)
  · obtain ⟨h, hh⟩ := Q5L4.exists_conj_to_k₀ h4K hgg
    let e' : ↥N ≃* projectiveSL 4 K := e.trans (MulAut.conj (proj 4 K h))
    have hu : e' ⟨t, htN⟩ = proj 4 K k₀ := by
      rw [show e' ⟨t, htN⟩ = MulAut.conj (proj 4 K h) (e ⟨t, htN⟩) from rfl, ← hg, hh]
    obtain ⟨-, hpf⟩ := Q5L4.J₀_eq_L h4K
    exact TightDatum.false_of_model hD hC e' htN hu (J₀ K) Q5L4.J₀_le_centralizer
      (fun M hM hMp => le_J₀ hM hMp) (Q5L4.noOddNormal_J₀ h4K) (Q5L4.noQ8Fix_Nc h4K hp hK)

theorem smallLeafR_l4Ne3 {r : ℕ} : SmallLeafR r SmallL4Ne3 :=
  SmallLeafR.of_noDatum4 noDatum4_l4Ne3

theorem noDatum4_l43 : ∀ (F : Type) [Group F], LieModel F .PSL 4 3 1 → NoDatum4 F := by
  intro F _ hm G _ _ N _ ⟨eN⟩ hC _ R S t hD
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

theorem smallLeafR_l43 {r : ℕ} : SmallLeafR r (fun F _ => LieModel F .PSL 4 3 1) :=
  SmallLeafR.of_noDatum4 noDatum4_l43

end CFSG.CGT.PushingUpLit.SolKNA.R4

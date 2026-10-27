module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4Out
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4Nc
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4Lin
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4T2

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL HBlocks StabL

namespace Q5L4

theorem odd_of_pow_mod_eight_ne_one {p f : ℕ} (hp : Odd p) (h : p ^ f % 8 ≠ 1) : Odd f := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | hf
  · exfalso
    apply h
    have hm : Odd (p ^ k) := hp.pow
    rw [pow_add, Nat.mul_mod]
    have h8 : p ^ k % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hodd8 : p ^ k % 2 = 1 := Nat.odd_iff.mp hm
    interval_cases hr : p ^ k % 8 <;> omega
  · exact hf

variable {K : Type} [Field K] [Fintype K]

theorem inv_split (hK : ringChar K ≠ 2) (h8 : Nat.card K % 8 ≠ 1) {z : projectiveSL 4 K}
    (hz : orderOf z = 2) :
    (∃ X : SpecialLinearGroup (Fin 4) K, proj 4 K X = z ∧ ∃ P : GL (Fin 4) K,
      (X : Matrix (Fin 4) (Fin 4) K) * P = P * X1 (1 : K)) ∨
    (Fintype.card K % 4 = 3 ∧ ∃ g : SpecialLinearGroup (Fin 4) K, proj 4 K g = z ∧
      (g : Matrix (Fin 4) (Fin 4) K) * g = -1) := by
  obtain ⟨g, rfl⟩ := proj_surjective 4 K z
  have hg2 : proj 4 K (g * g) = 1 := by
    rw [map_mul, ← sq, ← hz, pow_orderOf_eq_one]
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hg2)
  have hX : (g : Matrix (Fin 4) (Fin 4) K) * g = (c : K) • 1 := by
    have hc' : (g : Matrix (Fin 4) (Fin 4) K) * g = scalar (Fin 4) (c : K) := hc
    rw [hc', scalar_apply, smul_one_eq_diagonal]
  have hns : ∀ a : K, (g : Matrix (Fin 4) (Fin 4) K) ≠ a • 1 := by
    intro a ha
    have hdet : a ^ 4 = 1 := by
      have h1 := g.2
      rw [ha, det_smul, det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hdet
    have h1 : proj 4 K g = 1 := proj_eq_one_iff.2 ⟨Units.mk0 a ha0,
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet, Units.val_one]), by
        rw [ha, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]⟩
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  rcases InvClassL.classify_inv hK hX c.ne_zero hns with
    ⟨l, hl0, -, hdet, P, hP⟩ | ⟨l, hl0, -, hdet, -⟩ | ⟨hsq, P, hP⟩
  · left
    set X : SpecialLinearGroup (Fin 4) K := ⟨l⁻¹ • (g : Matrix (Fin 4) (Fin 4) K), hdet⟩
      with hXdef
    have hXm : (X : Matrix (Fin 4) (Fin 4) K) = l⁻¹ • (g : Matrix (Fin 4) (Fin 4) K) := rfl
    refine ⟨X, ?_, P, by rw [hXm]; exact hP⟩
    have hl4 : l⁻¹ ^ 4 = 1 := by
      have h1 := hdet
      rw [det_smul, g.2, mul_one, Fintype.card_fin] at h1
      exact h1
    have hgi : ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * g = 1 :=
      congrArg (fun y : SpecialLinearGroup (Fin 4) K => (y : Matrix (Fin 4) (Fin 4) K))
        (inv_mul_cancel g)
    refine (proj_eq_proj_iff.mpr (mem_scalars.mpr ⟨Units.mk0 l⁻¹ (inv_ne_zero hl0),
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hl4, Units.val_one]), ?_⟩)).symm
    rw [Matrix.SpecialLinearGroup.coe_mul, hXm, Units.val_mk0, Matrix.mul_smul, hgi, scalar_apply,
      smul_one_eq_diagonal]
  · exact (L4U4.false_of_det_neg_one hK h8 hl0 hdet).elim
  · right
    have hPu : IsUnit (P : Matrix (Fin 4) (Fin 4) K).det := Matrix.isUnits_det_units P
    have hdN : (InvClassL.stdN (c : K)).det = 1 := by
      have h1 := congrArg Matrix.det hP
      rw [det_mul, det_mul, g.2, one_mul] at h1
      exact (mul_eq_left₀ hPu.ne_zero).mp h1.symm
    rw [InvClassL.det_stdN] at hdN
    have hc1 : (c : K) ≠ 1 := fun h1 => hsq (by rw [h1]; exact ⟨1, by ring⟩)
    have hcm : (c : K) = -1 := by
      have h0 : ((c : K) - 1) * ((c : K) + 1) = 0 := by linear_combination hdN
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (sub_eq_zero.1 h) hc1
      · linear_combination h
    refine ⟨?_, g, rfl, by rw [hX, hcm, neg_one_smul]⟩
    have hns1 : ¬ IsSquare (-1 : K) := by rw [← hcm]; exact hsq
    rw [FiniteField.isSquare_neg_one_iff] at hns1
    omega

end Q5L4

theorem noQ8Datum_l4Ne3 : ∀ (F : Type) [Group F], SmallL4Ne3 F → NoQ8Datum F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h8, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC _ R S t hD _
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

theorem smallSimpleLeaf_l4Ne3 : SmallSimpleLeaf SmallL4Ne3 :=
  smallSimpleLeaf_of_noQ8Datum noQ8Datum_l4Ne3

end CFSG.ClassicalInvolution.Q3.TA3

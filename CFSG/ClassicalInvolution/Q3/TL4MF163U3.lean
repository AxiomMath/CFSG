module

public import CFSG.ClassicalInvolution.Q3.TL4MF163U3Q5
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3Q3
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Cl

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial

theorem model163U3_proved : Model163U3 := by
  intro X _ _ R S z hm hs _ _ h3 p f hp hp2 hL
  obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  have hq3 : 3 ≤ p ^ f := by
    have h2 := hp.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a := by
    by_contra hcomm
    simp only [not_exists, ne_eq, not_not] at hcomm
    have hZ : Subgroup.center (genFittingFStar X) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hcomm y x
    have h1 : Nat.card (FStarQuot X) = 1 := by
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv]
      exact Subgroup.index_top
    have h2 := MFMuZ2.card_psu3_mul hp hf hK
    rw [← Nat.card_congr e₀.toEquiv, h1, one_mul] at h2
    have h4 : 4 ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
      have h5 : 27 ≤ (p ^ f) ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq3 3
      have h6 : 1 ≤ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
        have : 9 ≤ (p ^ f) ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq3 2
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      calc 4 ≤ (p ^ f) ^ 3 := by omega
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    have h7 : Nat.gcd 3 (p ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    omega
  have hC := centralizer_genFittingFStar_eq_bot hnab
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv (MFMuZ2.center_fstar_eq_bot hnab)
  by_cases h3q : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3q
    exact MF163.U3.concl163_u3_three hm.datum hm.cls.1 hm.cls.2.1 h3 hC
      (MFMuZ2.lieModel_of_mulEquiv_classical eF (Or.inr rfl) hL)
  · have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
    have h5 : 5 ≤ p ^ f := by omega
    exact MF163.U3.concl163_ge_five hm.datum hm.cls.1 hC h hp2 h5 (eF.trans e₀)

end CFSG.ClassicalInvolution.Q3.TL4

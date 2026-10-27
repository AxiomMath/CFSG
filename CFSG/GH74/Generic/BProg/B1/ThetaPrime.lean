module

public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.GLS.C3.Layer1.Th2BalGlobal

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic.BProg Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_AG_le {D E : Subgroup G} (hDE : D ≤ E)
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : ⁅AG D, E⁆ ≤ AG D := by
  rw [Subgroup.commutator_le]
  intro y hy e he
  have h1 : e * y⁻¹ * e⁻¹ ∈ AG D :=
    Th2.Bal.conj_mem_AG (fun d hd => hE e he d (hDE hd)) ((AG D).inv_mem hy)
  have : ⁅y, e⁆ = y * (e * y⁻¹ * e⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact (AG D).mul_mem hy h1

theorem thetaHalf_le_thetaHalfPrime [Finite G] {A E : Subgroup G}
    (hA : CFSG.IsElementaryAbelian 2 ↥A) (hE : IsE 2 A E) :
    thetaHalf (pRank 2 ↥E - 1) E ≤ thetaHalfPrime A := by
  obtain ⟨hEA, hEel, hk⟩ := hE
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    Th2Sig6.mul_comm_of_isElementaryAbelian hEel ha hb
  by_cases h2 : pRank 2 ↥E = 2
  · rw [h2]
    exact le_iSup₂_of_le E ⟨hEA, hEel, hk⟩ (le_iSup_of_le h2 le_rfl)
  · have hk3 : 3 ≤ pRank 2 ↥E := by omega
    have hAG : ∀ D : Subgroup G, D ≤ E → 2 ≤ pRank 2 ↥D → AG D ≤ thetaHalfPrime A := by
      intro D hDE hD2
      have hDel : CFSG.IsElementaryAbelian 2 ↥D := Th2Sig6.isElementaryAbelian_of_le hEel hDE
      obtain ⟨D₂, hD₂D, hD₂card⟩ := Th2Sig6.exists_sub_card hDel (k := 2) hD2
      have hD₂E : IsE 2 A D₂ := Th2Sig6.isE_of_card hA (hD₂D.trans (hDE.trans hEA)) hD₂card
      have := hD₂E.2.1
      have hD₂r : pRank 2 ↥D₂ = 2 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hD₂card
      have h1 : AG D ≤ AG D₂ :=
        Th2Sig6.le_AG fun d hd hd1 => Th2Sig6.AG_le_pPrimeCoreOf (hD₂D hd) hd1
      exact h1.trans ((le_sup_right : AG D₂ ≤ thetaHalf 1 D₂).trans
        (le_iSup₂_of_le D₂ hD₂E (le_iSup_of_le hD₂r le_rfl)))
    unfold thetaHalf
    refine sup_le (iSup₂_le fun D hD => ?_) ?_
    · exact (commutator_AG_le hD.1 hEab).trans (hAG D hD.1 (by have := hD.2.2; omega))
    · exact hAG E le_rfl hk

end CFSG.GH74.Generic.BProg.B1

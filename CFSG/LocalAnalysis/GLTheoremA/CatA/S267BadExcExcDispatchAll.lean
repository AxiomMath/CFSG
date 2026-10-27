module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcExcDispatch
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE8Five

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley

section Dispatch

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem false_of_badExcCore_E8_of_not_dvd_all {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hqp : q ≠ p) (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E8 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E8 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E8 Q, hv⟩).Group)
    (hndvd : ¬ p ∣ Q.card ^ 2 - 1)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) :
    False := by
  rw [TauCeti.LieTypeIndex.characteristic_E8] at hchar
  subst hchar
  have hpq : p ≠ Q.p := Ne.symm hqp
  have he := three_le_orderOf_of_not_dvd hp (not_dvd_card_of_ne hp hpq) hndvd
  have hrk := pRank_mulAut_le_E8_all Q hv e hp hpq he
  have hμ : degCount Tag.E8 (orderOf ((Q.card : ℕ) : ZMod p)) ≤ 4 := by
    by_contra h
    have h30 := le_thirty_of_degCount_pos (τ := Tag.E8) (by simp) (by omega :
      0 < degCount Tag.E8 (orderOf ((Q.card : ℕ) : ZMod p)))
    have key : ∀ e ≤ 30, 3 ≤ e → degCount Tag.E8 e ≤ 4 := by decide
    exact h (key _ h30 he)
  have hrk' : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p S))) ≤ 5 := by
    refine hrk.trans ?_
    split_ifs <;> omega
  have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC hrk'
  exact false_of_hq_of_lift (r := 7) ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num))
    hHq e fun X _ _ φ hφ => seven_le_twoLocalRank_cat_E8 Q hv hq2 φ hφ

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end

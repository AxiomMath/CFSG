module

public import CFSG.Foundations.Basic
public import CFSG.Open.GriessAllModelsStatement
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHard
import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListLieModels

public section

namespace CFSG.LieType.OutStructure

open CFSG.Blueprint.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b

theorem center_eq_bot_of_lieIndex_of_five_le (hGA : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hOp : CFSG.pPrimeCore p K = ⊥) {d : TauCeti.ValidLieTypeIndex}
    (e : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 3) :
    Subgroup.center K = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hZp : IsPGroup p (Subgroup.center K) :=
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center K) inferInstance inferInstance hOp
  by_contra hne
  have hdvd : p ∣ Nat.card (Subgroup.center K) :=
    hZp.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨t, n, r, f, hm, -⟩ := GL83.I243.CoverList.exists_lieModel_spec d
  have htab := hdvd.trans
    (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table hGA hq e hm)
  have hPSLU : (t = .PSL ∧ p ∣ Nat.gcd n (r ^ f - 1)) ∨
      (t = .PSU ∧ p ∣ Nat.gcd n (r ^ f + 1)) := by
    rcases case_of_dvd_table hp hp2 htab with h | h | (⟨-, h3, -⟩ | ⟨-, h3, -⟩) | ⟨h3, -⟩
    · exact Or.inl h
    · exact Or.inr h
    all_goals omega
  have ht : t = .PSL ∨ t = .PSU := hPSLU.imp And.left And.left
  have hpg : p ∣ diagGcd t n r f := by
    rcases hPSLU with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact h
  have hpa : p ∣ (genericOrders t n r f).1 := by
    rcases hPSLU with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact h
  have hpn : p ∣ n := by
    rcases hPSLU with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h.trans (Nat.gcd_dvd_left _ _)
  have hn2 : 2 ≤ n := by
    rcases ht with rfl | rfl
    · exact hm.1.2.2.1
    · have := hm.1.2.2.1
      omega
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd (by omega) hpn)
  have hcl : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) t n r f := by
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
    · exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hcl
    · omega
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) :=
    le_trans (by omega) (n_sub_two_le_pRank_of_model hcl ht hn2 hp hp2 hpg)
  obtain ⟨-, h2⟩ := lieCoverRankHighLin_aux hGA hq.1 hp hp2 hdvd h3
    (Or.inl ⟨by rcases ht with rfl | rfl <;> decide, hcl⟩) ht hpa
  omega

end CFSG.LieType.OutStructure

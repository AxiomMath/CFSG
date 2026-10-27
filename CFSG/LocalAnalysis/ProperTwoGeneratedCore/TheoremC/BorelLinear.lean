module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelTransport
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsLinear

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.BenderSuzuki

theorem benderBorelFacts_psl2Model {n : ℕ} (hn : 2 ≤ n) (U : Sylow 2 (PSL2Model n)) :
    BenderBorelFacts (PSL2Model n) (U : Subgroup (PSL2Model n)) := by
  obtain ⟨hUel, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two hn U
  have hcomm : ∀ a ∈ (U : Subgroup (PSL2Model n)), ∀ b ∈ (U : Subgroup (PSL2Model n)),
      Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcenter : ∀ w, InCenterOf (U : Subgroup (PSL2Model n)) w ↔
      w ∈ (U : Subgroup (PSL2Model n)) := fun w =>
    ⟨fun h => h.1, fun hw => ⟨hw, fun q hq => hcomm q hq w hw⟩⟩
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_, ?_, ?_, fun σ hσ => ?_⟩
  · rw [hcenter]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · rw [hcenter]
    exact mul_mem ha ha
  · obtain ⟨D, -, hDcard, -, hsup, hreg⟩ := CFSG.Walter.psl2_even_normalizer_sylow_two hn U
    refine ⟨D, ?_, hsup ▸ le_sup_right, hsup, fun w w' hw hw1 hw' hw'1 => ?_,
      fun β _ _ _ hβc _ a ha b hb => hβc a ha b ((hcenter b).mpr hb)⟩
    · rw [hDcard]
      exact Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    · obtain ⟨d, hd, -⟩ := hreg w hw.1 hw1 w' hw'.1 hw'1
      exact ⟨(d : PSL2Model n)⁻¹, inv_mem d.2, by rw [inv_inv]; exact hd⟩
  · rw [Nat.card_congr (Equiv.subtypeEquivRight hcenter)]
    exact hUcard ▸ hq
  · obtain ⟨j, hj, hσj⟩ := BenderFacts.exists_mem_eq_conj_of_fixes_sylow_of_mulEquiv_psl2 hn
      (GaloisField.card 2 n (by omega)) (MulEquiv.refl _) U σ hσ
    exact ⟨j, hj, fun k => by rw [hσj]; rfl⟩

theorem psl2BorelFacts : PSL2BorelFacts := fun _ hn =>
  ⟨Classical.arbitrary _, benderBorelFacts_psl2Model hn _⟩

theorem benderBorelFactsHold_of_suzuki_unitary (hS : SuzukiBorelFacts)
    (hU : UnitaryBorelFacts) : BenderBorelFactsHold :=
  benderBorelFactsHold_of_models psl2BorelFacts hS hU

end CFSG.ProperTwoGeneratedCore.TheoremC

module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversFacts
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.BenderSuzuki

theorem benderCoverFacts_psl2Model {n : ℕ} (hn : 3 ≤ n) (U : Sylow 2 (PSL2Model n)) :
    BenderCoverFacts (PSL2Model n) (U : Subgroup (PSL2Model n)) := by
  obtain ⟨hUel, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two (by omega : 2 ≤ n) U
  have hcomm : ∀ a ∈ (U : Subgroup (PSL2Model n)), ∀ b ∈ (U : Subgroup (PSL2Model n)),
      Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcenter : ∀ w, InCenterOf (U : Subgroup (PSL2Model n)) w ↔
      w ∈ (U : Subgroup (PSL2Model n)) := fun w =>
    ⟨fun h => h.1, fun hw => ⟨hw, fun q hq => hcomm q hq w hw⟩⟩
  refine ⟨Or.inl ?_, fun P _ _ h₃ _ a ha b hb => h₃ a b ((hcenter a).mpr ha) hb⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcenter), hUcard]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

end CFSG.ProperTwoGeneratedCore.Lemma37

module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSym
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Assembly.LowTwoRank

theorem mcltf_statedScalars_zmod2 (ι : Type) [Fintype ι] [DecidableEq ι] :
    StatedScalars ι (ZMod 2) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot ι

@[expose] noncomputable def mcltf_spProjEquiv (n : ℕ) :
    ↥(StatedSp n (ZMod 2)) ≃* StatedProj (StatedSp n (ZMod 2)) :=
  ((QuotientGroup.quotientMulEquivOfEq (by
    rw [mcltf_statedScalars_zmod2, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot).symm

theorem mcltf_facts_Sp {n : ℕ} (hn : 3 ≤ n) : mcltf_Facts ↥(StatedSp n (ZMod 2)) := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) n
    (by omega) (Or.inr (Or.inr ⟨hK, hn⟩))
  have : IsSimpleGroup ↥(StatedSp n (ZMod 2)) := (mcltf_spProjEquiv n).isSimpleGroup
  exact mcltf_facts_of_simple (mcltf_exists_ne_of_perfect
    (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n (ZMod 2)
      (Or.inr (Or.inr ⟨hK, hn⟩))).commutator_eq_top)

theorem mcltf_facts_statedSp {n : ℕ} (hn : 2 ≤ n) :
    mcltf_Facts ↥(CFSG.Open.StatedSp n (ZMod 2)) := by
  have e : ↥(CFSG.Open.StatedSp n (ZMod 2)) ≃* ↥(StatedSp n (ZMod 2)) := MulEquiv.subgroupCongr rfl
  refine mcltf_facts_of_mulEquiv e ?_
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact mcltf_facts_of_mulEquiv
      (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm (ZMod 2) (ZMod.card 2))
      (mcltf_facts_perm (by norm_num))
  · exact mcltf_facts_Sp h

end CFSG.HardMathSupport.Solomon.Coordinator

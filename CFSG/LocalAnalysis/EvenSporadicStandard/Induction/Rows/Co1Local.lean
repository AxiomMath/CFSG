module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OutLocalQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block

@[expose] def Co1Q (H : Type) [Group H] (L K : Subgroup H) (u : H) : Prop :=
  Co1Pair H L K u ∧ (∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2) ∧
    ∀ [Finite H] (N : Subgroup H) (t : H), SolomonHypQ H N L K t u → t ∈ N

theorem co1Q_inL : PairClass.InL Co1Q := fun _ _ _ _ _ h => h.1.1

theorem co1Q_twoSylow : PairClass.TwoSylow Co1Q := fun _ _ _ _ _ _ h => h.2.1

theorem tMemFStar_co1 : TMemFStar .Co1 Co1Q := fun _ _ _ N _ _ t _ _ hhyp hQ => hQ.2.2 N t hhyp

theorem solomonLocalQ_of_local {s : TauCeti.SporadicName} {H : Type} [Group H] [Finite H]
    {L K : Subgroup H} {u : H} (hcov : OddCover s L) (hl : SolomonLocal L K u) :
    SolomonLocalQ L K u where
  u_order := hl.u_order
  u_mem := Subgroup.le_normalizer hl.u_mem
  u_not_central := hcov.not_mem_centralizer_of_orderOf_two hl.u_mem hl.u_order
  K_le := hl.K_le
  u_mem_centralizer_K := hl.u_mem_centralizer_K
  standard_in_L := solStd_of_standardComponentIsStandard hl.standard_in_L
  autCentralizer_two := hl.autCentralizer_two

theorem sol78SettingLocalQ_co1 (hmult : OddMultTrivial .Co1) :
    Sol78SettingLocalQ .Co1 Co1Q Co1Pair := by
  intro H _ _ L K u hcov hQ
  exact ⟨solomonLocalQ_of_local hcov (solomonLocal_co1 (hcov.isSporadic_of_mult hmult) hQ.1), hQ.1⟩

theorem sol78Local39Q_co1 (hmult : OddMultTrivial .Co1) : Sol78Local39Q .Co1 Co1Pair := by
  intro H _ _ N L K t u hcov hset hP
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := co1_model (hcov.isSporadic_of_mult hmult) hP
  obtain ⟨M⟩ := co1_outModel
  exact M.local39_of_fields hP.1 hP.2.1 hP.2.2.1 (mem_centralizer_iff.2 hP.2.2.2.1) hset.hyp35 Ψ
    hΨ hΨL hΨR hΨu hP.2.2.2.2.1 (hP.2.2.2.2.2.trans card_twoBD.symm)

end CFSG.EvenSporadicStandard.Induction

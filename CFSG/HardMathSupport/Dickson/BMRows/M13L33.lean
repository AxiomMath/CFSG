
module

public import CFSG.HardMathSupport.Dickson.BMRows.M13L33Base
import all CFSG.HardMathSupport.Dickson.BMRows.M13L33Base

public import Certificates.Certificate17632

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.BMRows.M13L33

open CFSG.CosetTable CFSG.GH74.KGroups CFSG.GH74.KGroups.L33

section Monster

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

section Facts

theorem l33_facts :
    (∀ r ∈ l33Rels, evalRel l33Gen r = 1) ∧
      gw yW * gw thirteenX = gw thirteenX * gw yW ∧
      gw j1W * gw thirteenX = gw thirteenX * gw j1W ∧ gw j1W ≠ 1 :=
  Certificates.certificate17632

noncomputable def l33Mon : PG 2 l33Rels →* Gmat := l33Hom l33Gen l33_facts.1

theorem l33Mon_of (i : Fin 2) : l33Mon (PresentedGroup.of i) = l33Gen i := l33Hom_of _ _ i

theorem range_l33Mon_le : l33Mon.range ≤ Subgroup.centralizer ({gw thirteenX} : Set Gmat) := by
  rw [l33Mon, range_l33Hom]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨by rw [l33Gen_zero]; exact l33_facts.2.2.1, by rw [l33Gen_one]; exact l33_facts.2.1⟩

section Iso

theorem l33Mon_injective : Function.Injective l33Mon := by
  haveI := isSimple_pg
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal l33Mon.ker with h | h
  · exact h
  · exfalso
    apply l33_facts.2.2.2
    have : PresentedGroup.of (0 : Fin 2) ∈ l33Mon.ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, l33Mon_of] at this
    exact this

theorem exists_l33_xE :
    ∃ Q : Subgroup Gmat, Q ≤ Subgroup.centralizer ({gw thirteenX} : Set Gmat) ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) := by
  obtain ⟨e⟩ := nonempty_equiv_sl
  exact ⟨l33Mon.range, range_l33Mon_le,
    ⟨(MonoidHom.ofInjective l33Mon_injective).symm.trans e⟩⟩

end Iso

end Facts

end Monster

end CFSG.HardMathSupport.Dickson.BMRows.M13L33

module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017MRankFiveHN
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint.NativeSporadic


theorem i1017MonsterFiveRank_holds : I1017MonsterFiveRank := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ : Nonempty
      (CFSG.Monster.Existence.MGriess ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    MonsterModel.iso_griess_y443Derived.trans MonsterModel.iso_y443Derived_tauCeti
  obtain ⟨E, hE, hc⟩ := exists_elemAbelian_five_four_of_monsterExistence
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  let φ := b.trans e.symm
  exact ⟨E.map φ.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hE _,
    by rw [Subgroup.card_map_of_injective φ.injective, hc]⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017

end

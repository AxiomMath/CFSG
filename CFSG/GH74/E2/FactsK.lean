module

public import CFSG.GH74.E2.FactsAssembly
public import CFSG.GH74.KGroups.TwoSz8
public import CFSG.GH74.KGroups.TwoM12Facts
public import CFSG.GH74.KGroups.CoverSz8

public section

namespace CFSG.GH74.E2

open CFSG.GH74 CFSG.Blueprint

theorem sz8Facts : Sz8Facts where
  autRank_ge5 := by
    intro K _ _ hK p hp h5 B hB
    obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel hK
    exact KGroups.Sz8.autRank_ge5 e p hp h5 B hB
  autRank3_le_two := by
    intro K _ _ hK R hR
    obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel hK
    exact KGroups.Sz8.autRank3_le_two e R hR
  autRank3_le_one := by
    intro K _ _ hK R hR
    obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel hK
    exact KGroups.Sz8.autRank3_le_one e R hR
  fixed_solvable := by
    intro K _ _ hK α hα2 hα1 L hL
    obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel hK
    exact KGroups.Sz8.fixed_solvable e α hα2 hα1 L hL

theorem not_comm_of_isQuasisimple {L : Type} [Group L] (hq : IsQuasisimple L) :
    ¬ ∀ a b : L, a * b = b * a := by
  intro h
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h a' b'])

theorem twoSz8Facts :
    TwoSz8Facts where
  autRank_ge5 := by
    intro K _ _ hK p hp h5 B hB
    exact KGroups.TwoSz8.autRank_ge5 hK.1.1 hK.2.2 p hp h5 B hB
  autRank3_le_two := by
    intro K _ _ hK R hR
    exact KGroups.TwoSz8.autRank3_le_two hK.1.1 hK.2.2 R hR
  autRank3_le_one := by
    intro K _ _ hK R hR
    exact KGroups.TwoSz8.autRank3_le_one hK.1.1 hK.2.2 R hR
  rank_ge4_sz := by
    intro K _ _ hK
    exact KGroups.TwoSz8.rank_ge4 hK.2.1 hK.2.2
  fixed_false := by
    intro K _ _ hK α hα2 hα1 L hL hq
    exact KGroups.TwoSz8.fixed_false hK.1.1 hK.2.2 α hα2 hα1 L hL hq.1
      (not_comm_of_isQuasisimple hq)

theorem k0Rest2 :
    K0Rest2 :=
  k0Rest2_of sz8Facts KGroups.TwoM12.twoM12Facts twoSz8Facts

theorem e2ComponentFacts :
    E2ComponentFacts :=
  e2ComponentFacts_of_sz8 KGroups.CoverSz8.sz8_cover

end CFSG.GH74.E2

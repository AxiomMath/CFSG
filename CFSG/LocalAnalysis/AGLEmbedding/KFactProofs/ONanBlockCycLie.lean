module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycOrth
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSmall
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabAutIrr

@[expose] def LieCyclicG2 : Prop :=
  ∀ (Y : Type) [Group Y], IsG2Two Y → HasE9 Y

theorem exists_sylow_of_isSylowTwoOf_top {Y : Type} [Group Y] [Finite Y] {T : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) : ∃ T' : Sylow 2 Y, (T' : Subgroup Y) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
  exact ⟨hT.2.1.toSylow hidx, rfl⟩

theorem lieCyclicParabolic_of (hG2 : LieCyclicG2) : LieCyclicParabolic := by
  intro Y _ _ hY T J hT hNJ hJ hJtop
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  rcases isClassicalTwoOrG2_cases hY with ⟨t, n, f, ht, h⟩ | hG | hS
  · rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact lieCyclic_of_model_psl h T' J hNJ hJ hJtop
    · exact Or.inl (hasE9_of_model_psu_of_parabolic h T' J hNJ hJ hJtop)
    · exact Or.inl (hasE9_of_model_psp h)
    · exact Or.inl (hasE9_of_model_pomegaPlus h)
    · exact Or.inl (hasE9_of_model_pomegaMinus h)
  · exact Or.inl (hG2 Y hG)
  · exact hasE9_or_aut5Le_of_small hS

theorem p_eq_two_of_card_eq_two {q : TauCeti.PrimePower} (h : q.card = 2) : q.p = 2 := by
  have h2 : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact h
  exact ((Nat.Prime.pow_eq_iff Nat.prime_two).1 h2).1

theorem lieCyclicOrthogonal : LieCyclicOrthogonal := by
  intro Y _ _ hY
  rcases hY with ⟨⟨d, hv⟩, ⟨m, q, hq, hdm⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hp2 := p_eq_two_of_card_eq_two hq
    rcases hdm with rfl | rfl | ⟨rfl, rfl⟩
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even m q hv hp2 e
      rw [hp2] at h
      exact Or.inl (hasE9_of_model_pomegaPlus h)
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hv hp2 e
      rw [hp2] at h
      exact Or.inl (hasE9_of_model_pomegaMinus h)
    · have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      rw [hp2] at h
      exact Or.inl (hasE9_of_model_psu h (by norm_num))
  · rcases hn with rfl | rfl | rfl
    · exact Or.inr (aut5Le_of_mulEquiv e.symm aut5Le_alternatingGroup_five)
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))

end CFSG.AGLEmbedding.BlockCyc

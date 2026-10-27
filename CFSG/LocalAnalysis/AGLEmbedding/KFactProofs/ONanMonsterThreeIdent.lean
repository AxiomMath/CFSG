module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeY
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporHS5
import CFSG.Sporadic.Bridge.Y322Central

public section

namespace CFSG.AGLEmbedding.MonsterThree

open CFSG.Blueprint
open CFSG.RankThree.PartOne.CTP.Fus (FusionGenerationOf)

theorem fusionGenerationOf_of_isSimple_monster {T : Type} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) : FusionGenerationOf T 3 :=
  fusionGenerationOf_of_mulEquiv e.symm (fusionGenerationOf_M_three e.injective.nontrivial)

theorem sporGammaOneAt_M_three :
    SporGammaOneAt .M 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  by_cases hnt : Nontrivial (NativeSporadic.Carrier .M)
  · exact sporGammaOneAt_of_fusion Nat.prime_three ⟨b⟩ (fusionGenerationOf_M_three hnt)
  · intro K _ _ he T
    obtain ⟨e⟩ := he
    have hsub : Subsingleton (NativeSporadic.Carrier .M) := not_nontrivial_iff_subsingleton.1 hnt
    have : Subsingleton K := (e.trans b.symm).injective.subsingleton
    exact eq_top_iff.2 fun g _ => by rw [Subsingleton.elim g 1]; exact one_mem _

end CFSG.AGLEmbedding.MonsterThree

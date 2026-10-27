module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCFive
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCSeven

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

@[expose] def KDI278SporCMonster : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z] (K : Subgroup Z), K.Normal → P64IsSpor .M ↥K →
    Subgroup.centralizer (K : Set Z) = ⊥ →
      ∀ B : Subgroup Z, CFSG.Open.IsElemAbelian 13 B → Nat.card B = 13 ^ 2 →
        (∀ y ∈ Subgroup.centralizer (B : Set Z), y ^ 13 = 1 → y ∈ B) →
          ∀ W : Subgroup Z, B ≤ Subgroup.normalizer (W : Set Z) →
            Nat.Coprime (Nat.card W) (2 * 13) → W = ⊥

theorem kdI278SporC_of_monster
    (hM : KDI278SporCMonster) : KDI278SporC := by
  intro p s hpair Z _ _ K hKn hsK hC B hB hBc hSC W hBW hW
  haveI : K.Normal := hKn
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact kdSporC_HS_five hsK hC hB hBc hBW hW
  · exact kdSporC_Ru_five hsK hC hB hBc hBW hW
  · exact kdSporC_Fi24_seven hsK hC hB hBc hBW hW
  · exact kdSporC_He_seven hsK hC hB hBc hBW hW
  · exact kdSporC_ON_seven hsK hC hB hBc hBW hW
  · exact hM Z K hKn hsK hC B hB hBc hSC W hBW hW

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

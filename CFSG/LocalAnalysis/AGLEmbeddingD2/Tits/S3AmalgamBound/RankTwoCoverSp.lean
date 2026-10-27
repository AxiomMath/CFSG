module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLProofs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSpLevi

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sp_adj (hF : Nat.card F = 2) (i j : Fin n) (hij : i.val + 1 = j.val) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(rankOne (rootDatum n F).rootGroup i ⊔ rankOne (rootDatum n F).rootGroup j) := by
  by_cases hj : j.val + 1 < n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨i', hi'⟩ : ∃ i' : Fin m, i = i'.castSucc := ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    obtain ⟨j', hj'⟩ : ∃ j' : Fin m, j = j'.castSucc := ⟨⟨j.val, by omega⟩, Fin.ext rfl⟩
    subst hi' hj'
    exact not_isPSolvable_sp_of_sl i' j' (OrdinaryProofs.RankTwoCoverSL.sl_adj (F := F) hF i' j' (by simpa using hij))
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hi' : i = Fin.natAdd m (0 : Fin 2) := Fin.ext (by simp; omega)
    have hj' : j = Fin.natAdd m (1 : Fin 2) := Fin.ext (by simp; omega)
    subst hi' hj'
    exact not_isPSolvable_lastTwo hF m

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

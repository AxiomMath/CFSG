module

public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pRank_pos_of_le_inf_conjSubgroup {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) {g : G} {X : Subgroup G}
    (hX : X ≤ M ⊓ CFSG.Quasithin.conjSubgroup M g) (hpos : 0 < CFSG.Open.pRank p X) : g ∈ M := by
  by_contra hg
  obtain ⟨E, hEX, -, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp X
  have hpE : p ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self p (by omega)
  have hg' : g⁻¹ ∉ M := fun hh => hg (by simpa using M.inv_mem hh)
  exact hsp.2.2 g⁻¹ hg' (hpE.trans (Subgroup.card_dvd_of_le (hEX.trans hX)))

end CFSG.GroupTheory

module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem exists_isElemAbelian_card_pow_three {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (h3 : 3 ≤ pRank p H) :
    ∃ A : Subgroup G, A ≤ H ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 3 := by
  obtain ⟨E, hEH, hE, hEc⟩ := pRank_attained p H (by omega)
  obtain ⟨K, hK, -, hKE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 3)
    (H := ⊥) (L := E) (by simp) (by rw [hEc]; exact pow_dvd_pow p h3) bot_le
  refine ⟨K, hKE.trans hEH, ⟨isMulCommutative_iff.mpr fun a b => ?_,
    fun x hx => hE.2 x (hKE hx)⟩, hK⟩
  have h := congrArg Subtype.val (isMulCommutative_iff.mp hE.1 ⟨a, hKE a.2⟩ ⟨b, hKE b.2⟩)
  exact Subtype.ext (by simpa using h)

end CFSG.LocalAnalysis.RankFourTheoremC

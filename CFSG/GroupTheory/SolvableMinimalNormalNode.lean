module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal

public section

namespace CFSG.SolvableHall

universe u

theorem solvable_minimal_normal_elementary_abelian {G : Type u} [Group G] [Finite G]
    (hG : Group.IsSolvable G) (N : Subgroup G) [hNn : N.Normal] (hN : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M.Normal → M ≠ ⊥ → M ≤ N → M = N) :
    ∃ r d : ℕ, r.Prime ∧ 1 ≤ d ∧ IsElementaryAbelian r N ∧ Nat.card N = r ^ d := by
  have hminimal : CFSG.RankThreeEvenClassification.Helpers.MinimalNontrivialNormal N :=
    ⟨⟨hNn, hN⟩, fun M hM hMN => (hmin M hM.1 hM.2 hMN).ge⟩
  obtain ⟨r, hr, ⟨hcomm, hpow⟩, d, hd, hcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.minimal_normal_solvable_elementary N hminimal
      inferInstance
  refine ⟨r, d, hr, hd, ?_, hcard⟩
  exact
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        apply Subtype.ext
        simpa using hpow x x.2 }

end CFSG.SolvableHall

module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.SectionRank

theorem isElementaryAbelian_iff_isElemAbelian {G : Type*} [Group G] (p : ℕ) (E : Subgroup G) :
    IsElementaryAbelian p E ↔ CFSG.Open.IsElemAbelian p E := by
  constructor
  · intro h
    exact ⟨h.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
  · rintro ⟨hc, hp⟩
    exact { toIsMulCommutative := hc
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
              Subtype.ext (by rw [Subgroup.coe_pow, hp x x.2, Subgroup.coe_one]) }

theorem pRank_eq_open_pRank_top (p : ℕ) (H : Type*) [Group H] [Finite H] :
    CFSG.pRank p H = CFSG.Open.pRank p (⊤ : Subgroup H) := by
  unfold CFSG.pRank CFSG.Open.pRank
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, le_top, true_and, isElementaryAbelian_iff_isElemAbelian]

theorem isStronglyQuasithin_iff {H : Type*} [Group H] [Finite H] :
    IsStronglyQuasithin H ↔
      ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup H) ≤ 2 := by
  simp only [IsStronglyQuasithin, pRank_eq_open_pRank_top]

end CFSG.SectionRank

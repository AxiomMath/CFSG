module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarCentre

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.EvenSporadicStandard.TwoHS

variable {G : Type} [Group G] [Finite G]

theorem central_mem_cover
    {H : Type} [Group H] {E : Subgroup H} (hE : IsHSCover H E)
    (M : CoverModel ↥E) {z : H} (hz1 : z ≠ 1) (hz : ∀ y : H, y * z = z * y) :
    ∃ hzE : z ∈ E, (⟨z, hzE⟩ : ↥E) = M.tE := by
  have hzE : z ∈ E := hE.centralizer_le (mem_centralizer_iff.2 fun y _ => hz y)
  have hcen : (⟨z, hzE⟩ : ↥E) ∈ center ↥E :=
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (hz y)
  refine ⟨hzE, ?_⟩
  rcases (M.mem_center_iff hE.card_center).1 hcen with h | h
  · exact absurd (congrArg Subtype.val h) hz1
  · exact h

theorem factorization_two_177408000' : (177408000 : ℕ).factorization 2 = 11 := by
  have h : (177408000 : ℕ) = 2 ^ 11 * 86625 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end CFSG.EvenSporadicStandard.Solomon78

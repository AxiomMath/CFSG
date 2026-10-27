module

public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LargeExtraspecial.DW37Input
public import CFSG.LargeExtraspecial.D73GL

public section

namespace CFSG.LargeExtraspecial.DW.D73

open Matrix
open scoped MatrixGroups

open CFSG.Assembly.LowTwoRank in
theorem le_of_two_pow_dvd_card_statedProj {K : Type} [Field K] [Finite K] {s m a : ℕ}
    (hK : Nat.card K = 2 ^ s) (h : 2 ^ a ∣ Nat.card (StatedProj (StatedSL m K))) :
    a ≤ s * (m * (m - 1) / 2) := by
  have h1 : Nat.card (StatedProj (StatedSL m K)) ∣ Nat.card (StatedSL m K) :=
    Subgroup.card_quotient_dvd_card _
  have h2 : Nat.card (StatedSL m K) ∣ Nat.card (GL (Fin m) K) :=
    Subgroup.card_subgroup_dvd_card _
  exact le_of_two_pow_dvd_card_GL hK (h.trans (h1.trans h2))

open CFSG.Assembly.LowTwoRank in
theorem nonempty_mulEquiv_SL_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (N : ℕ) : Nonempty (StatedProj (StatedSL N K) ≃* SL(N, ZMod 2)) := by
  let _ := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hK'
  exact ⟨(projectiveSpecialLinearGroupEquivStatedProj N K).symm.trans
    ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv e.symm (Fin N)).trans
      (DW.slEquivPSL N).symm)⟩

end CFSG.LargeExtraspecial.DW.D73

module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3NLCtx
public import CFSG.ClassicalInvolution.Q3.Q3NSModel
public import CFSG.ClassicalInvolution.Uniform.UFacade
public import CFSG.ClassicalInvolution.Uniform.UTwin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NH

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3NS
  CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups

section Local

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem oddCoreIn_locLayer_eq_bot_of_intrinsic (hz : IsClassicalMember3 K z)
    (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hex : ExactMembers3 (conjClass3 K)) : oddCoreIn (locLayer (conjClass3 K) z) = ⊥ := by
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hOK : oddCoreIn K = ⊥ := by
    unfold oddCoreIn
    rw [show componentClassificationOddCore ↥K = ⊥ from hex K hK]
    exact Subgroup.map_bot _
  have hOC : oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
    rw [← Uniform.oddCoreIn_eq_of_intrinsic (IsClassicalMemberU.ofQ3 hz) hint]
    exact hOK
  have hΩ : ConjInvariant (conjClass3 K) := (inClass3_conjugates hz).conjInvariant
  have hle : oddCoreIn (locLayer (conjClass3 K) z) ≤
      oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    le_oddCoreIn_of_normalizes
      ((oddCoreIn_le _).trans (centralizingLayer_le_centralizer _ _))
      (fun n hn => mem_normalizer_oddCoreIn_centralizingLayer hΩ hn) (odd_card_oddCoreIn _)
  exact le_bot_iff.mp (hOC ▸ hle)

theorem localOddThreeFree3_of_intrinsic_at (hz : IsClassicalMember3 K z)
    (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hex : ExactMembers3 (conjClass3 K)) : Q3W.LocalOddThreeFree3 (conjClass3 K) z := by
  have hbot := oddCoreIn_locLayer_eq_bot_of_intrinsic hz hint hex
  show ¬ 3 ∣ Nat.card (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z))
  have hcard : Nat.card (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z)) = 1 := by
    have h1 := Subgroup.card_map_of_injective
      (K := classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z))
      (locLayer (conjClass3 K) z).subtype_injective
    have h2 : Nat.card (oddCoreIn (locLayer (conjClass3 K) z)) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [← h1]
    exact h2
  rw [hcard]
  decide

theorem setup3_of_exact_intrinsic (hz : IsClassicalMember3 K z)
    (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hex : ExactMembers3 (conjClass3 K)) : Setup3 K z := by
  refine And.intro hex ?_
  have hbot := oddCoreIn_locLayer_eq_bot_of_intrinsic hz hint hex
  have h1 : classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (locLayer (conjClass3 K) z).subtype_injective).mp hbot
  intro x hx
  have hx' : x ∈ classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z) := hx
  rw [h1, Subgroup.mem_bot] at hx'
  subst hx'
  exact Subgroup.one_mem _

end Local

end CFSG.ClassicalInvolution.Q3.Q3NH

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lLift

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.OddStandard.SmallF3.HypA2 (TypU isSLTwoOver_of_mulEquiv coreInvariant_typU)

theorem a2l_nonempty_equiv_map {P S : Type} [Group P] [Group S] (π : P →* S) (J : Subgroup P)
    (hinj : ∀ x ∈ J, π x = 1 → x = 1) : Nonempty (↥J ≃* ↥(J.map π)) := by
  refine ⟨MulEquiv.ofBijective (π.subgroupMap J) ⟨?_, π.subgroupMap_surjective J⟩⟩
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  exact Subtype.ext (hinj x.1 x.2 (congrArg Subtype.val hx))

theorem a2lDatum_of_block {P S : Type} [Group P] [Finite P] [Group S] (π : P →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center P) {q₀ : ℕ} (hodd : Odd q₀)
    (h5 : 5 ≤ q₀) {t : P} (ht : t * t = 1) (ht1 : π t ≠ 1) {J N : Subgroup P} (hNJ : N ≤ J)
    (htN : t ∈ N) (hJc : J ≤ centralizer ({t} : Set P))
    (hJs : CFSG.Assembly.IsSubnormal J (centralizer ({t} : Set P)))
    (hJq : CFSG.IsQuasisimple ↥J) (hinj : ∀ x ∈ J, π x = 1 → x = 1)
    (hN : HarrisLit.IsSLTwoOver q₀ ↥N) (hTU : TypU ↥J) : a2lDatum S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ x, π (MulAut.conj t x) = MulAut.conj (π t) (π x) := fun x => by
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hz2 : π t * π t = 1 := by rw [← map_mul, ht, map_one]
  have hJcomp : CFSG.Assembly.IsComponentOf J (fixedSubgroup (MulAut.conj t)) := by
    rw [CFSG.Sporadic.HeldB.fixedSubgroup_conj]
    exact ⟨hJc, hJs, (AssemblyBPredicates.isQuasisimple_iff_native _).2 hJq⟩
  have hcomp := LocalAnalysis.ComponentInitial.isComponentOf_map_fixed hπ hker
    (a2l_conj_involutive ht) hcomm hJcomp
  rw [CFSG.Sporadic.HeldB.fixedSubgroup_conj] at hcomp
  obtain ⟨eJ⟩ := a2l_nonempty_equiv_map π J hinj
  obtain ⟨eN⟩ := a2l_nonempty_equiv_map π N fun x hx => hinj x (hNJ hx)
  refine ⟨q₀, J.map π, N.map π, π t, hodd, h5, ?_, Subgroup.mem_map_of_mem π htN,
    Subgroup.map_mono hNJ, ?_, hcomp, isSLTwoOver_of_mulEquiv eN hN, ?_⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact hz2) ht1
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 (hJc hx)]
  · exact coreInvariant_typU _ _ ⟨QuotientGroup.congr _ _ eJ (CFSG.pPrimeCore_map_iso 2 eJ)⟩ hTU

end CFSG.OddStandard.SmallF3.HypA2Leaves

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
import CFSG.Quasithin.Background.A318PL3Inst
import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofCharThree
import CFSG.RankThree.PartTwo.Sec4.Item426A6U43

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Adapters.RankTwoModelTransports (nonempty_mulEquiv_psl_galoisField)
open CFSG.Quasithin.A318P (projSU_of_statedClassicalModel_gen)
open CFSG.RankThree.PartTwo.Sec4 (projSLEquivPSLn)
open CFSG.RankThree.PartTwo.Sec4.Item426 (u43ThreeCentralizer)
open CFSG.RankThree.PartTwo.Sec21.Item228CensusProof
  (orderOf_ne_fifteen_projSL_four_three orderOf_ne_fifteen_projSL_three_nine)

theorem orderOf_ne_fifteen_of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : ∀ y : T, orderOf y ≠ 15) (x : S) : orderOf x ≠ 15 := fun hx =>
  h (e x) (by rw [MulEquiv.orderOf_eq]; exact hx)

theorem orderOf_ne_fifteen_projSU_four_three (t : projSU 4 3 1) : orderOf t ≠ 15 := by
  intro ht
  have hy : orderOf (t ^ 5) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [ht]; norm_num), ht]
  have hz : orderOf (t ^ 3) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [ht]; norm_num), ht]
  have hmem : t ^ 3 ∈ Subgroup.centralizer ({t ^ 5} : Set (projSU 4 3 1)) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact (Commute.pow_pow_self t 5 3).eq
  have hdvd : 5 ∣ Nat.card (Subgroup.centralizer ({t ^ 5} : Set (projSU 4 3 1))) := by
    have h := orderOf_dvd_natCard (⟨t ^ 3, hmem⟩ : Subgroup.centralizer ({t ^ 5} : Set _))
    rwa [Subgroup.orderOf_mk, hz] at h
  exact u43ThreeCentralizer _ hy hdvd

theorem noFifteen_holds : NoFifteen := by
  intro S _ _ hS x
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hS with h | h | h
  · obtain ⟨e⟩ := projSU_of_statedClassicalModel_gen (h.statedClassicalModel (by decide))
    exact orderOf_ne_fifteen_of_mulEquiv e orderOf_ne_fifteen_projSU_four_three x
  · obtain ⟨e⟩ := nonempty_mulEquiv_psl_galoisField S 3 3 2 (h.statedClassicalModel (by decide))
    exact orderOf_ne_fifteen_of_mulEquiv (e.trans (projSLEquivPSLn 3 _).symm)
      orderOf_ne_fifteen_projSL_three_nine x
  · obtain ⟨e⟩ := nonempty_mulEquiv_psl_galoisField S 4 3 1 (h.statedClassicalModel (by decide))
    exact orderOf_ne_fifteen_of_mulEquiv (e.trans (projSLEquivPSLn 4 _).symm)
      orderOf_ne_fifteen_projSL_four_three x

end CFSG.EvenSporadicStandard.HSStd.InvCent

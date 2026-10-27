module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Tools
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Skeleton

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Max

variable {X : Type} [Group X] [Finite X]

theorem LPrec.card_quot_le {K L : Subgroup X} (h : LPrec X K L) :
    Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ≤ Nat.card (↥L ⧸ pPrimeCore 2 ↥L) := by
  rcases h with rfl | ⟨s, t, hs, ht, hst, hne, hKs, hLt, htc, hlt⟩
  · exact le_rfl
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hKq : IsTwoGenQuasi ↥K := by
    obtain ⟨hKC, hKpc⟩ := hKs
    exact (isTwoGenQuasi_subgroupOf_iff hKC).1 (isPComponent_two_iff.1 hKpc).2
  have hF : oTwoPrimeOf (K ⊓ centralizer ({t} : Set X)) ≤ L := by
    refine le_trans ?_ hlt
    unfold lTwist
    rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    exact oTwoPrimeOf_mono le_sup_left
  have hFK : oTwoPrimeOf (K ⊓ centralizer ({t} : Set X)) ≤ K :=
    (oTwoPrimeOf_le _).trans inf_le_left
  exact card_quot_pPrimeCore_le_of_covers hFK hF
    (oTwoPrimeOf_inf_centralizer_covers ht2 hKq.1 htc)

theorem LBelow.card_quot_le {K L : Subgroup X} (h : LBelow X K L) :
    Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ≤ Nat.card (↥L ⧸ pPrimeCore 2 ↥L) := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (LPrec.card_quot_le hstep.2.2)

theorem HypA.card_quot_le_of_lPrec (hA : HypA X) {n : ℕ} (hn : IsMaxAhatDeg X n) {u : X}
    {Lu M : Subgroup X} (hu : orderOf u = 2) (hL : IsAhatIntr X u Lu)
    (hLn : IsDoubleCoverOfAlt (↥Lu ⧸ pPrimeCore 2 ↥Lu) n) (hM : IsLComp X M)
    (hLM : LPrec X Lu M) :
    Nat.card (↥M ⧸ pPrimeCore 2 ↥M) ≤ Nat.card (↥Lu ⧸ pPrimeCore 2 ↥Lu) := by
  have hstar := hA n hn u Lu hu hL hLn
  have hbelow : LBelow X Lu M := Relation.ReflTransGen.single ⟨hL.isLComp hu, hM, hLM⟩
  exact (hstar.2 M hbelow).card_quot_le

end Max

end CFSG.OddStandard.Solomon75

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SzFiveTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
public import CFSG.GroupTheory.PRankBound
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

theorem isSolvable_and_pRank_three_le_one_of_sz32
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 5 X = ⊥)
    {N : Subgroup X} (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    Group.IsSolvable ↥N ∧ CFSG.Open.pRank 3 ⁅N, N⁆ ≤ 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K : Subgroup X := CFSG.generalizedFitting X with hKdef
  obtain ⟨hKs, -, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := 5) (by norm_num) hO hN
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  obtain hSz := CFSG.AGLEmbeddingD2.sz32Normal_of_mulEquiv d hd hKn hKC e
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hD := hSz.data T
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    rw [hT]
    exact normalizer_subgroupOf_le_of_isStronglyPEmbedded hN hPK
      (P.isPGroup'.to_le inf_le_left) (inf_le_left.trans hPN) inf_le_right
  have hne : N.subgroupOf K ≠ ⊤ := fun h =>
    CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
      (Subgroup.subgroupOf_eq_top.mp h)
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := by
    refine ⟨?_, fun Y hY => ?_⟩
    · intro htop
      have h1 := hD.card_normalizer
      rw [htop, Subgroup.card_top, hSz.card] at h1
      norm_num at h1
    · rcases hD.maximal hY.le with h | h
      · exact absurd h hY.ne'
      · exact h
  have hOuterCard : Nat.card (Outer ↥K) ∣ 5 := by
    change Nat.card (MulAut ↥K ⧸ inner ↥K) ∣ 5
    rw [← Subgroup.index_eq_card]
    exact hSz.outer
  haveI : IsCyclic (Outer ↥K) := isCyclic_of_card_dvd_prime (p := 5) hOuterCard
  have hout : Group.IsSolvable (Outer ↥K) :=
    Group.isSolvable_of_comm fun a b =>
      (IsCyclic.isMulCommutative (α := Outer ↥K)).is_comm.comm a b
  refine ⟨isSolvable_of_isCoatom_normalizer hKC hout hmax hD.isSolvable_normalizer hle hne, ?_⟩
  have hcardX : Nat.card X ∣ 32537600 * 5 := by
    rw [← Subgroup.card_mul_index K, hSz.card]
    exact mul_dvd_mul_left 32537600 hSz.index_dvd_five
  have h3X : ¬ 3 ∣ Nat.card X := by
    intro h3
    have h3' : 3 ∣ 32537600 * 5 := h3.trans hcardX
    norm_num at h3'
  have h3comm : ¬ 3 ∣ Nat.card (⁅N, N⁆ : Subgroup X) := fun h =>
    h3X (h.trans ((Subgroup.card_dvd_of_le (Subgroup.commutator_le_self N)).trans
      (by simpa using Subgroup.card_dvd_of_le (show N ≤ (⊤ : Subgroup X) from le_top))))
  have hle0 := CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ
    (G := X) (H := ⁅N, N⁆) (p := 3) (k := 0) (by norm_num) (by simpa using h3comm)
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo

module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLemma44
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Type
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBComponent
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBModule
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBLTwo
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBBlock
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (PstarSet)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)

variable {Ω : Type} [Group Ω] [Finite Ω] {G : Subgroup Ω}

open scoped IsMulCommutative

private theorem not_isAlt_three_btype {M : Type} [Group M] (hq : CFSG.IsQuasisimple M) :
    ¬ CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt M 3 := by
  rintro ⟨e⟩
  obtain ⟨a, b, hab⟩ := hq.2.2
  have hcard : Nat.card M = 3 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hfact : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcyc : IsCyclic M := isCyclic_of_prime_card hcard
  exact hab (mul_comm a b)

private theorem isGomi410Type_or_hasGomiBlock_of_isSLn_or_isAlt_btype {W B : Subgroup Ω}
    {M : Subgroup (MulAut ↥W)} [IsMulCommutative ↥W] (hB : IsGomi410bComponent G W B M)
    (hW2 : ∀ w : ↥W, w ^ 2 = 1) (h37 : GomiFact37Two) {Y S' : Subgroup (MulAut ↥W)}
    (hP : (Pset Y).Nonempty) (hSyl : IsSylowIn 2 S' Y) (hMY : M ≤ Y)
    (hMsub : (M.subgroupOf Y).IsSubnormal)
    (ht : ∃ m : ℕ, 2 ≤ m ∧
      (IsSLn ↥M 2 m ∨ CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt ↥M (2 * m - 1)))
    (hM3 : ¬ CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt ↥M 3)
    (hMP : ⁅M, sSup (PstarSet Y)⁆ ≠ ⊥) :
    IsGomi410Type G B ∨ HasGomiBlock G :=
  hB.isGomi410Type_or_hasGomiBlock hW2 h37
    ⟨hP, hSyl, hMY, hMsub, Or.inl ht, fun h => absurd h hM3⟩ hMP

open scoped IsMulCommutative in
theorem IsGomi410bSetting.isGomi410Type_or_hasGomiBlock {S L H W : Subgroup Ω}
    [IsMulCommutative ↥W] (hset : IsGomi410bSetting G S L H W) (hS : IsSylowTwoOf S G)
    (h43 : GomiHyp43 G) (h37 : GomiFact37Two) (h44 : GomiLemma44) {M : Subgroup (MulAut ↥W)}
    (hMY : M ≤ autOn H W) (hMc : CFSG.IsComponent (M.subgroupOf (autOn H W)))
    (hM2 : CFSG.pCore 2 ↥M = ⊥) (hMJ : ⁅M, ffJ (autOn H W)⁆ ≠ ⊥)
    (hMP : ⁅M, sSup (PstarSet (autOn H W))⁆ ≠ ⊥) {B : Subgroup Ω}
    (hB : IsGomi410bComponent G W B M) : IsGomi410Type G B ∨ HasGomiBlock G := by
  obtain ⟨hW2, -, hP, hSyl, hsec⟩ := hset.moduleSetting hS
  have hT : GomiHyp43Type ↥M := h44 G h43 ↥W hW2 (autOn H W) hsec M hMY hMc hM2 hMJ
  have hMq : CFSG.IsQuasisimple ↥M :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMY).symm hMc.1
  have hM3 : ¬ CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt ↥M 3 :=
    not_isAlt_three_btype hMq
  obtain ⟨e⟩ := hB.quotient_equiv
  rcases hT with ⟨hC, hU3, hSz⟩ | ⟨n, hn7, ⟨g⟩⟩
  · by_cases hL2 : IsGomiL2 (↥M ⧸ Subgroup.center ↥M)
    · rcases nonempty_mulEquiv_of_isGomiL2 hMq hM2 hL2 with h5 | ⟨m, hm3, ⟨eSL⟩⟩
      · obtain ⟨e5⟩ := h5
        refine isGomi410Type_or_hasGomiBlock_of_isSLn_or_isAlt_btype hB hW2 h37 hP hSyl hMY
          hMc.2 ⟨3, by norm_num, ?_⟩ hM3 hMP
        right
        change Nonempty (↥M ≃* alternatingGroup (Fin (2 * 3 - 1)))
        rw [show 2 * 3 - 1 = 5 by norm_num]
        exact ⟨e5⟩
      · have hm0 : m ≠ 0 := by omega
        have hSL : IsSLn ↥M 2 m :=
          ⟨GaloisField 2 m, inferInstance, inferInstance, GaloisField.card 2 m hm0,
            ⟨eSL.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
              (GaloisField 2 m))⟩⟩
        exact isGomi410Type_or_hasGomiBlock_of_isSLn_or_isAlt_btype hB hW2 h37 hP hSyl hMY
          hMc.2 ⟨m, by omega, Or.inl hSL⟩ hM3 hMP
    · have eZ := QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) e
        (Subgroup.map_center_eq e)
      exact Or.inl (Or.inl ⟨hC.of_mulEquiv e.symm, fun h => hL2 (h.of_mulEquiv eZ),
        fun h => hU3 (h.of_mulEquiv eZ), fun h => hSz (h.of_mulEquiv eZ)⟩)
  · obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · have hk3 : 3 ≤ k := by omega
      refine Or.inl (Or.inr (Or.inl ⟨k, hk3, ?_⟩))
      rw [← hk]
      exact ⟨e.trans g⟩
    · have hkn : 2 * (k + 1) - 1 = n := by omega
      refine isGomi410Type_or_hasGomiBlock_of_isSLn_or_isAlt_btype hB hW2 h37 hP hSyl hMY
        hMc.2 ⟨k + 1, by omega, ?_⟩ hM3 hMP
      right
      change Nonempty (↥M ≃* alternatingGroup (Fin (2 * (k + 1) - 1)))
      rw [hkn]
      exact ⟨g⟩

end CFSG.GroupTheory

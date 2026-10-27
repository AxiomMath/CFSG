module

public import CFSG.GroupTheory.SylowIntersectionControl.Selection
public import CFSG.GroupTheory.AschbacherBlock
import CFSG.CGT.PushingUpLit.SubnormalTwoGroup
import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellShort
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne

variable {Ω : Type} [Group Ω]

structure IsGomiTwoComponent (G B : Subgroup Ω) : Prop where
  le : B ≤ G
  subnormal : (B.subgroupOf G).IsSubnormal
  residual : oResidualTwo ↥B = ⊤
  quotient : IsQuasisimple (↥B ⧸ pCore 2 ↥B) ∨
    ((Nat.card (↥B ⧸ pCore 2 ↥B)).Prime ∧ Odd (Nat.card (↥B ⧸ pCore 2 ↥B)))

theorem commutator_pCoreOf_eq_of_isSubnormal [Finite Ω] {G B : Subgroup Ω} (hBG : B ≤ G)
    (hsub : (B.subgroupOf G).IsSubnormal) (hB : oResidualTwo ↥B = ⊤) :
    ⁅pCoreOf 2 G, B⁆ = ⁅pCoreOf 2 B, B⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hGQ : G ≤ Subgroup.normalizer ((pCoreOf 2 G : Subgroup Ω) : Set Ω) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
  have hBQ := hBG.trans hGQ
  have hQB : pCoreOf 2 G ≤ Subgroup.normalizer (B : Set Ω) :=
    CFSG.CGT.PushingUpLit.SubTwo.le_normalizer_of_isSubnormal_sup
      (CFSG.CGT.PushingUpLit.SubTwo.noTwoQuotient_of_oResidualTwo hB) hQ2 hBQ
      (isSubnormal_subgroupOf_of_le (sup_le hBG hQG) hsub)
  have hRQ : pCoreOf 2 B ≤ pCoreOf 2 G :=
    CFSG.QuasithinUnique.Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hBG hsub
  have hcomm : ⁅pCoreOf 2 G, B⁆ ≤ pCoreOf 2 B := by
    have h1 : ⁅pCoreOf 2 G, B⁆ ≤ pCoreOf 2 G ⊓ B :=
      le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hBQ)
        (Subgroup.le_normalizer_iff_commutator_le_right.mp hQB)
    refine h1.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (hQ2.to_le inf_le_left))
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxQ, hxB⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hBQ hb) x).mp hxQ,
        B.mul_mem (B.mul_mem hb hxB) (B.inv_mem hb)⟩
    · rintro ⟨hxQ, hxB⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hBQ hb) x).mpr hxQ, ?_⟩
      have := B.mul_mem (B.mul_mem (B.inv_mem hb) hxB) hb
      simpa [mul_assoc] using this
  have hL : ∀ (N : Subgroup B) [N.Normal], IsPGroup 2 (B ⧸ N) → N = ⊤ := by
    intro N hN hN2
    rw [eq_top_iff, ← hB]
    exact sInf_le ⟨hN, hN2⟩
  refine le_antisymm ?_ (Subgroup.commutator_mono hRQ le_rfl)
  exact (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
    hL hQ2 hBQ).ge.trans (Subgroup.commutator_mono hcomm le_rfl)

section Frame

variable [Finite Ω]

@[expose] def HasGomiBlock (G : Subgroup Ω) : Prop :=
  ∃ B : Subgroup ↥G, IsAschbacherBlockGomi B

structure Gomi410Cex (f : PSubgroupSelection 2 Ω) (hyp : Subgroup Ω → Prop) (G : Subgroup Ω) :
    Prop where
  hyp_self : hyp G
  singular : ¬ f.IsRegular G
  not_block : ¬ HasGomiBlock G
  minimal : ∀ H : Subgroup Ω, H < G → pCoreOf 2 G ≤ H → hyp H → ¬ f.IsRegular H →
    HasGomiBlock H

theorem hasGomiBlock_of_cex {f : PSubgroupSelection 2 Ω} {hyp : Subgroup Ω → Prop}
    (hcex : ∀ G : Subgroup Ω, Gomi410Cex f hyp G → f.IsRegular G) (G : Subgroup Ω)
    (hG : hyp G) (hs : ¬ f.IsRegular G) : HasGomiBlock G := by
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    by_contra hno
    refine hs (hcex G ⟨hG, hs, hno, fun H hHG _ hH hsH => ?_⟩)
    exact ih (Nat.card H) (hn ▸ Subgroup.card_lt_of_lt hHG) H hH hsH rfl

end Frame

end CFSG.GroupTheory

end

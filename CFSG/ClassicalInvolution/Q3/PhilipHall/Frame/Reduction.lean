module

public import CFSG.ClassicalInvolution.Q3.Q3TLMain
import CFSG.GH74.GLS.Balance.Bender.Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.Q3TMFSBalance
public import CFSG.ClassicalInvolution.Q3.Q3TMFSCases
public import CFSG.ClassicalInvolution.Q3.Q3TMFSMember

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3T.MFS

section Simple

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)]

theorem simpleGroup_of_le_fstar {K : Subgroup Y}
    (hgen : Subgroup.normalClosure (K : Set Y) = ⊤) (hKT : K ≤ genFittingFStar Y) :
    IsSimpleGroup Y := by
  have : (genFittingFStar Y).Normal := fstar_normal
  have htop : genFittingFStar Y = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact Subgroup.normalClosure_le_normal hKT
  let e : genFittingFStar Y ≃* Y := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  exact e.symm.isSimpleGroup

end Simple

section Member

variable {Y : Type} [Group Y] [Finite Y]

theorem three_mem_of_member (hBelow : CIT3Below (Nat.card Y))
    (hO : classicalInvolutionOddCore Y = ⊥) {z : Y} {L : Subgroup Y} (hz : IsClassicalMember3 L z)
    {T : Subgroup Y} (hT : IsComponentOf T ⊤) (hTL : T ⊔ L = ⊤)
    (hgen : Subgroup.normalClosure (L : Set Y) = ⊤) (hconn : NonCommConnected (Q3B.conjClass L))
    [hTn : T.Normal] (hCT : Subgroup.centralizer (T : Set Y) = ⊥)
    (hmem : ∃ (z' : T) (L' : Subgroup T), IsClassicalMember3 L' z') :
    ∀ x ∈ L, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ T := by
  intro x hx h3
  by_cases hTY : T = ⊤
  · rw [hTY]
    exact Subgroup.mem_top x
  obtain ⟨z', L', hL'⟩ := hmem
  have hqs : CFSG.Open.IsQuasisimple T := hT.2.2
  have hZ : Subgroup.center T = ⊥ := by
    refine eq_bot_iff.mpr fun c hc => ?_
    have hc' : (c : Y) ∈ Subgroup.centralizer (T : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨t, ht⟩)
    rw [hCT, Subgroup.mem_bot] at hc'
    exact Subgroup.mem_bot.mpr (Subtype.ext hc')
  have hgen' : Subgroup.normalClosure (L' : Set T) = ⊤ := by
    rcases Q3T.normal_le_center_or_eq_top_qs hqs Subgroup.normalClosure_normal with h | h
    · exfalso
      have h1 := h (Subgroup.subset_normalClosure hL'.mem)
      rw [hZ, Subgroup.mem_bot] at h1
      exact hL'.ne_one h1
    · exact h
  have hcard : Nat.card T < Nat.card Y := by
    rw [← Subgroup.card_top (G := Y)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hTY)
  have hLie := hBelow T hcard _ (Q3B.inClass3_conjClass hL' hgen')
  have hOT := Q3T.oddCore_eq_bot_of_quasisimple hqs hZ hL'.orderOf_eq_two
  obtain ⟨ι, _, ⟨S⟩⟩ := hLie
  let e : T ⧸ classicalInvolutionOddCore T ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hOT).trans QuotientGroup.quotientBot
  obtain ⟨i, hi⟩ := Q3T.exists_eq_top_of_commute hqs hZ
    (fun i => (e.toMonoidHom.comp (S.hom i)).range)
    (fun i j hij x hx y hy => by
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      show e (S.hom i a) * e (S.hom j b) = e (S.hom j b) * e (S.hom i a)
      rw [← map_mul, ← map_mul, S.commute i j hij a b])
    (by
      simp only [MonoidHom.range_comp]
      rw [← Subgroup.map_iSup, S.generate]
      exact Subgroup.map_top_of_surjective _ e.surjective)
  have hsurj : Function.Surjective (e.toMonoidHom.comp (S.hom i)) :=
    MonoidHom.range_eq_top.mp hi
  have hker : (e.toMonoidHom.comp (S.hom i)).ker ≤ Subgroup.center (S.kind i).G := by
    intro y hy
    refine S.ker_le_center i ?_
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (MulEquiv.map_eq_one_iff e).mp hy
  exact Q3T.three_mem_of_component Q3T.d4OuterThree3_proved hBelow hO hz hT hTL hgen hconn hCT
    hZ (S.valid i) _ hsurj hker x hx h3

theorem le_of_setting (hBelow : CIT3Below (Nat.card Y)) {z : Y} {K T : Subgroup Y}
    (hS : Setting z K T)
    (hMF : (∀ (z' : T) (L' : Subgroup T), ¬ IsClassicalMember3 L' z') →
      memberIndex K T = 3 → False) : K ≤ T := by
  have : T.Normal := hS.normal
  by_cases hmem : ∃ (z' : T) (L' : Subgroup T), IsClassicalMember3 L' z'
  · exact Q3T.le_of_almostSimple_member Q3T.modelOddAutRigid_proved hBelow hS.member hS.comp
      hS.cent (Q3T.isClassicalMember3_inf_of_three_mem hS.member
        (three_mem_of_member hBelow hS.oddCore hS.member hS.comp hS.sup hS.gen hS.conn hS.cent
          hmem))
  · have hfree : ∀ (z' : T) (L' : Subgroup T), ¬ IsClassicalMember3 L' z' :=
      fun z' L' h => hmem ⟨z', L', h⟩
    exfalso
    rcases memberIndex_cases (T := T) hS.member with h1 | h3 | h12 | h24
    · exact hfree _ _ ((isClassicalMember3_inf_of_memberIndex_eq_one hS.member hS.sup h1).subgroupOf
        inf_le_right)
    · exact hMF hfree h3
    · exact typeABExcluded_of_solvBalance CFSG.GH74.GLS.Balance.solvableL2PrimeBalance_proved
        Y z K T hS (Or.inl h12)
    · exact typeABExcluded_of_solvBalance CFSG.GH74.GLS.Balance.solvableL2PrimeBalance_proved
        Y z K T hS (Or.inr h24)

end Member

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

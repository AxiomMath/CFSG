module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompList
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDownAux

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremB.MovingAround (SporTables.SporTypes)

theorem not_isList93_of_spor_comp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hN2 : ∀ (S : Type) [Group S] (j : TauCeti.CFSGIndex), List93.NotChev2Idx j →
      Nonempty (S ≃* j.Group) → ¬ IsChevSimple 2 S)
    {name : TauCeti.SporadicName} (hname : ∃ r, k2Spor r name)
    (hT : SporTables.SporTypes p (fun T _ => ¬ catalogIs T (S9.isList93 p)) name)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (e : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group)) (α : MulAut S)
    (hα : α ^ p = 1) (I : Subgroup S)
    (hI : GLAPComponent p (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I) :
    ¬ catalogIs (PSimple p I) (S9.isList93 p) := by
  haveI := hS
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 :=
    hOut S hS hnab name e
  by_cases hα1 : α = 1
  · rw [hα1, CFSG.LocalAnalysis.GLTheoremA.rtd_fixSubgroup_one] at hI
    obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.rtd_nonempty_pSimple_equiv_top hp hnab hI
    exact not_isList93_of_sporadic hN2 hname ⟨f.trans e.some⟩
  · have hcop : Nat.Coprime p
        (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) :=
      CFSG.HardMathSupport.Timmesfeld.Coordinator.coprime_of_le_two hp hp2
        Nat.card_pos.ne' hout
    have hαp : IsPGroup p (Subgroup.zpowers α) := by
      haveI : Fact p.Prime := ⟨hp⟩
      exact IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime hα hα1, pow_one])
    obtain ⟨x, rfl⟩ := CFSG.HardMathSupport.Timmesfeld.Coordinator.le_inner_of_isPGroup
      hcop hαp (Subgroup.mem_zpowers α)
    have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot hcen
    have hxo : orderOf x = p := by
      haveI : Fact p.Prime := ⟨hp⟩
      rw [← orderOf_injective _ hinj x]
      exact orderOf_eq_prime hα hα1
    rw [CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415.fixSubgroup_conj] at hI
    exact hT S e x hxo I hI

end CFSG.LocalAnalysis.GLTheoremA

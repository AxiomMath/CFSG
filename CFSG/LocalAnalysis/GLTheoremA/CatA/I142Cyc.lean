module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Setup
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement


theorem centFix_zpowers {X : Type*} [Group X] (β : MulAut X) :
    centFix (Subgroup.zpowers β) = fixSubgroup β := by
  ext x
  rw [mem_centFix, mem_fixSubgroup]
  constructor
  · intro h
    exact h β (Subgroup.mem_zpowers β)
  · intro hx e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    have hβs : β ∈ MulAction.stabilizer (MulAut X) x := MulAction.mem_stabilizer_iff.2 hx
    exact MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer (MulAut X) x).zpow_mem hβs k)

theorem centFix_bot {X : Type*} [Group X] : centFix (⊥ : Subgroup (MulAut X)) = ⊤ := by
  ext x
  simp only [mem_centFix, Subgroup.mem_bot, Subgroup.mem_top, iff_true]
  intro e he
  rw [he]
  rfl

theorem isQuasisimple_of_simple_nonabelian {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) : CFSG.Open.IsQuasisimple S := by
  have hcomm : commutator S = ⊤ := by
    haveI : (commutator S).Normal := Subgroup.commutator_normal ⊤ ⊤
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  have hcen : Subgroup.center S = ⊥ := by
    haveI : (Subgroup.center S).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have ha : a ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
  refine ⟨hcomm, ?_⟩
  exact MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans (QuotientGroup.quotientBot))

theorem perfect_le_layer_top {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (P : Subgroup S) :
    P ≤ GLALayer (⊤ : Subgroup S) := by
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup S) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv.symm : S ≃* ↥(⊤ : Subgroup S)) (isQuasisimple_of_simple_nonabelian hS hnc)
  have hcomp : CFSG.Open.IsComponentOf (⊤ : Subgroup S) (⊤ : Subgroup S) :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hq⟩
  exact le_trans le_top (le_sSup (show (⊤ : Subgroup S) ∈
    {M : Subgroup S | CFSG.Open.IsComponentOf M (⊤ : Subgroup S)} from hcomp))

theorem lieSemisimpleCentE_zpowers_of_lie (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hiso : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ idx.1.characteristic) (β : MulAut S) (hβ : β ^ p = 1) :
    ∀ P : Subgroup S, P ≤ centFix (Subgroup.zpowers β) → ⁅P, P⁆ = P →
      P ≤ GLALayer (centFix (Subgroup.zpowers β)) := by
  by_cases hβ1 : β = 1
  · subst hβ1
    rw [Subgroup.zpowers_one_eq_bot, centFix_bot]
    intro P _ _
    exact perfect_le_layer_top hS hnc P
  · intro P hP hPperf
    rw [centFix_zpowers] at hP ⊢
    have key := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent S hS hnc
      idx hiso p hp hp2 hpq β hβ hβ1
    exact key P hP hPperf

@[reducible, expose] def ResidualCyc : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 2 S → ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        idx.1.characteristic = p) →
      ∀ β : MulAut S, β ^ p = 1 → ∀ P : Subgroup S, P ≤ centFix (Subgroup.zpowers β) →
        ⁅P, P⁆ = P → P ≤ GLALayer (centFix (Subgroup.zpowers β))

@[reducible, expose] def ResidualNonCyc : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 2 S → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup (MulAut S),
      IsElemAbelian p E → (¬ ∃ β : MulAut S, E = Subgroup.zpowers β) →
        ∀ P : Subgroup S, P ≤ centFix E → ⁅P, P⁆ = P → P ≤ GLALayer (centFix E)

theorem lieSemisimpleCentE_of_residuals (hc : ResidualCyc) (hn : ResidualNonCyc) :
    LieSemisimpleCentE := by
  intro S _ _ hS hnc hchev p hp hp2 E hE P hP hperf
  by_cases hcyc : ∃ β : MulAut S, E = Subgroup.zpowers β
  · obtain ⟨β, rfl⟩ := hcyc
    have hβ : β ^ p = 1 := hE.2 β (Subgroup.mem_zpowers β)
    by_cases hidx : ∃ idx : TauCeti.ValidLieTypeIndex,
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧ p ≠ idx.1.characteristic
    · obtain ⟨idx, hiso, hpq⟩ := hidx
      exact lieSemisimpleCentE_zpowers_of_lie S hS hnc idx hiso hp hp2 hpq β hβ P hP hperf
    · exact hc S hS hnc hchev p hp hp2 (fun idx hiso => by
        by_contra hne
        exact hidx ⟨idx, hiso, fun h => hne h.symm⟩) β hβ P hP hperf
  · exact hn S hS hnc hchev p hp hp2 E hE hcyc P hP hperf

end CFSG.LocalAnalysis.GLTheoremA.I142

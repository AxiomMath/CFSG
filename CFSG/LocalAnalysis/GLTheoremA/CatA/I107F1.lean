module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107Of
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement


@[expose] def ChevTwoNonabelian : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsChevSimple 2 S → ∃ a b : S, a * b ≠ b * a

theorem isChevSimple_two_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsChevSimple 2 B) :
    IsChevSimple 2 A := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩

theorem center_eq_bot_of_simple_nonab {S : Type} [Group S] [IsSimpleGroup S] {a b : S} (hab : a * b ≠ b * a) :
    Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have ha : a ∈ Subgroup.center S := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem commutator_eq_top_of_simple_nonab {S : Type} [Group S] [IsSimpleGroup S] {a b : S} (hab : a * b ≠ b * a) :
    commutator S = ⊤ := by
  haveI : (commutator S).Normal := Subgroup.commutator_normal ⊤ ⊤
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    have hmem : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hab hmem
  · exact h

theorem i107LabelAt_of_nonab (hNA : ChevTwoNonabelian) : I107LabelAt := by
  intro S _ _ hS hchev
  obtain ⟨a, b, hab⟩ := hNA S hS hchev
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hab
  let e : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hq : CFSG.Open.IsQuasisimple S := ⟨commutator_eq_top_of_simple_nonab hab, e.isSimpleGroup⟩
  have hchevQ : IsChevSimple 2 (S ⧸ Subgroup.center S) := isChevSimple_two_of_mulEquiv e hchev
  exact rk2_exists_label (CFSG.StandardType.ChevTwo.ys08_holds S hq hchevQ)

theorem i107LabelAt_holds (hNA : ChevTwoNonabelian) : I107LabelAt :=
  i107LabelAt_of_nonab hNA

end CFSG.LocalAnalysis.GLTheoremA

end

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.RuStd
  CFSG.EvenSporadicStandard.Induction.TMem

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

theorem ru_conj_u (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u) :
    ∀ w ∈ L, orderOf w = 2 → (∀ k ∈ K, k * w = w * k) → ∃ x ∈ L, x * u * x⁻¹ = w := by
  intro w hwL hw2 hwK
  have hQw : RuPair H L K w := ⟨hwL, hw2, hQ.2.2.1, hwK, hQ.2.2.2.2⟩
  have hcu := card_centralizer_of_ruPair hL hQ
  have hcw := card_centralizer_of_ruPair hL hQw
  have hu2 : orderOf (⟨u, hQ.1⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hQ.2.1
  have hw2' : orderOf (⟨w, hwL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hw2
  have hcu' : Nat.card (centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L)) = 116480 := by
    rw [card_centralizer_subtype L ⟨u, hQ.1⟩]; exact hcu
  have hcw' : Nat.card (centralizer ({(⟨w, hwL⟩ : ↥L)} : Set ↥L)) = 116480 := by
    rw [card_centralizer_subtype L ⟨w, hwL⟩]; exact hcw
  obtain ⟨x, hx⟩ := isConj_iff.1 ((ruFacts_of_isSporadic hL).isConj_B _ _ hu2 hw2' hcu' hcw')
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem ru_uniq (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u) :
    ∀ K'' : Subgroup H, K'' ≤ L → (∀ k ∈ K'', k * u = u * k) → Group.IsPerfect ↥K'' →
      Nat.card ↥K'' = Nat.card ↥K → K'' = K := by
  intro K'' hK''L hK''u hperf hcard
  have hder := ruPair_eq_derived hf hL hQ
  have hle : K'' ≤ K := by
    rw [hder]
    exact le_commutator_of_perfect_of_le (Group.isPerfect_def.1 hperf) fun x hx =>
      ⟨hK''L hx, mem_centralizer_singleton_iff.2 (hK''u x hx)⟩
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem ru_small (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u) :
    ∀ S : Subgroup H, S ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥S →
      Nat.card ↥S < 2 ^ twoAdic K := by
  intro S hS _
  have h4 : Nat.card ↥S ≤ 4 := by
    have := Subgroup.card_le_of_le hS
    rwa [hf.card_centralizer H L K u hL hQ] at this
  refine lt_two_pow_twoAdic (m := 3) ?_ (by omega)
  rw [hQ.2.2.2.2]
  norm_num

theorem tMemOfNotMax_ru_proved (hf : RuLocalFacts) (hmult : OddMultTrivial .Ru) :
    TMemOfNotMax [.Ru] (fun _ => RuPair) := by
  intro s hs H _ _ N L K t u hcov hhyp hQ hnm
  rcases List.mem_singleton.1 hs with rfl
  by_contra htN
  have hL : IsSporadic ↥L .Ru := hcov.isSporadic_of_mult hmult
  have hinn : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l := fun α =>
    TwoRu.HypOne.allInner_of_isSporadic hL α
  have hq := ruPair_isQuasisimple hf hL hQ
  have hKq : CFSG.Open.IsQuasisimple ↥K :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).1 hq
  have D : TMemData H N L K u :=
    TMemData.of_inner hhyp htN hQ.1 hinn hq.1 hQ.2.2.2.1 (ru_conj_u hL hQ) (ru_uniq hf hL hQ)
  exact hnm (D.maximal hKq (ru_small hf hL hQ))

end CFSG.EvenSporadicStandard.Induction

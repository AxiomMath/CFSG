module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.KGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ReachGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.KFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

theorem isSporadic_equiv {X Y : Type} [Group X] [Group Y] {s : TauCeti.SporadicName}
    (e : X ≃* Y) (h : IsSporadic X s) : IsSporadic Y s := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem card_of_isSporadic {X : Type} [Group X] {s : TauCeti.SporadicName} {n : ℕ}
    (hs : Nat.card (Carrier s) = n) (h : IsSporadic X s) : Nat.card X = n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact hs

theorem not_isSporadic_of_card_ne {Y : Type} [Group Y] {s : TauCeti.SporadicName} {n m : ℕ}
    (hY : Nat.card Y = m) (hs : Nat.card (Carrier s) = n) (hne : m ≠ n) : ¬ IsSporadic Y s :=
  fun h => hne (hY.symm.trans (card_of_isSporadic hs h))

theorem fi23Excl_of_card_ne {s : TauCeti.SporadicName} {n N : ℕ}
    (hsimple : IsSimpleGroup (Carrier .Fi23)) (h23 : Nat.card (Carrier .Fi23) = N)
    (hnp : ¬ N.Prime) (hs : Nat.card (Carrier s) = n) (hne : n ≠ N) : Fi23Excl s := by
  intro X _ hX hXs
  have hXsimple : IsSimpleGroup X := by
    obtain ⟨e⟩ := hX
    have := hsimple
    exact MulEquiv.isSimpleGroup e
  have hXcard : Nat.card X = N := card_of_isSporadic h23 hX
  have hq : Nat.card (X ⧸ center X) = N := by
    rw [card_quotient_center_of_isSimpleGroup (by rwa [hXcard]), hXcard]
  exact hne ((card_of_isSporadic hs hXs).symm.trans hq)

theorem fiNotExc_of_card {G : Type} [Group G] {N c : ℕ} (hG : Nat.card G = N)
    (h1 : c * (c ^ 2 - 1) < 2 * N) (h2 : 2 * N < (c + 1) * ((c + 1) ^ 2 - 1))
    (hA7 : N ≠ 2520) : NotExc G :=
  notExc_of_card_group hG h1 h2 hA7

theorem fiSporadicNotExc_of_card {s : TauCeti.SporadicName} {N c : ℕ}
    (hs : Nat.card (Carrier s) = N) (h1 : c * (c ^ 2 - 1) < 2 * N)
    (h2 : 2 * N < (c + 1) * ((c + 1) ^ 2 - 1)) (hA7 : N ≠ 2520) : SporadicNotExc s :=
  fun _ _ h => fiNotExc_of_card (card_of_isSporadic hs h) h1 h2 hA7

theorem oddCentralExt_finite {D X : Type} [Group D] [Finite D] [Group X]
    (h : IsOddCentralExt D X) : Finite X := by
  obtain ⟨-, π, hπs, -, hπo⟩ := h
  have hker : Finite π.ker := Nat.finite_of_card_ne_zero hπo.pos.ne'
  have hq : Finite (X ⧸ π.ker) :=
    Finite.of_equiv D (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm.toEquiv
  exact Finite.of_subgroup_quotient π.ker

theorem isQuasisimple_quotient_oddCore {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple (X ⧸ CFSG.oddCore X) :=
  isQuasisimple_of_cover hq (QuotientGroup.mk' (CFSG.oddCore X)) (QuotientGroup.mk'_surjective _)
    (by
      rw [QuotientGroup.ker_mk']
      exact oddCore_le_center hq)

theorem isOddCentralExt_quot_of_equiv {D X : Type} [Group D] [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (e : (X ⧸ CFSG.oddCore X) ≃* D) :
    IsOddCentralExt D (X ⧸ CFSG.oddCore X) :=
  oddCentralExt_of_mulEquiv (isQuasisimple_quotient_oddCore hq) e

end CFSG.EvenSporadicStandard.Induction.Fi

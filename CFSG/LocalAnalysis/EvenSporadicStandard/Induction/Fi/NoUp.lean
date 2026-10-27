module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Step23
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Final

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

structure FiPinned : Prop where
  orders : FiOrders
  excl24 : Fi23Excl .Fi24Prime
  mult23 : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    IsSporadic (X ⧸ center X) .Fi23 → center X = ⊥
  mult24 : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    IsSporadic (X ⧸ center X) .Fi24Prime → Odd (Nat.card (center X))
  rank23 : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    IsSporadic (X ⧸ center X) .Fi23 → 3 ≤ CFSG.pRank 2 X
  rank24 : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    IsSporadic (X ⧸ center X) .Fi24Prime → 3 ≤ CFSG.pRank 2 X
  notExc23 : SporadicNotExc .Fi23
  notExc24 : SporadicNotExc .Fi24Prime

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

omit [Finite H] in
theorem fiNoUp_nil : FiNoUp [] H := fun _ _ _ h => absurd h List.not_mem_nil

theorem fiEvenOut_fi23 (pf : FiPinned) (Up : List TauCeti.SporadicName) :
    EvenCoverOutHered Up .Fi23 := by
  intro Y _ _ _ N' _ _ _ L' _ hq hcq hodd
  refine absurd ?_ hodd
  have hZ' := pf.mult23 ↥L' hq hcq
  have : Nat.card ↥(center ↥L') = 1 := by rw [hZ', Subgroup.card_bot]
  rw [this]
  exact odd_one

theorem fiEvenOut_fi24 (pf : FiPinned) (Up : List TauCeti.SporadicName) :
    EvenCoverOutHered Up .Fi24Prime := by
  intro Y _ _ _ N' _ _ _ L' _ hq hcq hodd
  exact absurd (pf.mult24 ↥L' hq hcq) hodd

theorem fiNoUp_fi24 (hsec : Link5bSection) (pf : FiPinned) (lit : Sol78Lit)
    (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {s₀ : TauCeti.SporadicName}
    (hnb : NoBiggerFi H s₀) (hlt : Nat.card (Carrier s₀) < Nat.card (Carrier .Fi24Prime)) :
    FiNoUp [.Fi24Prime] H := by
  intro Q hQ s'' hs'' h
  obtain rfl := List.mem_singleton.1 hs''
  have hQq : CFSG.IsQuasisimple ↥Q := hQ.isQuasisimple
  have hEven : EvenCoverOutHered [] .Fi24Prime := fiEvenOut_fi24 pf []
  have ihS : BelowSec (Sol78PredS [.Fi24Prime]) H :=
    BelowSec.mono_types (by simp [fiTypes]) ih
  have hmax : Maximal Q :=
    fiMaximal_of_central_type hsec
      (Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec ih.uHered)) ihS fiNoUp_nil hN
      hidx hkp hQ (by simp) h (Or.inl pf.excl24) hEven pf.notExc24
  have hstd : StdBare Q :=
    fiStdBare_of_maximal (lit.thm22 H ih.uHered) hkp hN hidx hmax (inL_ne_of_fStarSimple' hN hQ)
      (pf.rank24 ↥Q hQq h)
  have hcov : OddCover .Fi24Prime Q := ⟨hQq, pf.mult24 ↥Q hQq h, h⟩
  exact absurd (hnb Q .Fi24Prime (solStd_of_inL_stdBare hQ hstd) (by simp [fiTypes]) hcov)
    (not_le.2 hlt)

theorem fiNoUp_fi23 (hsec : Link5bSection) (pf : FiPinned) (lit : Sol78Lit)
    (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hup24 : FiNoUp [.Fi24Prime] H)
    (hnb : NoBiggerFi H .Fi22) : FiNoUp [.Fi23] H := by
  intro Q hQ s'' hs'' h
  obtain rfl := List.mem_singleton.1 hs''
  have hQq : CFSG.IsQuasisimple ↥Q := hQ.isQuasisimple
  have hZ : center ↥Q = ⊥ := pf.mult23 ↥Q hQq h
  have hEven : EvenCoverOutHered [.Fi24Prime] .Fi23 := fiEvenOut_fi23 pf [.Fi24Prime]
  have ihS : BelowSec (Sol78PredS [.Fi23]) H :=
    BelowSec.mono_types (by simp [fiTypes]) ih
  have hmax : Maximal Q :=
    fiMaximal_of_central_type hsec
      (Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec ih.uHered)) ihS hup24 hN hidx
      hkp hQ (by simp) h (Or.inr (by simp)) hEven pf.notExc23
  have hstd : StdBare Q :=
    fiStdBare_of_maximal (lit.thm22 H ih.uHered) hkp hN hidx hmax (inL_ne_of_fStarSimple' hN hQ)
      (pf.rank23 ↥Q hQq h)
  have hodd : Odd (Nat.card ↥(center ↥Q)) := by
    have : Nat.card ↥(center ↥Q) = 1 := by rw [hZ, Subgroup.card_bot]
    rw [this]
    exact odd_one
  have hcov : OddCover .Fi23 Q := ⟨hQq, hodd, h⟩
  exact absurd (hnb Q .Fi23 (solStd_of_inL_stdBare hQ hstd) (by simp [fiTypes]) hcov)
    (not_le.2 pf.orders.1)

theorem fiNoUpA (hsec : Link5bSection) (pf : FiPinned) :
    Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
      ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
        CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → NoBiggerFi H .Fi22 →
          FiNoUp [.Fi23, .Fi24Prime] H := by
  intro lit H _ _ ih N hN hidx hkp hnb
  have h24 : FiNoUp [.Fi24Prime] H :=
    fiNoUp_fi24 hsec pf lit ih hN hidx hkp hnb (pf.orders.1.trans pf.orders.2)
  have h23 : FiNoUp [.Fi23] H := fiNoUp_fi23 hsec pf lit ih hN hidx hkp h24 hnb
  intro Q hQ s'' hs'' h
  rcases List.mem_cons.1 hs'' with rfl | hs''
  · exact h23 Q hQ _ (by simp) h
  · obtain rfl := List.mem_singleton.1 hs''
    exact h24 Q hQ _ (by simp) h

theorem fiNoUpB (hsec : Link5bSection) (pf : FiPinned) :
    Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
      ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
        CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → NoBiggerFi H .Fi23 →
          FiNoUp [.Fi24Prime] H := by
  intro lit H _ _ ih N hN hidx hkp hnb
  exact fiNoUp_fi24 hsec pf lit ih hN hidx hkp hnb pf.orders.2

end CFSG.EvenSporadicStandard.Induction.Fi

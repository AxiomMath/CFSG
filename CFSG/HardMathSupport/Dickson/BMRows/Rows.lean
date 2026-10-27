module

public import CFSG.HardMathSupport.Dickson.BMRows.Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRows

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)

@[expose] def PCardCensus (p : ℕ) (Q : Type) [Group Q] (N : ℕ) : Prop :=
  ∀ x : Q, orderOf x = p → ∀ J : Subgroup Q,
    GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) J → Nat.card (PSimple p J) ∣ N

section Model

variable {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]

theorem row_of_census (hOut : SporadicOuterLeTwo) (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hnc : ∃ a c : Q, a * c ≠ c * a) {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p Q P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → I1416Rows.TypeOK p T) :
    I1416Rows.I1416SporRow s p :=
  I1416Rows.row_of_model hOut b hnc fun k hk I hI => hT _ (hC k hk I hI)

theorem qrow_of_census (hOut : SporadicOuterLeTwo) (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hnc : ∃ a c : Q, a * c ≠ c * a) {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p Q P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → I1416QRows.QTypeOK p T) :
    I1416QRows.I1416QRow s p :=
  I1416QRows.qrow_of_model hOut b hnc fun k hk I hI => hT _ (hC k hk I hI)

theorem arow_of_census (hOut : SporadicOuterLeTwo) (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hnc : ∃ a c : Q, a * c ≠ c * a) {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p Q P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → I1415Rows.ATypeOK p T) :
    I1415Rows.I1415Row s p :=
  I1415Rows.arow_of_model hOut b hnc fun k hk I hI => hT _ (hC k hk I hI)

theorem srow_of_census (hOut : SporadicOuterLeTwo) (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hnc : ∃ a c : Q, a * c ≠ c * a) {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p Q P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → SporAltRows.STypeOK p T) :
    SporAltRows.SRow s p :=
  SporAltRows.srow_of_model hOut b hnc fun k hk I hI => hT _ (hC k hk I hI)

theorem kdSporRow_of_census (hOut : SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (hp2 : p ≠ 2) {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p Q P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → kLevel p T ≤ 2) : KDSporRow s p :=
  KDSpor.kdSporRow_of_levelOK hOut b hnc hp hp2 fun k hk I hI => hT _ (hC k hk I hI)

theorem kdl227Row_of_census (hOut : SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus 3 Q P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → ¬ catalogIs T (onLie (isL2 27))) :
    KDL227Rows.KDL227SporRow s := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact KDL227Rows.kdl227Row_of_model hOut b hnc fun k hk1 hk3 J hJ =>
    hT _ (hC k (orderOf_eq_prime hk3 hk1) J hJ)

theorem row_of_cardCensus (hOut : SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a) {N : ℕ}
    (hC : PCardCensus p Q N) (hT : ∀ (T : Type) [Group T], Nat.card T ∣ N → I1416Rows.TypeOK p T) :
    I1416Rows.I1416SporRow s p :=
  I1416Rows.row_of_model hOut b hnc fun k hk I hI => hT _ (hC k hk I hI)

theorem qrow_of_cardCensus (hOut : SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a) {N : ℕ}
    (hC : PCardCensus p Q N)
    (hT : ∀ (T : Type) [Group T], Nat.card T ∣ N → I1416QRows.QTypeOK p T) :
    I1416QRows.I1416QRow s p :=
  I1416QRows.qrow_of_model hOut b hnc fun k hk I hI => hT _ (hC k hk I hI)

theorem arow_of_cardCensus (hOut : SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a) {N : ℕ}
    (hC : PCardCensus p Q N)
    (hT : ∀ (T : Type) [Group T], Nat.card T ∣ N → I1415Rows.ATypeOK p T) :
    I1415Rows.I1415Row s p :=
  I1415Rows.arow_of_model hOut b hnc fun k hk I hI => hT _ (hC k hk I hI)

end Model

end CFSG.HardMathSupport.Dickson.BMRows

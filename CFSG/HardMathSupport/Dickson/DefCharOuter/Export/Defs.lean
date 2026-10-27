module

public import CFSG.Yardstones.Md42047359a2a.Definitions
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.Yardstones.Md42047359a2a (LieFamily lieFamily)

structure OuterCentData (p : ℕ) {S : Type} [Group S] (β : MulAut S) : Prop where
  unique : ∀ I J : Subgroup S, GLAPComponent p (fixSubgroup β) I →
    GLAPComponent p (fixSubgroup β) J → I = J
  chev : ∀ I : Subgroup S, GLAPComponent p (fixSubgroup β) I → IsChevSimple p (PSimple p I)
  core : ¬ (p = 3 ∧ IsLTwoTwentySeven S) → GLAPPrimeCoreOf p (fixSubgroup β) = ⊥
  cent : ¬ (p = 3 ∧ IsLTwoTwentySeven S) → ∀ w : MulAut S, Nat.Coprime p (orderOf w) →
    w * β = β * w → (∀ x ∈ fixSubgroup β, w x = x) → w ∈ innerAut S
  noHatSix : p = 3 → ∀ I : Subgroup S, GLAPComponent 3 (fixSubgroup β) I →
    ¬ IsHatSix (↥I ⧸ GLAPPrimeCore 3 ↥I)
  l227 : p = 3 → ∀ I : Subgroup S, GLAPComponent 3 (fixSubgroup β) I →
    IsLTwoTwentySeven (PSimple 3 I) → ∀ β' : MulAut S, β' ^ 3 = 1 → β' * β = β * β' →
      I.map β'.toMonoidHom = I →
        ∃ i ∈ I, ∀ x ∈ I, β' x * (i * x * i⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 I

@[expose] def CarrierOn (F : LieFamily) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, lieFamily d.1 = F → d.1.characteristic ≠ 2 →
    Finite (TauCeti.CFSGIndex.lie d).Group ∧ IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group ∧
      ∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a

@[expose] def OuterCentOn (F : LieFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = F →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        ∀ p : ℕ, p.Prime → p ≠ 2 → p = idx.1.characteristic →
          ∀ β : MulAut S, orderOf β = p → β ∉ innerAut S → OuterCentData p β

@[expose] def OuterCentAll : Prop := ∀ F : LieFamily, CarrierOn F ∧ OuterCentOn F

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export

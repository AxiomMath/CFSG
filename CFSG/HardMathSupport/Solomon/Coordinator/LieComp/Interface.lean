module

public import CFSG.Yardstones.Md42047359a2a.Definitions
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a

structure LieCompData (q : ℕ) (H : Type) [Group H] : Prop where
  chev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q (H ⧸ Subgroup.center H)
  centre : Nonempty ((H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) →
    ¬ 3 ∣ Nat.card (Subgroup.center H)

@[expose] def NoThreeCover (S : Type) [Group S] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* S) → ¬ 3 ∣ Nat.card (Subgroup.center Y)

@[expose] def LieCompOn (F : LieFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = F →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → ∀ J : Subgroup S, GLAPComponent 3 (Lemma510Ns.fixSub β) J →
      LieCompData (lieIndexChar idx.1) (barOf 3 J) ∧
      (Nonempty ((barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≃* alternatingGroup (Fin 6)) →
        NoThreeCover S)

@[expose] def LieComp : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → ∀ J : Subgroup S, GLAPComponent 3 (Lemma510Ns.fixSub β) J →
      LieCompData (lieIndexChar idx.1) (barOf 3 J) ∧
      (Nonempty ((barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≃* alternatingGroup (Fin 6)) →
        NoThreeCover S)

theorem lieComp_of_families (h : ∀ F, LieCompOn F) : LieComp :=
  fun S _ _ hs hna idx he β hβ J hJ => h (lieFamily idx.1) S hs hna idx rfl he β hβ J hJ

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

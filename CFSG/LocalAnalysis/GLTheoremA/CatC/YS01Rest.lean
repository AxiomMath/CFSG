module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallRes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallFExist
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF12L3
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallAbs

@[expose] def SmallF12At (d : TauCeti.LieTypeIndex) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (hv : d.Valid), Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨d, hv⟩).Group) →
    ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → ¬ E ≤ inner S →
      Nat.card ↥(E ⊓ inner S) = 3 ^ 2 → SmallF2 S E ∧ SmallF1 S E

section Cert

theorem smallF12_of_rest
    (h : (∀ q : TauCeti.PrimePower, q.card = 27 → SmallF12At (.twistedA 2 q)) ∧ SmallF12At (.reeG2
        1)) (S : Type) [Group S] [Finite S]
    (d : TauCeti.ValidLieTypeIndex) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hd : IsRank3Small d.1) (E : Subgroup (MulAut S)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (hnot : ¬ E ≤ inner S) (hE0 : Nat.card ↥(E ⊓ inner S) = 3 ^ 2) : SmallF2 S E ∧ SmallF1 S E := by
  obtain ⟨ld, hv⟩ := d
  cases ld with
  | A n q =>
    rcases n with _ | _ | _ | n
    · exact (show False from hd).elim
    · exact (show False from hd).elim
    · obtain ⟨e⟩ := he
      exact KDRank3SmallF12L3.smallF2_smallF1_A2 S q hv hd e E hE hEc hnot hE0
    · exact (show False from hd).elim
  | twistedA n q =>
    rcases n with _ | _ | _ | n
    · exact (show False from hd).elim
    · exact (show False from hd).elim
    · exact h.1 q hd S hv he E hE hEc hnot hE0
    · exact (show False from hd).elim
  | reeG2 m =>
    have hm : m = 1 := hd
    subst hm
    exact h.2 S hv he E hE hEc hnot hE0
  | _ => exact (show False from hd).elim

theorem kdRank3Small_of_rest
    (h : (∀ q : TauCeti.PrimePower, q.card = 27 → SmallF12At (.twistedA 2 q)) ∧ SmallF12At (.reeG2
        1)) : KDRank3Small :=
  KDRank3SmallRes.kdRank3Small_of_residuals KDRank3SmallFExist.hExistRest_all
      (fun S _ _ d he hd E hE hEc hnot hE0 => (smallF12_of_rest h S d he hd E hE hEc hnot hE0).2)
      (fun S _ _ d he hd E hE hEc hnot hE0 => (smallF12_of_rest h S d he hd E hE hEc hnot hE0).1)
      KDRank3SmallF3.smallF3_all

end Cert

end CFSG.LocalAnalysis.GLTheoremA

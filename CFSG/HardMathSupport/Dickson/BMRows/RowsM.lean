module

public import CFSG.HardMathSupport.Dickson.BMRows.Rows

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.HardMathSupport.Timmesfeld.Proving (sporadicOuterLeTwo_holds)

theorem model_M :
    Finite (Carrier .M) ∧ IsSimpleGroup (Carrier .M) ∧
      Nonempty (Carrier .M ≃* (TauCeti.CFSGIndex.sporadic .M).Group) ∧
      ∃ a c : Carrier .M, a * c ≠ c * a := by
  have hcard : Nat.card (Carrier .M) = monsterOrder :=
    (Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv).trans
      CFSG.Milestones.fam_m_finiteness
  haveI : Finite (Carrier .M) :=
    CFSG.Sporadic.finite_carrier_M_of_card CFSG.Milestones.fam_m_finiteness
  haveI : IsSimpleGroup MonsterY443Derived := CFSG.Milestones.fam_m_simplicity
  haveI : IsSimpleGroup (Carrier .M) :=
    CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.isSimpleGroup
  refine ⟨inferInstance, inferInstance, CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv,
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ?_⟩
  rw [hcard]
  norm_num [monsterOrder]

section Rows


theorem row_M_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p (Carrier .M) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → I1416Rows.TypeOK p T) :
    I1416Rows.I1416SporRow .M p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact row_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem qrow_M_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p (Carrier .M) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → I1416QRows.QTypeOK p T) :
    I1416QRows.I1416QRow .M p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact qrow_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem arow_M_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p (Carrier .M) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → I1415Rows.ATypeOK p T) :
    I1415Rows.I1415Row .M p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact arow_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem srow_M_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p (Carrier .M) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → SporAltRows.STypeOK p T) :
    SporAltRows.SRow .M p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact srow_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem kdSporRow_M_of_census {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : TauCeti.CFSGIndex → Prop}
    (hC : PCompCensus p (Carrier .M) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → kLevel p T ≤ 2) : KDSporRow .M p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact kdSporRow_of_census sporadicOuterLeTwo_holds b hnc hp hp2 hC hT

theorem kdl227Row_M_of_census {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus 3 (Carrier .M) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → ¬ catalogIs T (onLie (isL2 27))) :
    KDL227Rows.KDL227SporRow .M := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact kdl227Row_of_census sporadicOuterLeTwo_holds b hnc hC hT

end Rows

end CFSG.HardMathSupport.Dickson.BMRows

module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed (I1430InnOther)

@[expose] def TriD4No (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 →
      KD264Lie.fieldSize d.1 = 2 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α β : MulAut S, α ∈ innAutDerived S → α ^ 3 = 1 → α ≠ 1 →
        β ∈ innAutDerived S → β ^ 3 = 1 → Commute α β →
        ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup α) J →
          catalogIs (PSimple 3 J) S9.isD4two → (∀ y ∈ J, β y ∈ J) →
          ∃ j ∈ J, ∀ y ∈ J, β y = j * y * j⁻¹

@[expose] def TriD4NoA : Prop :=
  TriD4No fun d => ∃ n q, d = .A n q

@[expose] def TriD4NoTwistedA : Prop :=
  TriD4No fun d => ∃ n q, d = .twistedA n q

@[expose] def TriD4NoB : Prop :=
  TriD4No fun d => ∃ n q, d = .B n q

@[expose] def TriD4NoD : Prop :=
  TriD4No fun d => ∃ n q, d = .D n q

@[expose] def TriD4NoTwistedD : Prop :=
  TriD4No fun d => ∃ n q, d = .twistedD n q

@[expose] def TriD4NoE6 : Prop :=
  TriD4No fun d => ∃ q, d = .E6 q

@[expose] def TriD4NoE78 : Prop :=
  TriD4No fun d => ∃ q, d = .E7 q ∨ d = .E8 q

@[expose] def TriD4NoF4 : Prop :=
  TriD4No fun d => ∃ q, d = .F4 q

@[expose] def TriD4NoOther : Prop :=
  TriD4No I1430InnOther

theorem triD4No_notTwE6 (hA : TriD4NoA) (htA : TriD4NoTwistedA) (hB : TriD4NoB)
    (hD : TriD4NoD) (htD : TriD4NoTwistedD) (hE6 : TriD4NoE6) (hE78 : TriD4NoE78)
    (hF4 : TriD4NoF4) (hO : TriD4NoOther) : TriD4No fun d => ¬ ∃ q, d = .twistedE6 q := by
  intro S _ _ hS hnc d hP hc hf hSd α β hα hα3 hα1 hβ hβ3 hαβ J hJ hT hβJ
  have key : ∀ {P : TauCeti.LieTypeIndex → Prop}, TriD4No P → P d.1 →
      ∃ j ∈ J, ∀ y ∈ J, β y = j * y * j⁻¹ := fun h hd =>
    h S hS hnc d hd hc hf hSd α β hα hα3 hα1 hβ hβ3 hαβ J hJ hT hβJ
  obtain ⟨d, hv⟩ := d
  cases d with
  | A n q => exact key hA ⟨n, q, rfl⟩
  | twistedA n q => exact key htA ⟨n, q, rfl⟩
  | B n q => exact key hB ⟨n, q, rfl⟩
  | C n q => exact key hO (Or.inl ⟨n, q, rfl⟩)
  | D n q => exact key hD ⟨n, q, rfl⟩
  | twistedD n q => exact key htD ⟨n, q, rfl⟩
  | E6 q => exact key hE6 ⟨q, rfl⟩
  | E7 q => exact key hE78 ⟨q, Or.inl rfl⟩
  | E8 q => exact key hE78 ⟨q, Or.inr rfl⟩
  | F4 q => exact key hF4 ⟨q, rfl⟩
  | G2 q => exact key hO (Or.inr (Or.inl ⟨q, rfl⟩))
  | twistedE6 q => exact absurd ⟨q, rfl⟩ hP
  | trialityD4 q => exact key hO (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))
  | suzuki m => exact key hO (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))))
  | reeG2 m => exact key hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))))
  | reeF4 m => exact key hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))))))
  | tits => exact key hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end

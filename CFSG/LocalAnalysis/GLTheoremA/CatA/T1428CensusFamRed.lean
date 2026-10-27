module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428U6D4Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428SuzukiCensusBody
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinearFinal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def CensusBody (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ η : MulAut (TauCeti.CFSGIndex.lie d).Group,
    η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      (TauCeti.CFSGIndex.lie d).Group →
    η ^ 3 = 1 → η ≠ 1 → ∀ r : ℕ, Odd r → 1 < r →
    ∀ J₁ J₂ J₃ : Subgroup (TauCeti.CFSGIndex.lie d).Group,
      CFSG.Open.IsComponentOf J₁ (fixSubgroup η) → CFSG.Open.IsComponentOf J₂ (fixSubgroup η) →
      CFSG.Open.IsComponentOf J₃ (fixSubgroup η) → J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ →
      catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r) →
      catalogIs (↥J₂ ⧸ Subgroup.center ↥J₂) (S10.isL2n r) →
      catalogIs (↥J₃ ⧸ Subgroup.center ↥J₃) (S10.isL2n r) →
      (catalogIs (TauCeti.CFSGIndex.lie d).Group (S10.isU6n r) ∧
        ∀ M : Subgroup (TauCeti.CFSGIndex.lie d).Group,
          CFSG.Open.IsComponentOf M (fixSubgroup η) →
            catalogIs (↥M ⧸ Subgroup.center ↥M) (S10.isL2n r)) ∨
      catalogIs (TauCeti.CFSGIndex.lie d).Group (isD4n r)

theorem t1428U6Census_iff :
    T1428U6Census ↔ ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 → CensusBody d :=
  Iff.rfl

@[expose] def CensusBodyTwistedA : Prop :=
  ∀ (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.twistedA n q, hv⟩

@[expose] def CensusBodyB : Prop :=
  ∀ (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B n q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.B n q, hv⟩

@[expose] def CensusBodyD : Prop :=
  ∀ (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D n q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.D n q, hv⟩

@[expose] def CensusBodyTwistedD : Prop :=
  ∀ (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedD n q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩

@[expose] def CensusBodyTriD4 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩

@[expose] def CensusBodyE6 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.E6 q, hv⟩

@[expose] def CensusBodyE7 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.E7 q, hv⟩

@[expose] def CensusBodyE8 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.E8 q, hv⟩

@[expose] def CensusBodyF4 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.F4 q, hv⟩

@[expose] def CensusBodyG2 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.G2 q, hv⟩

@[expose] def CensusBodyTwistedE6 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid), q.p = 2 →
    CensusBody ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩

@[expose] def CensusBodyReeF4 : Prop :=
  ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    CensusBody ⟨TauCeti.LieTypeIndex.reeF4 m, hv⟩

@[expose] def CensusBodyTits : Prop :=
  ∀ hv : TauCeti.LieTypeIndex.tits.Valid, CensusBody ⟨TauCeti.LieTypeIndex.tits, hv⟩

theorem censusBodyOn_C (n : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.C n q).Valid)
    (hchar : (TauCeti.LieTypeIndex.C n q).characteristic = 2) :
    CensusBody ⟨TauCeti.LieTypeIndex.C n q, hv⟩ := by
  exfalso
  have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
  have hp : q.p = 2 := by simpa using hchar
  exact hrange.2 hp

theorem censusBodyOn_reeG2 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid)
    (hchar : (TauCeti.LieTypeIndex.reeG2 m).characteristic = 2) :
    CensusBody ⟨TauCeti.LieTypeIndex.reeG2 m, hv⟩ := by
  exfalso
  have h3 : (3 : ℕ) = 2 := by simpa using hchar
  omega

theorem t1428U6Census_of_bodies
    (hTwA : CensusBodyTwistedA) (hB : CensusBodyB) (hD : CensusBodyD)
    (hTwD : CensusBodyTwistedD) (hTri : CensusBodyTriD4) (hE6 : CensusBodyE6)
    (hE7 : CensusBodyE7) (hE8 : CensusBodyE8) (hF4 : CensusBodyF4) (hG2 : CensusBodyG2)
    (hTwE6 : CensusBodyTwistedE6) (hReeF4 : CensusBodyReeF4) (hTits : CensusBodyTits) :
    T1428U6Census := by
  rw [t1428U6Census_iff]
  rintro ⟨d, hv⟩ hchar
  cases d with
  | A n q => exact census_linear ⟨TauCeti.LieTypeIndex.A n q, hv⟩ rfl hchar
  | twistedA n q => exact hTwA n q hv (by simpa using hchar)
  | B n q => exact hB n q hv (by simpa using hchar)
  | C n q => exact censusBodyOn_C n q hv hchar
  | D n q => exact hD n q hv (by simpa using hchar)
  | twistedD n q => exact hTwD n q hv (by simpa using hchar)
  | E6 q => exact hE6 q hv (by simpa using hchar)
  | E7 q => exact hE7 q hv (by simpa using hchar)
  | E8 q => exact hE8 q hv (by simpa using hchar)
  | F4 q => exact hF4 q hv (by simpa using hchar)
  | G2 q => exact hG2 q hv (by simpa using hchar)
  | twistedE6 q => exact hTwE6 q hv (by simpa using hchar)
  | trialityD4 q => exact hTri q hv (by simpa using hchar)
  | suzuki m => exact suzuki_census_body m hv
  | reeG2 m => exact censusBodyOn_reeG2 m hv hchar
  | reeF4 m => exact hReeF4 m hv
  | tits => exact hTits hv

end CFSG.LocalAnalysis.GLTheoremA.T1428

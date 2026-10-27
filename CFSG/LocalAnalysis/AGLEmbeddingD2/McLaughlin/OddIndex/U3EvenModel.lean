module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3EvenSE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Models TauCeti
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem statedClassicalModel_of_lieModel' {G : Type} [Group G]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hn : n ≠ 0) (h : LieModel G t n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G t n p f :=
  CFSG.Models.LieModel.statedClassicalModel_of_ne_zero hn h

theorem overgroupL32Odd_of_twistedA_even (K : Type) [Group K] [Finite K]
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower) (hq2 : q.p = 2)
    (hq3 : q.card % 3 = 1) (hd : d.1 = .twistedA 2 q)
    (e : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) : OvergroupL32Odd K := by
  intro _ _ _ _ A W Y _ _ _ _ hY
  exfalso
  obtain ⟨e⟩ := e
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 2 q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 2 q
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 q.p q.exponent := by
    have := statedClassicalModel_of_lieModel' (by omega) (lieModel_twistedA 2 q hv e)
    rwa [hc, hf] at this
  rw [hq2] at hmodel
  have hcard : q.card = 2 ^ q.exponent := by
    have := TauCeti.PrimePower.card_def q
    rwa [hq2] at this
  have hm : 2 ≤ q.exponent := by
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [h1, pow_one] at hcard
    omega
  obtain ⟨e'⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hm hmodel
  have : Finite (PSU3 2 q.exponent) := Finite.of_equiv K e'.toEquiv
  have hB := (bender_psu3_borel_full q.exponent hm).map_mulEquiv e'.symm
  exact not_isLThreeTwo_of_stronglyEmbedded (fun Q => (hB Q).1) Y hY

theorem overgroupL32U3_of_odd
    (hodd : ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex)
      (q : TauCeti.PrimePower), q.p ≠ 2 → q.card % 3 = 1 → d.1 = .twistedA 2 q →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → OvergroupL32Odd K) :
    OvergroupL32U3 := by
  intro K _ _ d q h3 hd e
  by_cases hq : q.p = 2
  · exact overgroupL32Odd_of_twistedA_even K d q hq h3 hd e
  · exact hodd K d q hq h3 hd e

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

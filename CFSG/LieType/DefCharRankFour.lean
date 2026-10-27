module

public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.LieType

open TauCeti CFSG.SectionRank CFSG.Assembly.LowTwoRank

@[expose] def IsExcRankFourIndex (d : LieTypeIndex) : Prop :=
  (∃ q, d = .E6 q) ∨ (∃ q, d = .E7 q) ∨ (∃ q, d = .E8 q) ∨ (∃ q, d = .F4 q) ∨
    (∃ q, d = .twistedE6 q) ∨ (∃ q, d = .trialityD4 q) ∨
    (∃ q : PrimePower, d = .G2 q ∧ 2 ≤ q.exponent)

@[expose] def DefCharRankFourExc : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : ValidLieTypeIndex),
    Nonempty (K ≃* (CFSGIndex.lie d).Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    p = d.1.characteristic → IsExcRankFourIndex d.1 → 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)

theorem defCharRankFourExc :
    DefCharRankFourExc := by
  intro K _ _ d ⟨e⟩ p hp hp2 hpc hexc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hv⟩ := d
  have hB := CFSG.TauCetiBridge.chevalleyBridges
  rcases hexc with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ |
    ⟨q, rfl, hq2⟩
  · obtain rfl : p = q.p := by simpa using hpc
    have h := four_mul_le_pRank_of_untwistedModel (τ := .E6) (by simp) (p := q.p)
      (f := q.exponent) (CFSG.TauCetiBridge.untwistedModel_of_bridge hB.e6 q hv hp2 e)
    have := q.exponent_pos
    omega
  · obtain rfl : p = q.p := by simpa using hpc
    have h := four_mul_le_pRank_of_untwistedModel (τ := .E7) (by simp) (p := q.p)
      (f := q.exponent) (CFSG.TauCetiBridge.untwistedModel_of_bridge hB.e7 q hv hp2 e)
    have := q.exponent_pos
    omega
  · obtain rfl : p = q.p := by simpa using hpc
    have h := four_mul_le_pRank_of_untwistedModel (τ := .E8) (by simp) (p := q.p)
      (f := q.exponent) (CFSG.TauCetiBridge.untwistedModel_of_bridge hB.e8 q hv hp2 e)
    have := q.exponent_pos
    omega
  · obtain rfl : p = q.p := by simpa using hpc
    have h := four_mul_le_pRank_of_untwistedModel (τ := .F4) (by simp) (p := q.p)
      (f := q.exponent) (CFSG.TauCetiBridge.untwistedModel_of_bridge hB.f4 q hv hp2 e)
    have := q.exponent_pos
    omega
  · obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_of_twistedE6Model (p := q.p) (f := q.exponent) q.exponent_pos
      (CFSG.TauCetiBridge.twistedModel_of_bridge hB.twistedE6 q hv hp2 (by decide) e)
  · obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_of_trialityD4Model (p := q.p) (f := q.exponent) q.exponent_pos
      (CFSG.TauCetiBridge.twistedModel_of_bridge hB.trialityD4 q hv hp2 (by decide) e)
  · obtain rfl : p = q.p := by simpa using hpc
    have h := three_mul_le_pRank_of_G2Model (p := q.p) (f := q.exponent)
      (CFSG.TauCetiBridge.untwistedModel_of_bridge hB.g2 q hv hp2 e)
    omega

end CFSG.LieType

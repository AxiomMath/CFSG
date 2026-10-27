module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescRankOne

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section Bridge

variable {S : Type} [Group S]

theorem innAutDerived_eq_inner (hab : commutator (MulAut S) ≤ inner S) : innAutDerived S = inner S :=
  le_antisymm (sup_le le_rfl hab) (CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived S)

theorem outPRankLE1_of_N1 (hN1 : KD264OutCyc) (d : TauCeti.ValidLieTypeIndex) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hchar : p ≠ d.1.characteristic)
    (hab : commutator (MulAut (TauCeti.CFSGIndex.lie d).Group) ≤ inner (TauCeti.CFSGIndex.lie d).Group) :
    OutPRankLE1 p (TauCeti.CFSGIndex.lie d).Group := by
  intro A hA
  have h := hN1 d p hp hp2 hchar A hA
  rwa [innAutDerived_eq_inner hab] at h

theorem outerFixLayer_of_N2 (hN2 : KD264OuterIdx) (d : TauCeti.ValidLieTypeIndex) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hchar : p ≠ d.1.characteristic)
    (h3 : ¬ (p = 3 ∧
      ((∃ q : TauCeti.PrimePower, (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
        (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q))))
    (h5 : ¬ (p = 5 ∧ d.1 = .suzuki 2))
    (hab : commutator (MulAut (TauCeti.CFSGIndex.lie d).Group) ≤ inner (TauCeti.CFSGIndex.lie d).Group)
    [Finite (TauCeti.CFSGIndex.lie d).Group] :
    OuterFixLayer p (TauCeti.CFSGIndex.lie d).Group := by
  intro α hα hout s hs _ _
  have hdvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := hs ▸ orderOf_dvd_natCard s
  have hαp : α ^ p = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have hnd : α ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group := by
    rw [innAutDerived_eq_inner hab]
    exact hout
  obtain ⟨J, hJ, hJp, -⟩ := hN2 d p hp hp2 hchar hdvd h3 h5 α hαp hnd
  intro hbot
  have hle : J ≤ GLAPLayer p (fixSubgroup α) := le_sSup hJ
  rw [hbot] at hle
  have hJ1 : Nat.card J = 1 := by
    rw [Subgroup.card_eq_one]
    exact le_bot_iff.1 hle
  rw [hJ1] at hJp
  exact hp.one_lt.ne' (Nat.dvd_one.1 hJp)

end Bridge

section KLevel

variable {Y : Type} [Group Y] [Finite Y]

theorem kConcl_of_N1_N2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN1 : KD264OutCyc) (hN2 : KD264OuterIdx)
    {K B : Subgroup Y} (h : KHyp p K B) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hchar : p ≠ d.1.characteristic)
    (h3 : ¬ (p = 3 ∧
      ((∃ q : TauCeti.PrimePower, (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
        (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q))))
    (h5 : ¬ (p = 5 ∧ d.1 = .suzuki 2))
    (hab : commutator (MulAut (TauCeti.CFSGIndex.lie d).Group) ≤ inner (TauCeti.CFSGIndex.lie d).Group)
    (h2 : TwoLocalRankLE1 p (TauCeti.CFSGIndex.lie d).Group)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3) : KConcl p K B :=
  kConcl_of_rankOne hp hp2 h e (outPRankLE1_of_N1 hN1 d hp hp2 hchar hab) h2
    (outerFixLayer_of_N2 hN2 d hp hp2 hchar h3 h5 hab) hc

end KLevel

end CFSG.LocalAnalysis.GLTheoremA.HDesc

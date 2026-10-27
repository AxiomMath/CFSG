module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyPrimeSquare
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.Assembly.LowTwoRank TauCeti

theorem isSQTKOddLieIndex_cases {d : LieTypeIndex} (hd : IsSQTKOddLieIndex d) :
    (∃ q : PrimePower, d = .A 1 q ∧ ((q.exponent = 1 ∧ 11 ≤ q.p) ∨ (q.exponent = 2 ∧ 5 ≤ q.p))) ∨
      (∃ q : PrimePower, d = .A 2 q ∧ q.exponent = 1 ∧ q.p ≠ 2) ∨
      (∃ q : PrimePower, d = .twistedA 2 q ∧ q.exponent = 1 ∧ 5 ≤ q.p) := by
  unfold IsSQTKOddLieIndex at hd
  split at hd
  · exact Or.inl ⟨_, rfl, hd⟩
  · exact Or.inr (Or.inl ⟨_, rfl, hd⟩)
  · exact Or.inr (Or.inr ⟨_, rfl, hd⟩)
  · exact hd.elim

theorem statedClassicalModel_PSL_of_lieA {X : Type} [Group X] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) (e : X ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group) :
    StatedClassicalModel X .PSL (r + 1) q.p q.exponent :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e

theorem noIrrFFOffender_lie_odd
    (d : TauCeti.ValidLieTypeIndex) (hd : IsSQTKOddLieIndex d.1) :
    NoIrrFFOffender (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Nontrivial W := hirr.1
  have hperf : Group.IsPerfect ↥L := hq.1
  rcases isSQTKOddLieIndex_cases hd with ⟨q, rfl, hq1 | hq2⟩ | ⟨q, rfl, hq1, hp2⟩ |
    ⟨q, rfl, hq1, hp5⟩
  · have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hmod := statedClassicalModel_PSL_of_lieA hv e
    rw [hq1.1] at hmod
    obtain ⟨α⟩ := Family.equiv_projectiveSL_of_model hmod
    exact (Family.primeLinearTwoCover hq1.2 hW hperf hirr.2 α).2 E hEN hE hel
  · have hmod := statedClassicalModel_PSL_of_lieA hv e
    rw [hq2.1] at hmod
    exact Family.primeSquareExclusion q.p q.prime_p hq2.2 W hW L hperf hirr hmod E hEN hE hel
  · have hmod := statedClassicalModel_PSL_of_lieA hv e
    rw [hq1] at hmod
    exact Family.primeLinearThreeExclusion q.p q.prime_p hp2 W hW L hperf hirr hmod E hEN hE hel
  · have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hq1] at hmod
    exact Family.primeUnitaryThreeExclusion q.p q.prime_p hp5 W hW L hperf hirr hmod E hEN hE hel

end CFSG.HardMathSupport.Cooperstein.Coordinator

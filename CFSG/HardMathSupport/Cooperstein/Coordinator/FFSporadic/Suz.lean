module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.SuzEngine
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.SuzFacts
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.SuzRow

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SuzOddCore
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

theorem eq_one_or_three_of_odd_dvd_six' {n : ℕ} (hodd : Odd n) (hn : n ∣ 6) : n = 1 ∨ n = 3 := by
  have : n ∈ Nat.divisors 6 := by simp [hn]
  have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [h6] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd hodd (by decide)
  · exact Or.inr rfl
  · exact absurd hodd (by decide)

theorem sporadicExclusion_Suz :
    QuasithinUnique.Setup.X1.SporadicExclusion .Suz := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hmult := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rw [nativeRow_Suz] at hmult
  have hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3 :=
    eq_one_or_three_of_odd_dvd_six' (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.odd_card_center_of_isIrrOn hW hirr)
      (hmult.trans (by decide))
  have e' : NativeSporadic.Carrier .Suz ≃* suzM := suzEquivM
  obtain ⟨A, g, hAc, hAp, hAcard, hgA, hg11, hgnc⟩ := suzAG_facts
  exact exclusion_of_three_generation hW hq hirr (e.trans e') hE hEne hEel hZ suzAut_gen
    suzAut_rank hAc hAp hAcard hgA hg11 hgnc

theorem noIrrFFOffender_Suz :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Suz).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel hquad
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  exact sporadicExclusion_Suz W hW L E hq hirr ⟨e.trans f.symm⟩ hE hEne hEel hquad

theorem gf2NoFFSporadicFor_Suz :
    GF2NoFFSporadicFor .Suz :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_Suz

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

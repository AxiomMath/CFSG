module

public import Certificates.Certificate16952
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMPairs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiLocal

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

namespace Fi24Seven

open CFSG.Blueprint CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair

theorem fi24Seven_parts : SevenFacts := Certificates.certificate16952

theorem oPrimeCoreTrivialAt_Fi24J_seven : OPrimeCoreTrivialAt 7 CFSG.Sporadic.Fi24.J := by
  have hF := fi24Seven_parts
  intro s hs
  obtain ⟨t, ht⟩ := hF.conj s hs
  have hcore : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({t * s * t⁻¹} : Set CFSG.Sporadic.Fi24.J)) = ⊥ := by
    rcases ht with ht | ht
    · rw [ht]
      exact hF.core_y
    · rw [ht]
      exact hF.core_c
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hu' := conj_mem_gLAPPrimeCoreOf_centralizer t s u hu
  rw [hcore, Subgroup.mem_bot] at hu'
  calc u = t⁻¹ * (t * u * t⁻¹) * t := by group
    _ = 1 := by rw [hu']; group

end Fi24Seven

open CFSG.Blueprint in
theorem sporadicOPrimeHolds_Fi24_seven :
    SporadicOPrimeHolds .Fi24Prime 7 :=
  sporadicOPrimeHolds_of_carrier
    (@OPrimeCoreTrivialAt.of_mulEquiv 7 (NativeSporadic.Carrier .Fi24Prime) _ CFSG.Sporadic.Fi24.J
      (Subgroup.toGroup CFSG.Sporadic.Fi24.J) CFSG.Sporadic.Fi24.fi24EquivJ
      Fi24Seven.oPrimeCoreTrivialAt_Fi24J_seven)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance

module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5CoverExcTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5CoverField
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5CoverExcRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.ComponentClassification.PerfectAutomorphisms CFSG.LieType.SemisimpleCentralizers.HeldLang

section Certificates

theorem kd264I5CoverLiftExc_of_certificates : KD264I5CoverLiftExc := by
  intro e k hk hexc K _ _ hK eK β hβ3 hout
  obtain ⟨d, hd⟩ := e
  obtain ⟨eK'⟩ := eK
  cases d with
  | E6 q => exact kd264I5CoverLift_E6 q hd hK eK' β hβ3
  | twistedE6 q =>
    by_cases hq : 3 ≤ q.card
    · exact kd264I5CoverLift_twistedE6 q hd hq hK eK' β hβ3
    · exfalso
      have h2 : 2 ≤ q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact (q.prime_p.two_le).trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
      have hγ3 : onCenterQuotient β ^ 3 = 1 := by
        have := congrArg (centerQuotientHom K) hβ3
        rwa [map_pow, map_one] at this
      exact false_of_outer_three_twistedE6_two q hd (by omega) eK' (onCenterQuotient β) hγ3 hout
  | _ => exact absurd hexc (by rintro ⟨q', h | h⟩ <;> simp at h)

theorem kd264I5Field_of_certificates' (hU : KD264I5UniversalExc) : KD264I5Field :=
  kd264I5Field_of_certificates kd264I5CoverLiftExc_of_certificates hU

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

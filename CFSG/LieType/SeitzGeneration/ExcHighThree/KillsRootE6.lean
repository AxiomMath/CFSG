module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.HardMathSupport.Malle.SeitzCube.LandingE6

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley


theorem langPlaneKillsRoot_E6 : LangPlaneKillsRoot Tag.E6 := by
  intro K _ _ A D α hα hk
  obtain ⟨uL, huLad, huL1, huLp, huLF, huLc⟩ :=
    kill_core (τ := Tag.E6) (Or.inr (Or.inl rfl)) K A D α hα hk
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hcop : ringChar K ≠ 3 → Nat.Coprime 3 (orderOf uL) := by
    intro h3
    rw [orderOf_eq_prime huLp huL1]
    exact (Nat.coprime_primes Nat.prime_three Fact.out).2 (Ne.symm h3)
  obtain ⟨u', hu'mem, hu'eq⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E6 D.Fr D.hFr
      huLad huLF hcop)
  exact finish_of_descent K A D.c u' hu'mem uL hu'eq huL1 huLp huLc

end CFSG.LieType.SeitzGeneration.ExcHighThree

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Native
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42DichProof
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyPrimeSquare
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeWrap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Tight

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup

open Dichotomy in
theorem asB42DichotomyNat_of_exclusions
    (hJ2 : X1.SporadicExclusion .J2) (hJ4 : X1.SporadicExclusion .J4)
    (hHS : X1.SporadicExclusion .HS) (hRu : X1.SporadicExclusion .Ru)
    (hA7 : ThreeA7Exclusion) : AsB42DichotomyNat := by
  intro W _ _ hW L hq hirr hlist E hEN hE hel hoff
  have hirrOn : X1.IsIrrOn L := isIrrOn_of_isIrrSec hirr
  have : Nontrivial W := hirrOn.1
  obtain ⟨A, hAE, hA0, hAel, hAq, hAoff⟩ := exists_quadratic_offender hW hE hel hoff
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) := hAE.trans hEN
  have hcon : ¬ Nat.card A * Nat.card (fixV A) < Nat.card W := not_lt.2 hAoff
  have hA7clause : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) →
      Subgroup.center ↥L = ⊥ := by
    intro h7
    by_contra hc
    exact hcon (hA7 W hW L A hq hirrOn h7 hc hAN hA0 hAel hAq)
  refine ⟨?_, hA7clause⟩
  have hbig : ∀ q : ℕ, q ≠ 2 → q ≠ 3 → q.Prime → 5 ≤ q := by
    intro q hq2 hq3 hqp
    have h2 := hqp.two_le
    have h4 : q ≠ 4 := by
      rintro rfl
      norm_num at hqp
    omega
  have hperf : Group.IsPerfect ↥L := hq.1
  rcases hlist with halt | ⟨p, hp, hp2, hcl⟩ | hchar2 | hSL | ⟨s, hs, ⟨e⟩⟩
  · exact Or.inl halt
  · rcases hcl with ⟨f, hf12, hmod⟩ | hmod | hmod
    · rcases hf12 with rfl | rfl
      · have : Fact p.Prime := ⟨hp⟩
        by_cases hp11 : 11 ≤ p
        · exfalso
          obtain ⟨α⟩ := Family.equiv_projectiveSL_of_model hmod
          exact hcon ((Family.primeLinearTwoCover hp11 hW hperf hirrOn.2 α).2 A hAN hA0 hAel)
        · have hp3 : 3 ≤ p := by have := hp.two_le; omega
          interval_cases p
          · exact absurd rfl hmod.1.2.2.2.2
          · norm_num at hp
          · exact Or.inr (Or.inl hmod)
          · norm_num at hp
          · exact Or.inr (Or.inr (Or.inl hmod))
          all_goals norm_num at hp
      · by_cases hp3 : p = 3
        · subst hp3
          exact Or.inr (Or.inr (Or.inr (Or.inl hmod)))
        · exfalso
          exact hcon (Family.primeSquareExclusion p hp (hbig p hp2 hp3 hp) W hW L hperf hirrOn
            hmod A hAN hA0 hAel)
    · exfalso
      exact hcon (Family.primeLinearThreeExclusion p hp hp2 W hW L hperf hirrOn hmod A hAN hA0
        hAel)
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmod))))
      · exfalso
        exact hcon (Family.primeUnitaryThreeExclusion p hp (hbig p hp2 hp3 hp) W hW L hperf
          hirrOn hmod A hAN hA0 hAel)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hchar2)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hSL)))))
  · exfalso
    have hex : X1.SporadicExclusion s := by
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact X1.sporadicExclusion_M11
      · exact X1.sporadicExclusion_M12
      · exact X1.sporadicExclusion_M22_of X1.m22TightProp
      · exact X1.sporadicExclusion_M23
      · exact X1.sporadicExclusion_M24_of X1.m24TightProp
      · exact X1.sporadicExclusion_of_J1 X1.j1ExclusionProp
      · exact hJ2
      · exact hJ4
      · exact hHS
      · exact X1.sporadicExclusion_He
      · exact hRu
    exact hcon (hex W hW L A hq hirrOn ⟨e⟩ hAN hA0 hAel hAq)

end CFSG.QuasithinUnique.Bridge

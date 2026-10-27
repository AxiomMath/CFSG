module

public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeQuotientNormalizers

public section

namespace CFSG.GroupTheory

theorem normal_coprime_quotient_normalizer {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] (N : Subgroup G) [N.Normal] (hN : ¬ p ∣ Nat.card N) (P : Subgroup G)
    (hP : IsPGroup p P) :
    (Subgroup.normalizer (P : Set G)).map (QuotientGroup.mk' N) =
      Subgroup.normalizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
  CFSG.SignalizerFunctor.Helpers.coprime_quotient_normalizer_image p Fact.out N P
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN) hP

end CFSG.GroupTheory

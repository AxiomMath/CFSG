module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter OuterAutomorphisms

universe u v

theorem oddPrimePower_of_odd_card (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : IsOddPrimePower (Nat.card K) := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨p, _hpchar, f, hp, hcard⟩ := FiniteField.card' K
  have hcard' : Nat.card K = p ^ (f : ℕ) := by
    rwa [Nat.card_eq_fintype_card]
  have hpodd : Odd p := by
    apply (Nat.odd_pow_iff f.ne_zero).mp
    rwa [← hcard']
  exact ⟨p, f, hp, hpodd, f.pos, hcard'⟩

theorem odd_semilinearAction_surjective
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard) := by
  rcases hK with ⟨p, f, hp, hpodd, hf, hKcard⟩
  let : Fact p.Prime := ⟨hp⟩
  exact pGammaL2ToMulAutPSL2_surjective K hKcard
    ⟨p, f, hp, hpodd, hf, hKcard⟩ hcard

@[expose] def odd_semilinearToOuter
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    PGammaL2 K →* Outer (PSL2 K) :=
  (QuotientGroup.mk' (inner (PSL2 K))).comp
    (pGammaL2ToMulAutPSL2 K hK hcard)

theorem odd_semilinearToOuter_surjective
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    Function.Surjective (odd_semilinearToOuter K hK hcard) :=
  (QuotientGroup.mk'_surjective (inner (PSL2 K))).comp
    (odd_semilinearAction_surjective K hK hcard)

theorem odd_semilinearToOuter_ker
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    (odd_semilinearToOuter K hK hcard).ker = pGammaL2PSLRange K := by
  ext g
  change QuotientGroup.mk' (inner (PSL2 K))
    (pGammaL2ToMulAutPSL2 K hK hcard g) = 1 ↔ _
  change (QuotientGroup.mk (pGammaL2ToMulAutPSL2 K hK hcard g) :
    Outer (PSL2 K)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy⟩
    apply (mem_pGammaL2PSLRange_iff K g).mpr
    refine ⟨y, ?_⟩
    apply pGammaL2ToMulAutPSL2_injective K hK hcard
    rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]
    exact hy
  · intro hg
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K g).mp hg
    refine ⟨y, ?_⟩
    rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]

@[expose] def odd_outerEquivSemilinearQuotient
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    SemilinearQuotient K ≃* Outer (PSL2 K) :=
  (QuotientGroup.quotientMulEquivOfEq (odd_semilinearToOuter_ker K hK hcard).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (odd_semilinearToOuter K hK hcard)
      (odd_semilinearToOuter_surjective K hK hcard))

theorem odd_outer_secondDerived_eq_bot
    (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 < Nat.card K) :
    derivedSeries (Outer (PSL2 K)) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective
    (odd_outerEquivSemilinearQuotient K (oddPrimePower_of_odd_card K hodd) hcard).toMonoidHom
    (odd_outerEquivSemilinearQuotient K (oddPrimePower_of_odd_card K hodd) hcard).surjective
    (semilinearQuotient_secondDerived_eq_bot K)

theorem odd_outer_solvable
    (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 < Nat.card K) :
    Group.IsSolvable (Outer (PSL2 K)) :=
  ⟨⟨2, odd_outer_secondDerived_eq_bot K hodd hcard⟩⟩

theorem odd_outer_secondDerived_eq_bot_of_equiv
    {G : Type v} [Group G]
    (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : G ≃* PSL2 K) : derivedSeries (Outer G) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (equivalence e).symm.toMonoidHom
    (equivalence e).symm.surjective (odd_outer_secondDerived_eq_bot K hodd hcard)

theorem odd_outer_solvable_of_equiv
    {G : Type v} [Group G]
    (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : G ≃* PSL2 K) : Group.IsSolvable (Outer G) :=
  ⟨⟨2, odd_outer_secondDerived_eq_bot_of_equiv K hodd hcard e⟩⟩

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo

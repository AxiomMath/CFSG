module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.SmallOddCore.HSWordBound
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallBasic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.ComponentClassification.OuterAutomorphisms

theorem card_mulAut_le_of_isSporadic_m22
    {N : Type} [Group N] [Finite N]
    (h : IsSporadic N .M22) : Nat.card (MulAut N) ≤ 2 * Nat.card N := by
  obtain ⟨e⟩ := h
  exact card_mulAut_le_of_mulEquiv e CFSG.Sporadic.Schreier.m22_mulAut_card

theorem card_mulAut_le_of_isSporadic_m23
    {N : Type} [Group N] [Finite N]
    (h : IsSporadic N .M23) : Nat.card (MulAut N) ≤ 1 * Nat.card N := by
  obtain ⟨e⟩ := h
  exact card_mulAut_le_of_mulEquiv (k := 1) e (by
    rw [one_mul]
    exact CFSG.Sporadic.Schreier.m23_mulAut_card)

theorem card_mulAut_le_of_isSporadic_m24
    {N : Type} [Group N] [Finite N]
    (h : IsSporadic N .M24) : Nat.card (MulAut N) ≤ 1 * Nat.card N := by
  obtain ⟨e⟩ := h
  exact card_mulAut_le_of_mulEquiv (k := 1) e (by
    rw [one_mul]
    exact CFSG.Sporadic.Schreier.m24_mulAut_card)

theorem card_mulAut_le_of_isSporadic_hs
    {N : Type} [Group N] [Finite N]
    (h : IsSporadic N .HS) : Nat.card (MulAut N) ≤ 2 * Nat.card N := by
  obtain ⟨e⟩ := h
  have e' : N ≃* CFSG.Sporadic.Schreier.hsP := e.trans CFSG.Sporadic.Schreier.hsPermEquiv
  refine card_mulAut_le_of_mulEquiv e' ?_
  have h := CFSG.Sporadic.SmallOddCore.hs_card_mulAut_le
  rw [CFSG.Sporadic.Schreier.card_hsP]
  omega

theorem card_mulAut_le_of_isSporadic_ru
    {N : Type} [Group N] [Finite N] (h : IsSporadic N .Ru) :
    Nat.card (MulAut N) ≤ 1 * Nat.card N := by
  obtain ⟨e⟩ := h
  have e' : N ≃* CFSG.Sporadic.RuSchreier.ruP := e.trans CFSG.Sporadic.RuSchreier.ruEquivP
  apply card_mulAut_le_of_card_outer_le (k := 1)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact le_of_eq CFSG.Sporadic.RuSchreier.card_outer_ruP

theorem card_mulAut_le_of_isSporadic_j2
    {N : Type} [Group N] [Finite N] (h : IsSporadic N .J2) :
    Nat.card (MulAut N) ≤ 2 * Nat.card N := by
  obtain ⟨e⟩ := h
  apply card_mulAut_le_of_card_outer_le (k := 2)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact CFSG.Sporadic.Schreier.AT_J2_Schreier.1

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

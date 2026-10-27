module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.HiiDomination
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.HiiHyperoval
public import CFSG.Sporadic.Fi22.LH.Facts
public import CFSG.Fischer.Polar.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Sporadic.Fi22

theorem hii_of_localPoints
    {X : Type} [Group X] {E : Set X} (hinv : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (hD2 : ∀ x ∈ E, x * x = 1)
    (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) E f)) :
    ∀ d ∈ E, ∀ b ∈ LocalClass E d, ∀ a ∈ E, a * d ≠ d * a → a ∈ LocalClass E b →
      ∀ c ∈ LocalClass E d, ∃ f ∈ LocalClass E a ∩ LocalClass E d, f * c = c * f := by
  intro d hd b hb a ha hat hab c hc
  obtain ⟨L⟩ := hloc d hd
  have hfar : a ∈ farSet E d :=
    ⟨ha, hat, b, hb, hb.1, fun e => hab.2.1 e.symm, hab.2.2.symm⟩
  have hLH := isLocallyHyperoval_muImg_of_conj polarFacts hyperovalFacts.linesByPerp f22_J
    connected_D hinv hD2 hloc hd hfar L
  obtain ⟨i, hi⟩ := (fi22Facts polarFacts hyperovalFacts).exists_mem_lhOrbit _ hLH
    ((L.muImg_nonempty_iff a).2 hfar.2.2)
  obtain ⟨x, hx, hxc⟩ := exists_commute_of_mem_lhOrbit hi (L.χ ⟨c, hc⟩)
  obtain ⟨s, hs, rfl⟩ := hx
  exact ⟨s, ⟨hs, s.2⟩, (L.comm s ⟨c, hc⟩).2 hxc.symm⟩

end CFSG.EvenSporadicStandard.TwoFi22

module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def HNCentralizerFacts : Prop :=
  ∃ z₀ : Carrier .HN, orderOf z₀ = 2 ∧
    ∃ E : Subgroup (centralizer ({z₀} : Set (Carrier .HN))),
      IsHSCover (centralizer ({z₀} : Set (Carrier .HN))) E ∧ E.index = 2 ∧
      ∀ g : centralizer ({z₀} : Set (Carrier .HN)), g ∉ E → g ^ 2 ∈ centralizer (E : Set _) →
        g ^ 2 = 1

theorem isSimpleGroup_of_mulEquiv {K C : Type} [Group K] [Group C] (e : K ≃* C)
    (hs : IsSimpleGroup C) : IsSimpleGroup K :=
  (MulEquiv.isSimpleGroup_congr e).2 hs

theorem exists_noncomm_of_mulEquiv {K C : Type} [Group K] [Group C] (e : K ≃* C)
    (h : ∃ a b : C, a * b ≠ b * a) : ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩

theorem isComponent_of_isHSCover
    {H : Type} [Group H] {E : Subgroup H} (h : IsHSCover H E) : CFSG.IsComponent E := by
  obtain ⟨e⟩ := h.quotient
  exact ⟨⟨h.perfect, isSimpleGroup_of_mulEquiv e CFSG.Sporadic.HS.isSimpleGroup_HS,
    exists_noncomm_of_mulEquiv e CFSG.Sporadic.SmallOddCore.hs_not_comm⟩,
    h.normal.isSubnormal⟩

end CFSG.EvenSporadicStandard.TwoHS

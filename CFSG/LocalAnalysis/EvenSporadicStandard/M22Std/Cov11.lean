module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov7
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov10

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem m22TwistedSylowData :
    M22TwistedSylowData := by
  intro G _ _ L t ht hZ hCL hCt hrel hperf hq hno
  have hc : CoverSetting L t := ⟨ht, hZ, hCL, hCt, by rw [hrel]⟩
  have hcov := hc.isM22Cover hq
  have : Group.IsPerfect L := Group.isPerfect_def.2 hperf
  obtain ⟨F⟩ := hcov.nonempty_twFacts
  have hLH : L ≤ centralizer ({t} : Set G) := hc.le_centralizer
  let ι : L →* centralizer ({t} : Set G) := Subgroup.inclusion hLH
  have hι : Function.Injective ι := Subgroup.inclusion_injective hLH
  have hmemL : ∀ y : centralizer ({t} : Set G), y ∈ ι.range ↔ (y : G) ∈ L := by
    intro y
    constructor
    · rintro ⟨l, rfl⟩
      exact l.2
    · intro hy
      exact ⟨⟨y, hy⟩, Subtype.ext rfl⟩
  have hn : ι.range.Normal := by
    refine ⟨fun r hr h => ?_⟩
    rw [hmemL] at hr ⊢
    have hhN : (h : G) ∈ normalizer (L : Set G) := hc.centralizer_t ▸ h.2
    have := (Subgroup.mem_normalizer_iff.1 hhN (r : G)).1 hr
    simpa using this
  have htc : ∀ h : centralizer ({t} : Set G), ι ⟨t, hc.t_mem⟩ * h = h * ι ⟨t, hc.t_mem⟩ := by
    intro h
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.1 h.2).symm
  have hno' : ∀ y : centralizer ({t} : Set G), y ∉ ι.range → orderOf y ≠ 2 := by
    intro y hy
    rw [hmemL] at hy
    rw [← Subgroup.orderOf_coe]
    exact hno y y.2 hy
  obtain ⟨T, hR1, hR2⟩ := twisted_sylow ι hι hn htc hcov F hno'
  refine ⟨T, fun ψ x hx => hR1 ψ x (Subtype.ext hx), fun u hu hu2 => ?_⟩
  have hu' : (⟨u, hLH hu⟩ : centralizer ({t} : Set G)) ∈ ι.range := (hmemL _).2 hu
  have hord : orderOf (⟨u, hLH hu⟩ : centralizer ({t} : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hu2
  obtain ⟨k, hk, z, hz, hzk⟩ := hR2 _ hu' hord
  refine ⟨(k : G), (hmemL k).1 hk, z, hz, ?_⟩
  have := congrArg Subtype.val hzk
  simpa using this

theorem false_of_center_ne_bot_of_split
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h25 : Finkelstein77.Asc76Lemma25) (hSplit : HaradaSolomon08M22Split) (h : StdHyp G L)
    (hq : IsSporadic (L ⧸ center L) .M22) (hZ : center L ≠ ⊥) : False :=
  false_of_center_ne_bot_of_cases h25 hSplit m22TwistedSylowData h hq hZ

end CFSG.EvenSporadicStandard.M22Std

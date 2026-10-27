module

public import CFSG.ClassicalInvolution.Q3.Sec13L711Gen
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75Conj

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace Q8Omega

variable (hΩ : Q8Omega Ω)
include hΩ

theorem mem_DSet_iff {W R : Subgroup G} :
    R ∈ DSet Ω W ↔ R ∈ Ω ∧ R ≤ Subgroup.normalizer (W : Set G) :=
  and_congr_left' hΩ.mem_RSet_iff

theorem conjSub_mem_DSet {W R : Subgroup G} (hR : R ∈ DSet Ω W) (g : G) :
    conjSub g R ∈ DSet Ω (conjSub g W) := by
  rw [hΩ.mem_DSet_iff] at hR ⊢
  refine ⟨hΩ.hyp.conjInvariant g R hR.1, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  rw [Thompson.conjSub_normalizer, mem_conjSub_iff]
  exact hR.2 hx

theorem exists_mem_DSet_of_mem_eta {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) {U : Subgroup G}
    (hU : U ∈ η) : ∃ J ∈ DSet Ω (⨆ V ∈ η, V), U ≤ J := by
  obtain ⟨J, hJ, hUJ⟩ := Sec6Gen.exists_member_of_mem_USet hΩ.hyp (hΩ.mem_USet_of_mem_eta hη hU)
  exact ⟨J, hΩ.mem_DSet_iff.mpr ⟨hJ, (hΩ.isSys_of_eta hη).le_normalizer_span hΩ hJ hU hUJ⟩, hUJ⟩

end Q8Omega

end CFSG.ClassicalInvolution.Q3.Sec13

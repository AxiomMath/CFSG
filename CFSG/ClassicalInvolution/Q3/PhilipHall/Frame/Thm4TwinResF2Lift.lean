module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace Thm4Twin

namespace F2

variable {G : Type} [Group G] [Finite G]

@[expose] def ExitSec (W K : Subgroup G) (hKW : K ≤ W) (z : G) (hz : IsUniqueInvolution K z) :
    Prop :=
  TwinE4 ↥W ∨ ∃ S : Sylow 2 ↥(K.subgroupOf W),
    ¬ TightInO2 (⟨z, hKW hz.mem⟩ : W) ∧
      TightEx ↥W (K.subgroupOf W) S (⟨z, hKW hz.mem⟩ : W)

theorem exists_lift_or_exit {n : ℕ} (hT : Thm1RTwinLiftSetBelow n) (hB : TightBelow n)
    (hG : Nat.card G < n) (hOG : classicalInvolutionOddCore G = ⊥) {Δ : Set (Subgroup G)}
    (hΩ : HypOmegaGen Δ) (h2 : ∀ K ∈ Δ, IsPGroup 2 K)
    (hq8 : ∀ K ∈ Δ, Nonempty (↥K ≃* QuaternionGroup 2)) (hA : ∀ K ∈ Δ, AEmpty Δ K)
    (hno : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → ¬ TightInO2 z) {K : Subgroup G}
    (hK : K ∈ Δ) {z : G} (hz : IsUniqueInvolution K z) :
    (∃ L : Subgroup G, IsLiftOf K L z) ∨
      ∃ (W : Subgroup G) (hKW : K ≤ W), IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : G) K) = W ∧
        ExitSec W K hKW z hz := by
  obtain ⟨W, hKW, hWs, hWg⟩ := exists_section K
  have hO : classicalInvolutionOddCore ↥W = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hOG W hWs
  have hlt : Nat.card W < n := lt_of_le_of_lt (Subgroup.card_le_card_group W) hG
  set R : Subgroup ↥W := K.subgroupOf W with hR
  set t : ↥W := ⟨z, hKW hz.mem⟩ with ht
  have hR2 : IsPGroup 2 R := (h2 K hK).comap_subtype
  have hut : IsUniqueInvolution R t := isUniqueInvolution_subgroupOf hz hKW
  have hq8R : Nonempty (↥R ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hKW).trans (hq8 K hK).some⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  obtain ⟨hd, hSq⟩ := q8TwinDatum_of_isPGroup hR2 S hut hq8R
  have htc : tightCore R = R := tightCore_eq_self_of_isPGroup hR2
  have hΩR : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := by
    rw [htc]; exact hypOmegaGen_conjClass_section hΩ hK hKW
  have hAR : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [htc]; exact aEmpty_conjClass_section hΩ h2 hK (hA K hK) hKW
  have hconj : ∀ g : ↥W, (conjSub g R).map W.subtype = conjSub (g : G) K := by
    intro g
    have hle : conjSub (g : G) K ≤ W := by
      have := conjSub_mono (n := (g : G)) hKW
      rwa [conjSub_eq_self_of_mem g.2] at this
    rw [hR, conjSub_subgroupOf]
    exact Subgroup.map_subgroupOf_eq_of_le hle
  have hgenW : (⨆ g : ↥W, conjSub g R) = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [hconj]
    exact hWg
  have hgen : TightSelfGen R := by
    show (⨆ g : ↥W, conjSub g (tightCore R)) = ⊤
    rw [htc]; exact hgenW
  have hzK : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core hd
  have hlift : TightHasLift R t → ∃ L : Subgroup G, IsLiftOf K L z := by
    rintro ⟨L, hRL, hL⟩
    refine ⟨L.map W.subtype, hz, ?_, F2.isClassicalMember3_map_subtype hWs hL⟩
    have hKR : R.map W.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKW
    rw [← hKR]
    exact Subgroup.map_mono (htc ▸ hRL)
  have hnoO2 : ¬ TightInO2 t := fun h => hno K hK z hz (F2.tightInO2_of_subnormal hWs _ h)
  by_cases htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R
  · rcases hT ↥W hlt R S t hd hSq hgen hO hΩR hAR htw with h | h | h
    · exact absurd h hnoO2
    · exact Or.inr ⟨W, hKW, hWs, hWg, Or.inl h⟩
    · exact Or.inl (hlift (h.hasLift htw))
  · have hsing : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R} := by
      ext K'
      constructor
      · intro hK'
        by_contra hne
        exact htw ⟨K', hK', hne⟩
      · intro hK'
        rw [Set.mem_singleton_iff] at hK'
        subst hK'
        exact ⟨CoreAssembly.mem_conjClass_self _, t, hzK, hzK⟩
    have hnormal := (twinSet_eq_singleton_iff (Q3B.conjInvariant_conjClass _)
      (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) (CoreAssembly.mem_conjClass_self _) hzK).mp hsing
    rw [htc] at hnormal
    have hdt : TightDatum R S t := hd.toTightDatum hnormal
    rcases hB ↥W hlt R S t hdt ⟨hSq, hgen, hO⟩ with h | h
    · by_cases hin : TightInO2 t
      · exact absurd hin hnoO2
      · exact Or.inr ⟨W, hKW, hWs, hWg, Or.inr ⟨S, hin, h⟩⟩
    · exact Or.inl (hlift (tightHasLift_of_good hdt h))

end F2

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

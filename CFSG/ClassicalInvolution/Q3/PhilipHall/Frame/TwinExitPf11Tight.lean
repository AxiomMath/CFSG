module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Lift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf11

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement


section Restrict

variable {G : Type} [Group G] [Finite G]

theorem aEmpty_restrictFamily_tight {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {X K : Subgroup G}
    (hKX : K ≤ X) (hA : AEmpty Ω K) : AEmpty (restrictFamily P X) (K.subgroupOf X) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin.aEmpty_restrict hΩ hPΩ hKX hA


theorem aEmpty_conjClass_section_tight {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {J : Subgroup G} (hJ : J ∈ Ω) (hA : AEmpty Ω J) {X : Subgroup G} (hJX : J ≤ X) :
    AEmpty (CoreAssembly.conjClass (J.subgroupOf X)) (J.subgroupOf X) := by
  rw [← restrictFamily_conjFamily hJX]
  exact aEmpty_restrictFamily_tight hΩ (conjFamily_subset hΩ.conjInvariant hJ X) hJX hA

end Restrict

section Datum

variable {Y : Type} [Group Y] [Finite Y]

theorem q8TwinDatum_of_tight {R : Subgroup Y}
    (hmod : IsPGroup 2 (↥R ⧸ classicalInvolutionOddCore ↥R)) (S : Sylow 2 R) {t : Y}
    (ht : IsUniqueInvolution R t) (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    Q8TwinDatum R S t := by
  have hSyl : IsSylow2In ((S : Subgroup R).map R.subtype) R := isSylow2In_map_subtype R S
  refine ⟨⟨3, le_rfl, hq8⟩, ?_, ?_, ?_, hmod⟩
  · exact Sec6Gen.mem_of_isSylow2In ht hSyl
  · exact orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  · intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (ht.commute_of_mem hw).symm

end Datum

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_or_exit_tight {n : ℕ} (hT : Thm1RTwinLiftSetBelow n) (hB : TightBelow n)
    (hG : Nat.card G < n) (hOG : classicalInvolutionOddCore G = ⊥) {Δ : Set (Subgroup G)}
    (hΩ : HypOmegaGen Δ) (htight : ∀ K ∈ Δ, tightCore K = K)
    (hmod : ∀ K ∈ Δ, IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K))
    (hq8 : ∀ K ∈ Δ, ∀ P : Subgroup G, IsSylow2In P K → Nonempty (↥P ≃* QuaternionGroup 2))
    (hA : ∀ K ∈ Δ, AEmpty Δ K)
    (hno : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → ¬ TightInO2 z) {K : Subgroup G}
    (hK : K ∈ Δ) {z : G} (hz : IsUniqueInvolution K z) :
    (∃ L : Subgroup G, IsLiftOf K L z) ∨
      ∃ (W : Subgroup G) (hKW : K ≤ W), IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : G) K) = W ∧
        Thm4Twin.F2.ExitSec W K hKW z hz := by
  obtain ⟨W, hKW, hWs, hWg⟩ := Thm4Twin.F2.exists_section K
  have hO : classicalInvolutionOddCore ↥W = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hOG W hWs
  have hlt : Nat.card W < n := lt_of_le_of_lt (Subgroup.card_le_card_group W) hG
  set R : Subgroup ↥W := K.subgroupOf W with hR
  set t : ↥W := ⟨z, hKW hz.mem⟩ with ht
  have hut : IsUniqueInvolution R t := isUniqueInvolution_subgroupOf hz hKW
  have htc : tightCore R = R := by
    have h1 : tightCore (K.subgroupOf W) = (tightCore K).subgroupOf W :=
      CFSG.ClassicalInvolution.Q3.tightCore_subgroupOf (by rw [htight K hK]; exact hKW)
    rw [hR, h1, htight K hK]
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  have hSylR := isSylow2In_map_subtype R S
  have hSylK : IsSylow2In (((S : Subgroup ↥R).map R.subtype).map W.subtype) K := by
    have := (isSylow2In_map_subtype_iff (Y := W)).mpr hSylR
    have h2 : R.map W.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKW
    rwa [h2] at this
  obtain ⟨e⟩ := hq8 K hK _ hSylK
  have hSq : Nonempty (↥(S : Subgroup ↥R) ≃* QuaternionGroup 2) :=
    ⟨(((S : Subgroup ↥R).equivMapOfInjective R.subtype R.subtype_injective).trans
      (((S : Subgroup ↥R).map R.subtype).equivMapOfInjective W.subtype
        W.subtype_injective)).trans e⟩
  have hd : Q8TwinDatum R S t :=
    q8TwinDatum_of_tight (isPGroup_two_quotient_subgroupOf K W (hmod K hK)) S hut hSq
  have hΩR : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := by
    rw [htc]; exact hypOmegaGen_conjClass_section hΩ hK hKW
  have hAR : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [htc]; exact aEmpty_conjClass_section_tight hΩ hK (hA K hK) hKW
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
    refine ⟨L.map W.subtype, hz, ?_, Thm4Twin.F2.isClassicalMember3_map_subtype hWs hL⟩
    have hKR : R.map W.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKW
    rw [← hKR]
    exact Subgroup.map_mono (htc ▸ hRL)
  have hnoO2 : ¬ TightInO2 t := fun h => hno K hK z hz (Thm4Twin.F2.tightInO2_of_subnormal hWs _ h)
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

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf11

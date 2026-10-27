module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Lift
public import CFSG.ClassicalInvolution.Q3.TL4SepCent

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tightCore_eq_self_of_twinT4Hyp {Δ : Set (Subgroup G)}
    (h : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) {K : Subgroup G} (hK : K ∈ Δ) :
    tightCore K = K := by
  rcases h.hyp.omega2 K hK with h1 | hne
  · exact h1
  · exfalso
    obtain ⟨e⟩ := hne
    have h3 : IsPGroup 2 SL(2, ZMod 3) := (h.twoGroup K hK).of_equiv e
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h3
    rw [natCard_sl2Three] at hk
    have h3dvd : 3 ∣ 2 ^ k := by
      rw [← hk]
      norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)

theorem q8TwinDatum_subgroupOf {Δ : Set (Subgroup G)}
    (h : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) {K : Subgroup G} (hK : K ∈ Δ) {z : G}
    (hz : IsUniqueInvolution K z) {W : Subgroup G} (hKW : K ≤ W)
    (S : Sylow 2 ↥(K.subgroupOf W)) :
    Q8TwinDatum (K.subgroupOf W) S ⟨z, hKW hz.mem⟩ ∧
      Nonempty (↥(S : Subgroup ↥(K.subgroupOf W)) ≃* QuaternionGroup 2) := by
  have hTR : IsSylow2In ((S : Subgroup ↥(K.subgroupOf W)).map (K.subgroupOf W).subtype)
      (K.subgroupOf W) := isSylow2In_map_sylow _ S
  have hP : IsSylow2In
      (((S : Subgroup ↥(K.subgroupOf W)).map (K.subgroupOf W).subtype).map W.subtype) K := by
    have h1 := isSylow2In_map_subtype_iff.mpr hTR
    rwa [Subgroup.map_subgroupOf_eq_of_le hKW] at h1
  obtain ⟨e⟩ := h.quat K hK _ hP
  have e' : ↥(S : Subgroup ↥(K.subgroupOf W)) ≃* QuaternionGroup 2 :=
    (((S : Subgroup ↥(K.subgroupOf W)).equivMapOfInjective _
      (K.subgroupOf W).subtype_injective).trans
      (Subgroup.equivMapOfInjective _ W.subtype W.subtype_injective)).trans e
  have hzP := Sec6Gen.mem_of_isSylow2In hz hP
  refine ⟨⟨⟨3, le_rfl, ⟨e'⟩⟩, ?_, ?_, ?_, ?_⟩, ⟨e'⟩⟩
  · obtain ⟨w, hw, hwz⟩ := hzP
    have hw' : w = ⟨z, hKW hz.mem⟩ := Subtype.ext hwz
    rw [← hw']
    exact hw
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  · intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hz.commute_of_mem (Subgroup.mem_subgroupOf.mp hw)).symm
  · exact isPGroup_two_quotient_subgroupOf K W (h.twoGroup K hK)

theorem aEmpty_restrictFamily' {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {X K : Subgroup G} (hKX : K ≤ X) (hA : AEmpty Ω K) :
    AEmpty (restrictFamily P X) (K.subgroupOf X) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin.aEmpty_restrict hΩ hPΩ hKX hA

theorem aEmpty_conjClass_section' {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {J : Subgroup G} (hJ : J ∈ Ω) (hA : AEmpty Ω J) {X : Subgroup G} (hJX : J ≤ X) :
    AEmpty (CoreAssembly.conjClass (J.subgroupOf X)) (J.subgroupOf X) := by
  rw [← PhilipHall.Frame.restrictFamily_conjFamily hJX]
  exact aEmpty_restrictFamily' hΩ (PhilipHall.Frame.conjFamily_subset hΩ.conjInvariant hJ X) hJX hA

theorem exists_secLift_or_exitR {n : ℕ} (hT : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n)
    (hB : TightBelow n) (hG : Nat.card G < n) {Δ : Set (Subgroup G)}
    (h : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) (hno : NoInvO2 Δ) {K : Subgroup G}
    (hK : K ∈ Δ) {z : G} (hz : IsUniqueInvolution K z) :
    ∃ (W : Subgroup G) (hKW : K ≤ W), IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : G) K) = W ∧
      (PhilipHall.Frame.Thm4Twin.F2.ExitSec W K hKW z hz ∨
        ∃ M : Subgroup ↥W, K.subgroupOf W ≤ M ∧ IsClassicalMember3 M ⟨z, hKW hz.mem⟩ ∧
          InClass3 (CoreAssembly.conjClass M)) := by
  obtain ⟨W, hKW, hWs, hWg⟩ := PhilipHall.Frame.Thm4Twin.F2.exists_section K
  refine ⟨W, hKW, hWs, hWg, ?_⟩
  have hO : classicalInvolutionOddCore ↥W = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree h.odd W hWs
  have hlt : Nat.card W < n := lt_of_le_of_lt (Subgroup.card_le_card_group W) hG
  set R : Subgroup ↥W := K.subgroupOf W with hR
  set t : ↥W := ⟨z, hKW hz.mem⟩ with ht
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  obtain ⟨hd, hSq⟩ := q8TwinDatum_subgroupOf h hK hz hKW S
  have hKK := tightCore_eq_self_of_twinT4Hyp h hK
  have htc : tightCore R = R := by
    rw [hR, tightCore_subgroupOf (hKK.symm ▸ hKW), hKK]
  have hΩR : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := by
    rw [htc]
    exact PhilipHall.Frame.hypOmegaGen_conjClass_section h.hyp hK hKW
  have hAR : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [htc]
    exact aEmpty_conjClass_section' h.hyp hK (h.aEmpty K hK) hKW
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
    rw [htc]
    exact hgenW
  have hzK : IsUniqueInvolution (tightCore R) t :=
    PhilipHall.Frame.Q8Datum.isUniqueInvolution_core hd
  have hcls : TightCls ↥W R S t := ⟨hSq, hgen, hO⟩
  have hlift : TightHasLift R t → ∃ M : Subgroup ↥W, R ≤ M ∧ IsClassicalMember3 M t ∧
      InClass3 (CoreAssembly.conjClass M) := by
    rintro ⟨M, hRM, hM⟩
    exact ⟨M, htc ▸ hRM, hM, inClass3_conjClass_of_lift hcls hRM hM⟩
  have hnoO2 : ¬ TightInO2 t := fun h' =>
    hno K hK z hz (PhilipHall.Frame.Thm4Twin.F2.tightInO2_of_subnormal hWs _ h')
  by_cases htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R
  · rcases hT.hasLift hlt hd hSq hgen hO hΩR hAR htw with h' | h' | h'
    · exact absurd h' hnoO2
    · exact Or.inl (Or.inl h')
    · exact Or.inr (hlift h')
  · have hsing : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
        {tightCore R} := by
      ext K'
      constructor
      · intro hK'
        by_contra hne
        exact htw ⟨K', hK', hne⟩
      · intro hK'
        rw [Set.mem_singleton_iff] at hK'
        subst hK'
        exact ⟨CoreAssembly.mem_conjClass_self _, t, hzK, hzK⟩
    have hnormal := (PhilipHall.Frame.twinSet_eq_singleton_iff (Q3B.conjInvariant_conjClass _)
      (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) (CoreAssembly.mem_conjClass_self _) hzK).mp hsing
    rw [htc] at hnormal
    have hdt : TightDatum R S t := hd.toTightDatum hnormal
    rcases hB ↥W hlt R S t hdt hcls with h' | h'
    · by_cases hin : TightInO2 t
      · exact absurd hin hnoO2
      · exact Or.inl (Or.inr ⟨S, hin, h'⟩)
    · exact Or.inr (hlift (tightHasLift_of_good hdt h'))

end CFSG.ClassicalInvolution.Q3.TL4

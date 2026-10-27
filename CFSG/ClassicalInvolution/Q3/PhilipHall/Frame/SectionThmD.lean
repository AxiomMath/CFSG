module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.TL3T21

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionThmD

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

variable {Y : Type} [Group Y] [Finite Y]

abbrev secClass (X K : Subgroup Y) : Set (Subgroup (SecQuot X)) :=
  CoreAssembly.conjClass (secImage X K)

theorem subgroupOf_inf_oddCore_eq_bot {X K : Subgroup Y} (hK2 : IsPGroup 2 K) :
    K.subgroupOf X ⊓ classicalInvolutionOddCore ↥X = ⊥ :=
  AscQuot.inf_eq_bot_of_isPGroup_of_odd _ hK2.comap_subtype le_rfl
    (odd_natCard_inf (CFSG.ComponentClassification.OddCore.odd_card ↥X) _)

@[expose] noncomputable def secImageEquiv {X K : Subgroup Y} (hKX : K ≤ X) (hK2 : IsPGroup 2 K) :
    ↥(secImage X K) ≃* ↥K :=
  (AscQuot.quotRestrictEquiv (subgroupOf_inf_oddCore_eq_bot hK2)).symm.trans
    (Subgroup.subgroupOfEquivOfLe hKX)

theorem natCard_secImage {X K : Subgroup Y} (hKX : K ≤ X) (hK2 : IsPGroup 2 K) :
    Nat.card (secImage X K) = Nat.card K :=
  Nat.card_congr (secImageEquiv hKX hK2).toEquiv

omit [Finite Y] in
theorem isPGroup_secImage {X K : Subgroup Y} (hK2 : IsPGroup 2 K) : IsPGroup 2 (secImage X K) :=
  hK2.comap_subtype.map _

theorem isUniqueInvolution_secImage {X J : Subgroup Y} (hJX : J ≤ X) (hJ2 : IsPGroup 2 J)
    {u : Y} (hu : IsUniqueInvolution J u) :
    IsUniqueInvolution (secImage X J) (secInv X ⟨u, hJX hu.mem⟩) :=
  AscQuot.isUniqueInvolution_map_mk (subgroupOf_inf_oddCore_eq_bot hJ2)
    (isUniqueInvolution_subgroupOf hu hJX)

omit [Finite Y] in
theorem secImage_conjSub {X K : Subgroup Y} (x : X) :
    secImage X (conjSub (x : Y) K) = conjSub (secInv X x) (secImage X K) := by
  unfold secImage secInv
  rw [← conjSub_subgroupOf]
  exact TwistQ.conjSub_map x (K.subgroupOf X)

theorem isUniqueInvolution_secImage_conjSub {X K : Subgroup Y} (hKX : K ≤ X)
    (hK2 : IsPGroup 2 K) {z : Y} (hz : IsUniqueInvolution K z) (x : X) :
    IsUniqueInvolution (secImage X (conjSub (x : Y) K))
      (secInv X (x * ⟨z, hKX hz.mem⟩ * x⁻¹)) := by
  have h := (isUniqueInvolution_secImage hKX hK2 hz).conj (secInv X x)
  rw [← secImage_conjSub] at h
  unfold secInv at h ⊢
  rwa [map_mul, map_mul, map_inv]

omit [Finite Y] in
theorem mem_secClass_iff {X K : Subgroup Y} {L : Subgroup (SecQuot X)} :
    L ∈ secClass X K ↔ ∃ x : X, secImage X (conjSub (x : Y) K) = L := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥X) g
    exact ⟨x, secImage_conjSub x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨secInv X x, (secImage_conjSub x).symm⟩

omit [Finite Y] in
theorem isPGroup_of_mem_secClass {X K : Subgroup Y} (hK2 : IsPGroup 2 K) :
    ∀ L ∈ secClass X K, IsPGroup 2 L := by
  rintro _ ⟨g, rfl⟩
  exact isPGroup_conjSub g (isPGroup_secImage hK2)

theorem natCard_of_mem_secClass {X K : Subgroup Y} (hKX : K ≤ X) (hK2 : IsPGroup 2 K) :
    ∀ L ∈ secClass X K, Nat.card L = Nat.card K := by
  rintro _ ⟨g, rfl⟩
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans
    (natCard_secImage hKX hK2)

omit [Finite Y] in
theorem secClass_trans {X K : Subgroup Y} :
    ∀ L ∈ secClass X K, ∀ L' ∈ secClass X K, ∃ g : SecQuot X, conjSub g L = L' := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨b * a⁻¹, ?_⟩
  show conjSub (b * a⁻¹) (conjSub a (secImage X K)) = conjSub b (secImage X K)
  rw [conjSub_mul, conjSub_inv_conjSub]

omit [Finite Y] in
theorem pSpan_secClass {X K : Subgroup Y} (hKX : K ≤ X)
    (hgen : (⨆ x : X, conjSub (x : Y) K) = X) : TC.Thin.pSpan (secClass X K) = ⊤ := by
  have hconj : ∀ g : ↥X, (conjSub g (K.subgroupOf X)).map X.subtype = conjSub (g : Y) K := by
    intro g
    have hle : conjSub (g : Y) K ≤ X := by
      have := conjSub_mono (n := (g : Y)) hKX
      rwa [conjSub_eq_self_of_mem g.2] at this
    rw [conjSub_subgroupOf]
    exact Subgroup.map_subgroupOf_eq_of_le hle
  have hgenX : (⨆ g : ↥X, conjSub g (K.subgroupOf X)) = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [hconj]
    exact hgen
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥X)), ← hgenX, Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [TwistQ.conjSub_map]
  exact TC.Thin.le_pSpan ⟨QuotientGroup.mk' _ g, rfl⟩

theorem thmDHyp_secClass {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {K X V : Subgroup Y} (hK : K ∈ Ω) (hK8 : Nat.card K = 8)
    (hKA : AEmpty Ω K) (hKX : K ≤ X) (hgen : (⨆ x : X, conjSub (x : Y) K) = X) {z : Y}
    (hz : IsUniqueInvolution K z) (hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (hV2 : IsPGroup 2 V) (hzV : z ∈ V) : TC.Thin.ThmDHyp 3 (secClass X K) := by
  have hK2 : IsPGroup 2 K := h2 K hK
  have hJ2 : IsPGroup 2 (K.subgroupOf X) := hK2.comap_subtype
  have hΩX := hypOmegaGen_conjClass_section hΩ hK hKX
  have hAJ := aEmpty_conjClass_section hΩ h2 hK hKA hKX
  have hmem : ∀ L ∈ CoreAssembly.conjClass (K.subgroupOf X), IsPGroup 2 L := by
    rintro _ ⟨g, rfl⟩
    exact isPGroup_conjSub g hJ2
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hfam : quotFamily (CoreAssembly.conjClass (K.subgroupOf X))
      (classicalInvolutionOddCore ↥X) = secClass X K :=
    image_conjClass (N := classicalInvolutionOddCore ↥X) (K.subgroupOf X)
  have hq := OddQuot.hypOmegaGen_quotFamily hΩX hmem hNodd
  have hAall := aEmpty_forall_of_transitive hΩX.conjInvariant (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) hAJ
  have hAq := OddQuot.aEmpty_quotFamily hΩX hmem hNodd hAall
  rw [hfam] at hq hAq
  have hVXn : (V.subgroupOf X).Normal :=
    ⟨fun v hv g => Subgroup.mem_subgroupOf.mpr (hVn g g.2 v (Subgroup.mem_subgroupOf.mp hv))⟩
  have hVbn : ((V.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))).Normal :=
    hVXn.map _ (QuotientGroup.mk'_surjective _)
  have hzVb : secInv X ⟨z, hKX hz.mem⟩ ∈
      (V.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzV)
  refine
    { hyp := hq
      two := isPGroup_of_mem_secClass hK2
      card := fun L hL => (natCard_of_mem_secClass hKX hK2 L hL).trans (hK8.trans (by norm_num))
      aEmpty := hAq
      gen := pSpan_secClass hKX hgen
      trans := secClass_trans
      odd := CFSG.ComponentClassification.OddCore.quotient_corefree ↥X
      inO2 := ?_ }
  rintro _ ⟨g, rfl⟩ u hu
  refine ⟨_, hVbn, hV2.comap_subtype.map _, ?_⟩
  have hgu : g * secInv X ⟨z, hKX hz.mem⟩ * g⁻¹ = u :=
    ((isUniqueInvolution_secImage hKX hK2 hz).conj g).eq hu
  rw [← hgu]
  exact hVbn.conj_mem _ hzVb g

theorem thmDConcl_at_section {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {K X V : Subgroup Y} (hK : K ∈ Ω) (hK8 : Nat.card K = 8)
    (hKA : AEmpty Ω K) (hKX : K ≤ X) (hgen : (⨆ x : X, conjSub (x : Y) K) = X) {z : Y}
    (hz : IsUniqueInvolution K z) (hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (hV2 : IsPGroup 2 V) (hzV : z ∈ V) {n : ℕ} (hD : TC.Thin.ThmDAbsBelow 3 n)
    (hXn : Nat.card X < n) : TC.Thin.ThmDConcl (secClass X K) := by
  have hcard : Nat.card (SecQuot X) < n :=
    lt_of_le_of_lt
      (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card (classicalInvolutionOddCore ↥X))) hXn
  exact TC.Thin.thmDAbsAt_iff.mp (hD _ hcard) _
    (thmDHyp_secClass hΩ h2 hK hK8 hKA hKX hgen hz hVn hV2 hzV)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionThmD

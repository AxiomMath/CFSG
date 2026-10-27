module

public import CFSG.ClassicalInvolution.Q3.TL4SepDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G]

theorem aEmpty_of_twinSet [Finite G] {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ) {K : Subgroup G}
    (hK : K ∈ Δ) (htw : twinSet Δ K = {K}) : AEmpty Δ K := by
  intro J hJ hJn zK zJ hzK hzJ
  by_contra hcon
  have hInA : InA Δ K J := ⟨hJ, hJn, zK, zJ, hzK, hzJ, hcon⟩
  obtain ⟨u, v, r, t', Kstar, ustar, rstar, -, -, -, -, -, -, -, -, -, -, -, hne, htw', -⟩ :=
    Sec6Gen.l6_4ThreeGen G _ hΩ _ hK J hJ.1 hInA zK zJ hzK hzJ _ _ rfl rfl
  have hmem : Kstar ∈ twinSet Δ K := by
    rw [htw']
    exact Or.inr rfl
  rw [htw] at hmem
  exact hne hmem

theorem twinSet_eq_of_noTwins {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (htwin : ∀ J ∈ Δ, ∀ J' ∈ Δ, ∀ u : G, IsUniqueInvolution J u → IsUniqueInvolution J' u →
      J = J') {K : Subgroup G} (hK : K ∈ Δ) : twinSet Δ K = {K} := by
  ext J
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hJ, z, hzK, hzJ⟩
    exact htwin J hJ K hK z hzJ hzK
  · rintro rfl
    obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 J hK
    exact ⟨hK, z, hz, hz⟩

theorem T4Hyp.of_noTwins [Finite G] {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    (hquat : ∀ J ∈ Δ, ∀ P : Subgroup G, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (htight : ∀ J ∈ Δ, ∀ u : G, IsUniqueInvolution J u →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (htwin : ∀ J ∈ Δ, ∀ J' ∈ Δ, ∀ u : G, IsUniqueInvolution J u → IsUniqueInvolution J' u →
      J = J')
    (hO : classicalInvolutionOddCore G = ⊥) : T4Hyp r G Δ :=
  ⟨hΩ, h2, hquat, htight, htwin,
    fun _ hK => aEmpty_of_twinSet hΩ hK (twinSet_eq_of_noTwins hΩ htwin hK), hO⟩

theorem T4Hyp.of_isPGroup [Finite G] {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hquat : ∀ J ∈ Δ, ∀ P : Subgroup G, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (htight : ∀ J ∈ Δ, ∀ u : G, IsUniqueInvolution J u →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (htwin : ∀ J ∈ Δ, ∀ J' ∈ Δ, ∀ u : G, IsUniqueInvolution J u → IsUniqueInvolution J' u →
      J = J')
    (hO : classicalInvolutionOddCore G = ⊥) : T4Hyp r G Δ :=
  T4Hyp.of_noTwins hΩ (fun J hJ => (h2 J hJ).to_quotient _) hquat htight htwin hO

theorem hypOmegaGen_sub {Δ Δ' : Set (Subgroup G)} (hΩ : HypOmegaGen Δ) (hsub : Δ' ⊆ Δ)
    (hinv : ConjInvariant Δ') : HypOmegaGen Δ' where
  conjInvariant := hinv
  omega1 := fun K hK => hΩ.omega1 K (hsub hK)
  omega2 := fun K hK => hΩ.omega2 K (hsub hK)
  omega3 := fun K hK J hJ => hΩ.omega3 K (hsub hK) J (hsub hJ)
  omega4 := fun K hK J hJ => hΩ.omega4 K (hsub hK) J (hsub hJ)
  omega5 := fun K hK J hJ => hΩ.omega5 K (hsub hK) J (hsub hJ)

theorem T4Hyp.sub [Finite G] {Δ Δ' : Set (Subgroup G)} (h : T4Hyp r G Δ) (hsub : Δ' ⊆ Δ)
    (hinv : ConjInvariant Δ') : T4Hyp r G Δ' :=
  T4Hyp.of_noTwins (hypOmegaGen_sub h.hyp hsub hinv) (fun J hJ => h.twoGroup J (hsub hJ))
    (fun J hJ => h.quat J (hsub hJ)) (fun J hJ => h.tight J (hsub hJ))
    (fun J hJ J' hJ' => h.noTwins J (hsub hJ) J' (hsub hJ')) h.odd

theorem T4Hyp.restrict [Finite G] {Δ : Set (Subgroup G)} (h : T4Hyp r G Δ) (X : Subgroup G)
    (hX : classicalInvolutionOddCore ↥X = ⊥) : T4Hyp r ↥X (restrictFamily Δ X) := by
  refine T4Hyp.of_noTwins (PhilipHall.Frame.hypOmegaGen_restrict h.hyp X) ?_ ?_ ?_ ?_ hX
  · rintro _ ⟨L, hL, hLX, rfl⟩
    let φ : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
    exact (h.twoGroup L hL).of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm
  · rintro _ ⟨L, hL, hLX, rfl⟩ P hP
    have hP' : IsSylow2In (P.map X.subtype) L := by
      have := isSylow2In_map_subtype_iff.mpr hP
      rwa [Subgroup.map_subgroupOf_eq_of_le hLX] at this
    obtain ⟨e⟩ := h.quat L hL _ hP'
    exact ⟨(P.equivMapOfInjective X.subtype X.subtype_injective).trans e⟩
  · rintro _ ⟨L, hL, hLX, rfl⟩ u hu c hc
    have hu' := isUniqueInvolution_of_subgroupOf hu hLX
    have hcG : (c : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      exact congrArg Subtype.val hc
    exact (mem_normalizer_subgroupOf_iff hLX).mp (h.tight L hL _ hu' hcG)
  · rintro _ ⟨L, hL, hLX, rfl⟩ _ ⟨L', hL', hL'X, rfl⟩ u hu hu'
    rw [h.noTwins L hL L' hL' (u : G) (isUniqueInvolution_of_subgroupOf hu hLX)
      (isUniqueInvolution_of_subgroupOf hu' hL'X)]

theorem exists_conjSub_of_restrict {X K J : Subgroup G} (hKX : K ≤ X) (hJX : J ≤ X)
    (h : ∃ x : X, conjSub x (K.subgroupOf X) = J.subgroupOf X) :
    ∃ g : G, g ∈ X ∧ conjSub g K = J := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x, x.2, ?_⟩
  rw [conjSub_subgroupOf] at hx
  have hle : conjSub (x : G) K ≤ X := by
    have := conjSub_mono (n := (x : G)) hKX
    rwa [conjSub_eq_self_of_mem x.2] at this
  have := Subgroup.subgroupOf_inj.mp hx
  rwa [inf_eq_left.mpr hle, inf_eq_left.mpr hJX] at this

theorem commutes_of_restrict {X K J : Subgroup G} (hKX : K ≤ X) (hJX : J ≤ X)
    (h : Commutes (K.subgroupOf X) (J.subgroupOf X)) : Commutes K J := by
  intro a ha b hb
  have := h ⟨a, hKX ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨b, hJX hb⟩
    (Subgroup.mem_subgroupOf.mpr hb)
  exact congrArg Subtype.val this

end CFSG.ClassicalInvolution.Q3.TL4

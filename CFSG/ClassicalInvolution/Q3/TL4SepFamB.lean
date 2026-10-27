module

public import CFSG.ClassicalInvolution.Q3.TL4SepFam

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G]

theorem TightFam.restrict {Δ : Set (Subgroup G)} (h : TightFam r G Δ) (X : Subgroup G) :
    TightFam r ↥X (restrictFamily Δ X) where
  conjInvariant := by
    rintro n _ ⟨L, hL, hLX, rfl⟩
    refine ⟨conjSub (n : G) L, h.conjInvariant _ L hL, ?_, conjSub_subgroupOf X n L⟩
    have := conjSub_mono (n := (n : G)) hLX
    rwa [conjSub_eq_self_of_mem n.2] at this
  inv := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    obtain ⟨u, hu⟩ := h.inv L hL
    exact ⟨_, isUniqueInvolution_subgroupOf hu hLX⟩
  gen := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    apply Subgroup.map_injective X.subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le hLX]
    conv_rhs => rw [← h.gen L hL]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, ⟨hxL, hx2⟩, rfl⟩
      exact ⟨hxL, isPGroup_zpowers_coe_iff.mpr hx2⟩
    · rintro ⟨hyL, hy2⟩
      exact ⟨⟨y, hLX hyL⟩, ⟨hyL, isPGroup_zpowers_coe_iff.mp hy2⟩, rfl⟩
  twoGroup := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    let φ : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
    exact (h.twoGroup L hL).of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm
  quat := by
    rintro _ ⟨L, hL, hLX, rfl⟩ P hP
    have hP' : IsSylow2In (P.map X.subtype) L := by
      have := isSylow2In_map_subtype_iff.mpr hP
      rwa [Subgroup.map_subgroupOf_eq_of_le hLX] at this
    obtain ⟨e⟩ := h.quat L hL _ hP'
    exact ⟨(P.equivMapOfInjective X.subtype X.subtype_injective).trans e⟩
  tight := by
    rintro _ ⟨L, hL, hLX, rfl⟩ u hu c hc
    have hu' := isUniqueInvolution_of_subgroupOf hu hLX
    have hcG : (c : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      exact congrArg Subtype.val hc
    exact (mem_normalizer_subgroupOf_iff hLX).mp (h.tight L hL _ hu' hcG)
  noTwins := by
    rintro _ ⟨L, hL, hLX, rfl⟩ _ ⟨L', hL', hL'X, rfl⟩ u hu hu'
    rw [h.noTwins L hL L' hL' (u : G) (isUniqueInvolution_of_subgroupOf hu hLX)
      (isUniqueInvolution_of_subgroupOf hu' hL'X)]

omit [Finite G] in
theorem closure_twoElements_tightCore (R : Subgroup G) :
    Subgroup.closure {x : G | x ∈ tightCore R ∧ IsPGroup 2 (Subgroup.zpowers x)} =
      tightCore R := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun _ hx => hx.1) ?_
  exact (Subgroup.closure_le _).mpr fun x hx =>
    Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩

variable {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightDatum.twoGroup_core (hd : TightDatum R S t) :
    IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) := by
  set K := tightCore R
  have hle : K ⊓ oddCoreImg R ≤ oddCoreImg K := by
    refine TC.le_oddCoreImg_of_normalizes inf_le_left (fun e he n hn => ⟨?_, ?_⟩) ?_
    · exact K.mul_mem (K.mul_mem he hn.1) (K.inv_mem he)
    · exact conj_mem_oddCoreImg (Subgroup.le_normalizer (tightCore_le R he)) hn.2
    · exact (odd_natCard_oddCoreImg R).of_dvd_nat
        (Subgroup.card_dvd_of_le (inf_le_right : K ⊓ oddCoreImg R ≤ oddCoreImg R))
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥K) q
  obtain ⟨k, hk⟩ := hd.twoGroup (QuotientGroup.mk' (classicalInvolutionOddCore ↥R)
    ⟨(x : G), tightCore_le R x.2⟩)
  refine ⟨k, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk ⊢
  have h1 : ((x : G) ^ 2 ^ k) ∈ oddCoreImg R := ⟨_, hk, by simp⟩
  have h2 : ((x : G) ^ 2 ^ k) ∈ K ⊓ oddCoreImg R := ⟨K.pow_mem x.2 _, h1⟩
  obtain ⟨y, hy, hyx⟩ := hle h2
  have : y = x ^ 2 ^ k := Subtype.ext (by rw [Subgroup.coe_pow]; exact hyx)
  rw [← this]
  exact hy

theorem TightFam.of_datum (hd : TightDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    TightFam r G (CoreAssembly.conjClass (tightCore R)) where
  conjInvariant := hd.hypOmegaGen.conjInvariant
  inv := fun _ hJ => hd.exists_isUniqueInvolution_member hJ
  gen := by
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [conjSub_tightCore]
    exact closure_twoElements_tightCore _
  twoGroup := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨_, hd', -⟩ := hd.conj g
    dsimp only
    let φ : ↥(conjSub g (tightCore R)) ≃* ↥(tightCore (conjSub g R)) :=
      MulEquiv.subgroupCongr (conjSub_tightCore R g)
    exact (TightDatum.twoGroup_core hd').of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm
  quat := by
    rintro _ ⟨g, rfl⟩ P hP
    obtain ⟨eS⟩ := hq
    set P₀ := conjSub g ((S : Subgroup R).map R.subtype) with hP₀def
    have hP₀ : IsSylow2In P₀ (conjSub g (tightCore R)) := Asc77.IsSylow2In.conj hd.sylow_core g
    obtain ⟨c, -, hc⟩ := S1916.IsSylow2In.exists_conj hP₀ hP
    let e₁ : ↥P ≃* ↥P₀ := (MulEquiv.subgroupCongr hc).symm.trans
      (P₀.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).symm
    let e₂ : ↥P₀ ≃* ↥((S : Subgroup R).map R.subtype) :=
      (((S : Subgroup R).map R.subtype).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm
    let e₃ : ↥((S : Subgroup R).map R.subtype) ≃* ↥(S : Subgroup R) :=
      ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm
    exact ⟨((e₁.trans e₂).trans e₃).trans eS⟩
  tight := fun _ hJ _ hu => (hd.normalizer_eq_centralizer_member hJ hu).ge
  noTwins := fun _ hJ _ hJ' _ hu hu' => hd.eq_of_isUniqueInvolution_member hJ hJ' hu hu'

end CFSG.ClassicalInvolution.Q3.TL4

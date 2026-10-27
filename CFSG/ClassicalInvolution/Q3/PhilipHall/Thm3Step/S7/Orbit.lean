module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Ident
import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Sub
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf17Inst

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step CFSG.ClassicalInvolution.Disconnected.AschTight

section Simple

variable {Y : Type} [Group Y] {L : Subgroup Y}

theorem centralizer_eq_bot_of_fStarSimple [Finite Y] (hF : FStarSimple Y) :
    Subgroup.centralizer (genFittingFStar Y : Set Y) = ⊥ :=
  haveI := hF.1
  centralizer_genFittingFStar_eq_bot hF.2

theorem le_of_le_normalizer (hLn : L.Normal) [IsSimpleGroup ↥L]
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) {X : Subgroup Y}
    (hX : L ≤ Subgroup.normalizer (X : Set Y)) (hne : X ≠ ⊥) : L ≤ X := by
  have hXL : (X.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp (hX g.2) n).mp hn
    simpa using h1
  rcases hXL.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply hne
    rw [eq_bot_iff, ← hC]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hc : x * l * x⁻¹ * l⁻¹ ∈ X ⊓ L := by
      refine ⟨?_, L.mul_mem (hLn.conj_mem l hl x) (L.inv_mem hl)⟩
      have h1 : l * x⁻¹ * l⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hX hl) x⁻¹).mp (X.inv_mem hx)
      have h2 : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
      rw [h2]
      exact X.mul_mem hx h1
    have hc' : (⟨_, hc.2⟩ : L) ∈ X.subgroupOf L := hc.1
    rw [hb, Subgroup.mem_bot] at hc'
    have h1 : x * l * x⁻¹ * l⁻¹ = 1 := congrArg Subtype.val hc'
    calc l * x = (x * l * x⁻¹ * l⁻¹)⁻¹ * (x * l) := by group
      _ = x * l := by rw [h1, inv_one, one_mul]
  · intro l hl
    have : (⟨l, hl⟩ : L) ∈ X.subgroupOf L := by rw [ht]; trivial
    exact this

theorem le_normalizer_map_subtype {H : Subgroup Y} {P : Subgroup H} (hP : P.Normal) :
    H ≤ Subgroup.normalizer (P.map H.subtype : Set Y) := by
  refine Subgroup.le_normalizer_iff.mpr fun h hh k hk => ?_
  obtain ⟨p, hp, rfl⟩ := hk
  exact ⟨⟨h, hh⟩ * p * ⟨h, hh⟩⁻¹, hP.conj_mem p hp _, rfl⟩

theorem oddCore_eq_bot_of_le [Finite Y] (hO : classicalInvolutionOddCore Y = ⊥) (hLn : L.Normal)
    [IsSimpleGroup ↥L] (hC : Subgroup.centralizer (L : Set Y) = ⊥) {X : Subgroup Y}
    (hLX : L ≤ X) : classicalInvolutionOddCore ↥X = ⊥ := by
  set O := (classicalInvolutionOddCore ↥X).map X.subtype with hOdef
  have hO' : O = ⊥ := by
    by_contra hne
    have hLO : L ≤ O := le_of_le_normalizer hLn hC
      (hLX.trans (le_normalizer_map_subtype inferInstance)) hne
    have hodd : Odd (Nat.card L) := by
      have h1 : Odd (Nat.card O) := by
        rw [hOdef, Subgroup.card_map_of_injective X.subtype_injective]
        exact CFSG.ComponentClassification.OddCore.odd_card ↥X
      exact h1.of_dvd_nat (Subgroup.card_dvd_of_le hLO)
    have hLb : L ≤ classicalInvolutionOddCore Y := le_sSup ⟨hLn, hodd⟩
    rw [hO, le_bot_iff] at hLb
    have : Nontrivial ↥L := IsSimpleGroup.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).mp this hLb
  exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hO'

theorem noNormalTwo_of_le (h2 : NoNormalTwo Y) (hLn : L.Normal) [IsSimpleGroup ↥L]
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) {X : Subgroup Y} (hLX : L ≤ X) :
    NoNormalTwo ↥X := by
  intro P hP hP2
  have hP' : P.map X.subtype = ⊥ := by
    by_contra hne
    have hLP : L ≤ P.map X.subtype :=
      le_of_le_normalizer hLn hC (hLX.trans (le_normalizer_map_subtype hP)) hne
    have hL2 : IsPGroup 2 ↥L := (hP2.map X.subtype).to_le hLP
    have hLb := h2 L hLn hL2
    have : Nontrivial ↥L := IsSimpleGroup.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).mp this hLb
  exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hP'

theorem genFittingFStar_eq_of_le [Finite Y] (hLn : L.Normal) [IsSimpleGroup ↥L]
    (hnab : ∃ a b : L, a * b ≠ b * a) (hC : Subgroup.centralizer (L : Set Y) = ⊥)
    {X : Subgroup Y} (hLX : L ≤ X) : genFittingFStar ↥X = L.subgroupOf X := by
  let e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  haveI : (L.subgroupOf X).Normal := hLn.subgroupOf X
  haveI : IsSimpleGroup ↥(L.subgroupOf X) := e.isSimpleGroup
  refine genFittingFStar_eq_of_normal_simple (L.subgroupOf X) ?_ ?_
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  · refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : (x : Y) ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hx ⟨l, hLX hl⟩ (Subgroup.mem_subgroupOf.mpr hl))
    rw [hC, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')

theorem fStarSimple_of_le [Finite Y] (hLn : L.Normal) [IsSimpleGroup ↥L]
    (hnab : ∃ a b : L, a * b ≠ b * a) (hC : Subgroup.centralizer (L : Set Y) = ⊥)
    {X : Subgroup Y} (hLX : L ≤ X) : FStarSimple ↥X := by
  have hF := genFittingFStar_eq_of_le hLn hnab hC hLX
  let e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  unfold FStarSimple
  rw [hF]
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end Simple

section Orbit

variable {Y : Type} [Group Y] {L M : Subgroup Y}

theorem mem_lOrbit_self : M ∈ lOrbit L M :=
  ⟨1, L.one_mem, conjSub_one M⟩

theorem lOrbit_subset {Φ : Set (Subgroup Y)} (hΦ : ConjInvariant Φ) (hM : M ∈ Φ) :
    lOrbit L M ⊆ Φ := by
  rintro _ ⟨l, -, rfl⟩
  exact hΦ l M hM

theorem le_conjStab_lOrbit : L ≤ conjStab (lOrbit L M) := by
  intro l hl
  rw [mem_conjStab_iff]
  intro N
  constructor
  · rintro ⟨l', hl', hN⟩
    refine ⟨l⁻¹ * l', L.mul_mem (L.inv_mem hl) hl', ?_⟩
    rw [conjSub_mul, hN, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  · rintro ⟨l', hl', rfl⟩
    exact ⟨l * l', L.mul_mem hl hl', conjSub_mul _ _ _⟩

theorem omegaGen_le_conjStab_lOrbit (hLn : L.Normal) :
    omegaGen (lOrbit L M) ≤ conjStab (lOrbit L M) := by
  refine iSup₂_le fun N hN n hn => ?_
  rw [mem_conjStab_iff]
  intro P
  constructor
  · intro hP
    have := lOrbit_stable hLn hN (N.inv_mem hn) hP
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  · exact lOrbit_stable hLn hN hn

theorem le_omegaGen_lOrbit (hLn : L.Normal) [IsSimpleGroup ↥L]
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (hM : M ≠ ⊥) : L ≤ omegaGen (lOrbit L M) :=
  le_of_le_normalizer hLn hC (le_conjStab_lOrbit.trans (T3Core.conjStab_le_normalizer_omegaGen _))
    fun h => hM (le_bot_iff.mp (h ▸ le_omegaGen mem_lOrbit_self))

theorem conjClass_subgroupOf_eq (hLn : L.Normal) (hLH : L ≤ omegaGen (lOrbit L M)) :
    CoreAssembly.conjClass (M.subgroupOf (omegaGen (lOrbit L M))) =
      restrictFamily (lOrbit L M) (omegaGen (lOrbit L M)) := by
  set H := omegaGen (lOrbit L M) with hH
  have hMH : M ≤ H := le_omegaGen mem_lOrbit_self
  ext N
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨conjSub (h : Y) M, (mem_conjStab_iff.mp (omegaGen_le_conjStab_lOrbit hLn h.2) M).mpr
      mem_lOrbit_self, ?_, conjSub_subgroupOf H h M⟩
    have := conjSub_mono (n := (h : Y)) hMH
    rwa [conjSub_eq_self_of_mem h.2] at this
  · rintro ⟨_, ⟨l, hl, rfl⟩, -, rfl⟩
    exact ⟨⟨l, hLH hl⟩, conjSub_subgroupOf H ⟨l, hLH hl⟩ M⟩

end Orbit

section AEmpty

variable {G : Type} [Group G] [Finite G]

theorem aEmpty_restrict_of_sub {Ω P : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (hPΩ : P ⊆ Ω)
    {X K : Subgroup G} (hKX : K ≤ X) (hA : AEmpty P K) :
    AEmpty (restrictFamily P X) (K.subgroupOf X) := by
  intro J' hJ'star hJ'nbr zK' zJ' hzK' hzJ'
  set J : Subgroup G := J'.map X.subtype with hJdef
  have hJ'eq : J.subgroupOf X = J' := subgroupOf_map_subtype' J'
  have hJX : J ≤ X := Subgroup.map_subtype_le J'
  have hJP : J ∈ P := mem_restrictFamily_iff.mp hJ'star.1
  have hstar : J ∈ omegaStarNbr P K := omegaStarNbr_of_restrict hKX hJX (by rwa [hJ'eq])
  have hnbr : J ∉ omegaNbr P K := by
    intro h
    apply hJ'nbr
    rw [← hJ'eq]
    obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
    have hTs : IsSylow2In T J :=
      Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ (hPΩ hJP) (rSet_subset hPΩ hT) hTJ
    have hTX : T ≤ X := hTJ.trans hJX
    have hTs' : IsSylow2In (T.subgroupOf X) (J.subgroupOf X) := by
      refine isSylow2In_map_subtype_iff.mp ?_
      rwa [Subgroup.map_subgroupOf_eq_of_le hTX, Subgroup.map_subgroupOf_eq_of_le hJX]
    refine ⟨subgroupOf_mem_restrictFamily hJP hJX, subgroupOf_ne_of_ne hKX hJX hne,
      T.subgroupOf X, mem_RSet_of_isSylow2In (subgroupOf_mem_restrictFamily hJP hJX) hTs',
      fun x hx => hTJ hx, fun x hx => ?_⟩
    exact (mem_normalizer_subgroupOf_iff hKX).mp (hTN (Subgroup.mem_subgroupOf.mp hx))
  have hzK : IsUniqueInvolution K (zK' : G) := isUniqueInvolution_of_subgroupOf hzK' hKX
  have hzJ : IsUniqueInvolution J (zJ' : G) :=
    isUniqueInvolution_of_subgroupOf (by rwa [hJ'eq]) hJX
  obtain ⟨g, hg, hgK⟩ := hA J hstar hnbr _ _ hzK hzJ
  set Z' : Subgroup X := Subgroup.closure ({zK', zJ'} : Set X) with hZ'
  have hZ : Z'.map X.subtype = Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :=
    map_closure_pair_subtype zK' zJ'
  have hZX : Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) ≤ X := by
    rw [← hZ]; exact Subgroup.map_subtype_le _
  have hgX : g ∈ X := by
    have : pairNormalizers K J (zK' : G) (zJ' : G) ≤ X := by
      unfold pairNormalizers
      exact sup_le (inf_le_left.trans hKX) (inf_le_left.trans hJX)
    exact this hg
  have hN : ∀ {A : Subgroup G}, A ≤ X →
      (A ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
        Subgroup G) : Set G)).subgroupOf X ≤
        A.subgroupOf X ⊓ Subgroup.normalizer ((Z' : Subgroup X) : Set X) := by
    intro A hAX x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hx.1, ?_⟩
    have := (mem_normalizer_subgroupOf_iff hZX).mp hx.2
    rwa [← hZ, subgroupOf_map_subtype'] at this
  have hAX : K ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ X := inf_le_left.trans hKX
  have hBX : J ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ X := inf_le_left.trans hJX
  have hmem : (⟨g, hgX⟩ : X) ∈ (pairNormalizers K J (zK' : G) (zJ' : G)).subgroupOf X :=
    Subgroup.mem_subgroupOf.mpr hg
  have hmem' : (⟨g, hgX⟩ : X) ∈ pairNormalizers (K.subgroupOf X) J' zK' zJ' := by
    have h1 := hmem
    unfold pairNormalizers at h1
    rw [Subgroup.subgroupOf_sup hAX hBX] at h1
    have h2' := hN (A := K) hKX
    have h3 := hN (A := J) hJX
    rw [hJ'eq] at h3
    exact sup_le_sup h2' h3 h1
  refine ⟨⟨g, hgX⟩, hmem', ?_⟩
  rw [conjSub_subgroupOf X ⟨g, hgX⟩ K]
  show (conjSub g K).subgroupOf X = J'
  rw [hgK]
  exact hJ'eq

end AEmpty

section Ctx


theorem orbitHyp_of_ctx {m : ℕ} {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}
    {K : Subgroup Y} (hc : Ctx m Y Φ K) (h2 : NoNormalTwo Y) (hF : FStarSimple Y)
    {M : Subgroup Y} (hM : M ∈ Φ) (hA : AEmpty (lOrbit (genFittingFStar Y) M) M) {z : Y}
    (hz : IsUniqueInvolution M z) :
    ∃ hzH : z ∈ omegaGen (lOrbit (genFittingFStar Y) M),
      OrbitHyp ↥(omegaGen (lOrbit (genFittingFStar Y) M))
        (M.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩ := by
  set L := genFittingFStar Y with hL
  set H := omegaGen (lOrbit L M) with hH
  haveI : IsSimpleGroup ↥L := hF.1
  have hLn : L.Normal := genFittingFStar_normal Y
  have hC := centralizer_eq_bot_of_fStarSimple hF
  have hMne : M ≠ ⊥ := fun h => hz.ne_one (Subgroup.mem_bot.mp (h ▸ hz.mem))
  have hLH : L ≤ H := le_omegaGen_lOrbit hLn hC hMne
  have hMH : M ≤ H := le_omegaGen mem_lOrbit_self
  have hcl := conjClass_subgroupOf_eq hLn hLH
  have hΨΦ : lOrbit L M ⊆ Φ := lOrbit_subset hc.hyp.hyp.conjInvariant hM
  have hsubΦ : CoreAssembly.conjClass (M.subgroupOf H) ⊆ restrictFamily Φ H := by
    rw [hcl]
    rintro _ ⟨N, hN, hNH, rfl⟩
    exact ⟨N, hΨΦ hN, hNH, rfl⟩
  have hFH := fStarSimple_of_le hLn hF.2 hC hLH
  refine ⟨hMH hz.mem, ?_⟩
  exact
    { odd := oddCore_eq_bot_of_le hc.odd hLn hC hLH
      two := noNormalTwo_of_le h2 hLn hC hLH
      fstar := hFH
      cent := centralizer_eq_bot_of_fStarSimple hFH
      hyp := typeRHyp_of_subset (hc.hyp.restrict H) hsubΦ (TL4.conjInvariant_conjClass _)
      gen := by rw [hcl]; exact omegaGen_restrictFamily_eq_top _ _ rfl
      aEmpty := by rw [hcl]; exact aEmpty_restrict_of_sub hc.hyp.hyp hΨΦ hMH hA
      inv := isUniqueInvolution_subgroupOf hz hMH }

end Ctx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConnEight
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanSignalizer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanLatticePar
public import CFSG.Sporadic.Schreier.ONEightNormalizers
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Choice
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Lift
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.MonsterDefs
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Walter.JRFacts
public import Certificates.Certificate3085Base

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open CFSG.ComponentClassification.GSThmB.OddQuot
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore
open CFSG.ClassicalInvolution.Balance (deltaCore TwoBalancedWrt)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isElemTwo_of_isElementaryAbelian {X : Type*} [Group X] {A : Subgroup X}
    [CFSG.IsElementaryAbelian 2 A] : IsElemTwo A := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  · have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    simpa [pow_two] using h

private theorem isElemTwo_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {A : Subgroup X}
    (hA : IsElemTwo A) : IsElemTwo (A.map f) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hA.1 x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hA.2 x hx, map_one]

theorem omSub_sqSub_of_on
    {P R : Subgroup G} (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan) (hR : IsSylowTwoIn R P) :
    IsElemTwo (omSub (sqSub R)) ∧ Nat.card (omSub (sqSub R)) = 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := ↥P
  let Y := H ⧸ pPrimeCore 2 H
  let π : H →* Y := QuotientGroup.mk' (pPrimeCore 2 H)
  let R' : Subgroup H := R.subgroupOf P
  have hR'2 : IsPGroup 2 R' :=
    (IsSylowTwoIn.isPGroup hR).of_equiv (Subgroup.subgroupOfEquivOfLe hR.1).symm
  let g : ↥R →* Y := π.comp (Subgroup.inclusion hR.1)
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have hx : (⟨x.1, hR.1 x.2⟩ : ↥P) ∈ R' := x.2
    have hy : (⟨y.1, hR.1 y.2⟩ : ↥P) ∈ R' := y.2
    have hxy' : π (⟨x.1, hR.1 x.2⟩ : ↥P) = π (⟨y.1, hR.1 y.2⟩ : ↥P) := hxy
    have heq := injOn_of_isPGroup hR'2 hx hy hxy'
    exact Subtype.ext (congrArg (fun z : ↥P => z.1) heq)
  obtain ⟨S, hS⟩ := hR.2
  let Rbar : Sylow 2 Y := S.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  have hRbar : (Rbar : Subgroup Y) = R'.map π := by
    rw [Sylow.coe_mapSurjective, hS]
  have hrange : g.range = (Rbar : Subgroup Y) := by
    rw [hRbar]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_map_of_mem π x.2
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.1, hp⟩, congrArg π (Subtype.ext rfl)⟩
  let e0 : ↥R ≃* ↥(Rbar : Subgroup Y) :=
    (MonoidHom.ofInjective hg_inj).trans (MulEquiv.subgroupCongr hrange)
  obtain ⟨eC⟩ : Nonempty (Y ≃* Blueprint.NativeSporadic.Carrier .ONan) := hON
  let eY : Y ≃* Pv := eC.trans onEquivPv
  let Sbar : Sylow 2 Pv := Sylow.mapSurjective (f := eY.toMonoidHom) eY.surjective Rbar
  have hSbar : (Sbar : Subgroup Pv) = (Rbar : Subgroup Y).map eY.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eY.toMonoidHom) eY.surjective Rbar
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Pv Sbar onTSylow
  let ψ : Y ≃* Pv := eY.trans (MulAut.conj c)
  have hmap_syl : (Rbar : Subgroup Y).map ψ.toMonoidHom = (onTSylow : Subgroup Pv) := by
    have hconj : (onTSylow : Subgroup Pv) =
        (Sbar : Subgroup Pv).map (MulAut.conj c).toMonoidHom := by
      have h := congrArg (fun S : Sylow 2 Pv => (S : Subgroup Pv)) hc
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
      convert h.symm using 2
      ext x
      rfl
    rw [hconj, hSbar, Subgroup.map_map]
    rfl
  have hmap_onTS : (Rbar : Subgroup Y).map ψ.toMonoidHom = onT.subgroupOf Pv := by
    rw [← onTSylow_coe]
    exact hmap_syl
  let e1 : ↥(Rbar : Subgroup Y) ≃* ↥onT :=
    ((Subgroup.equivMapOfInjective (Rbar : Subgroup Y) ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hmap_onTS)).trans
      (Subgroup.subgroupOfEquivOfLe onT_le)
  let e : ↥R ≃* ↥onT := e0.trans e1
  let ω0 : Subgroup ↥R := omSub (sqSub (⊤ : Subgroup ↥R))
  let ωT : Subgroup ↥onT := omSub (sqSub (⊤ : Subgroup ↥onT))
  have hω0map : ω0.map e.toMonoidHom = ωT := by
    show (omSub (sqSub (⊤ : Subgroup ↥R))).map e.toMonoidHom =
      omSub (sqSub (⊤ : Subgroup ↥onT))
    rw [omSub_map e.toMonoidHom e.injective, sqSub_map,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  have hsqT : sqSub (⊤ : Subgroup ↥onT) = sqT := by
    rw [sqSub, sqT]
    congr 1
    ext x
    simp
  have hωT : ωT = omegaT := by
    show omSub (sqSub (⊤ : Subgroup ↥onT)) = omegaT
    rw [hsqT]
    rfl
  let eω : ω0 ≃* omegaP :=
    (Subgroup.equivMapOfInjective ω0 e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hω0map).trans
        ((MulEquiv.subgroupCongr hωT).trans omegaPEquiv.symm))
  have hωR : ω0.map R.subtype = omSub (sqSub R) := by
    show (omSub (sqSub (⊤ : Subgroup ↥R))).map R.subtype = omSub (sqSub R)
    rw [omSub_map R.subtype R.subtype_injective, sqSub_map, Subgroup.map_top,
      Subgroup.range_subtype]
  let eR : ω0 ≃* omSub (sqSub R) :=
    (Subgroup.equivMapOfInjective ω0 R.subtype R.subtype_injective).trans
      (MulEquiv.subgroupCongr hωR)
  let E : omSub (sqSub R) ≃* omegaP := eR.symm.trans eω
  have : CFSG.IsElementaryAbelian 2 omegaP := omegaP_elementary
  have hωP : IsElemTwo omegaP := isElemTwo_of_isElementaryAbelian
  have hcardP : Nat.card omegaP = 8 := card_omegaP
  refine ⟨?_, ?_⟩
  · refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have heq : (⟨x * y, mul_mem hx hy⟩ : omSub (sqSub R)) =
          ⟨y * x, mul_mem hy hx⟩ := by
        apply E.injective
        change E ((⟨x, hx⟩ : omSub (sqSub R)) * ⟨y, hy⟩) =
          E ((⟨y, hy⟩ : omSub (sqSub R)) * ⟨x, hx⟩)
        rw [map_mul, map_mul]
        exact Subtype.ext (hωP.1 (E ⟨x, hx⟩) (E ⟨x, hx⟩).2 (E ⟨y, hy⟩) (E ⟨y, hy⟩).2)
      exact congrArg Subtype.val heq
    · have heq : (⟨x * x, mul_mem hx hx⟩ : omSub (sqSub R)) = 1 := by
        apply E.injective
        change E ((⟨x, hx⟩ : omSub (sqSub R)) * ⟨x, hx⟩) = E 1
        rw [map_mul, map_one]
        exact Subtype.ext (hωP.2 (E ⟨x, hx⟩) (E ⟨x, hx⟩).2)
      exact congrArg Subtype.val heq
  · rw [Nat.card_congr E.toEquiv, hcardP]

theorem exists_eight_normalizers_top_of_on
    {H : Type} [Group H] [Finite H]
    (hON : IsSporadic (H ⧸ pPrimeCore 2 H) .ONan) (R : Sylow 2 H) :
    ∃ F₀ F₁ : Subgroup H, F₀ ≤ R ∧ F₁ ≤ R ∧ IsElemTwo F₀ ∧ Nat.card F₀ = 8 ∧
      IsElemTwo F₁ ∧ Nat.card F₁ = 8 ∧
      (⊤ : Subgroup H) ≤ normalizer (F₀ : Set H) ⊔ normalizer (F₁ : Set H) ⊔ pPrimeCore 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y := H ⧸ pPrimeCore 2 H
  let π : H →* Y := QuotientGroup.mk' (pPrimeCore 2 H)
  let R' : Subgroup H := R
  have hR'2 : IsPGroup 2 R' := R.isPGroup'
  let Rbar : Sylow 2 Y := R.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  have hRbar : (Rbar : Subgroup Y) = R'.map π := Sylow.coe_mapSurjective _ _
  obtain ⟨Fbar0, Fbar1, hFbar0R, hFbar1R, hc0, hs0, h8_0, hc1, hs1, h8_1, hgen⟩ :=
    CFSG.ONSchreier.on_eight_normalizers hON Rbar
  let F0' : Subgroup H := R' ⊓ Fbar0.comap π
  let F1' : Subgroup H := R' ⊓ Fbar1.comap π
  have hF0'map : F0'.map π = Fbar0 := by
    show (R' ⊓ Fbar0.comap π).map π = Fbar0
    exact map_inf_comap_eq (by rwa [← hRbar])
  have hF1'map : F1'.map π = Fbar1 := by
    show (R' ⊓ Fbar1.comap π).map π = Fbar1
    exact map_inf_comap_eq (by rwa [← hRbar])
  have hF0'2 : IsPGroup 2 F0' := hR'2.to_le inf_le_left
  have hF1'2 : IsPGroup 2 F1' := hR'2.to_le inf_le_left
  have hcardF0' : Nat.card F0' = 8 := by
    have h := card_map_of_isPGroup (H := H) (E := F0') hF0'2
    rw [hF0'map, h8_0] at h
    exact h.symm
  have hcardF1' : Nat.card F1' = 8 := by
    have h := card_map_of_isPGroup (H := H) (E := F1') hF1'2
    rw [hF1'map, h8_1] at h
    exact h.symm
  have helemF0' : IsElemTwo F0' := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have hxR : x ∈ R' := (inf_le_left : F0' ≤ R') hx
      have hyR : y ∈ R' := (inf_le_left : F0' ≤ R') hy
      have hxbar : π x ∈ Fbar0 := by
        rw [← hF0'map]
        exact mem_map_of_mem π hx
      have hybar : π y ∈ Fbar0 := by
        rw [← hF0'map]
        exact mem_map_of_mem π hy
      exact injOn_of_isPGroup hR'2 (R'.mul_mem hxR hyR) (R'.mul_mem hyR hxR) (by
        rw [map_mul, map_mul]
        exact hc0 (π x) hxbar (π y) hybar)
    · have hxR : x ∈ R' := (inf_le_left : F0' ≤ R') hx
      have hxbar : π x ∈ Fbar0 := by
        rw [← hF0'map]
        exact mem_map_of_mem π hx
      exact injOn_of_isPGroup hR'2 (R'.mul_mem hxR hxR) R'.one_mem (by
        rw [map_mul, map_one]
        exact hs0 (π x) hxbar)
  have helemF1' : IsElemTwo F1' := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have hxR : x ∈ R' := (inf_le_left : F1' ≤ R') hx
      have hyR : y ∈ R' := (inf_le_left : F1' ≤ R') hy
      have hxbar : π x ∈ Fbar1 := by
        rw [← hF1'map]
        exact mem_map_of_mem π hx
      have hybar : π y ∈ Fbar1 := by
        rw [← hF1'map]
        exact mem_map_of_mem π hy
      exact injOn_of_isPGroup hR'2 (R'.mul_mem hxR hyR) (R'.mul_mem hyR hxR) (by
        rw [map_mul, map_mul]
        exact hc1 (π x) hxbar (π y) hybar)
    · have hxR : x ∈ R' := (inf_le_left : F1' ≤ R') hx
      have hxbar : π x ∈ Fbar1 := by
        rw [← hF1'map]
        exact mem_map_of_mem π hx
      exact injOn_of_isPGroup hR'2 (R'.mul_mem hxR hxR) R'.one_mem (by
        rw [map_mul, map_one]
        exact hs1 (π x) hxbar)
  have hN0 : normalizer (Fbar0 : Set Y) = (normalizer (F0' : Set H)).map π := by
    have h := normalizer_map_eq (H := H) (E := F0') hF0'2
    rwa [hF0'map] at h
  have hN1 : normalizer (Fbar1 : Set Y) = (normalizer (F1' : Set H)).map π := by
    have h := normalizer_map_eq (H := H) (E := F1') hF1'2
    rwa [hF1'map] at h
  have hjoin : (normalizer (F0' : Set H) ⊔ normalizer (F1' : Set H)).map π = ⊤ := by
    rw [Subgroup.map_sup, ← hN0, ← hN1, hgen]
  refine ⟨F0', F1', inf_le_left, inf_le_left, helemF0', hcardF0', helemF1', hcardF1', ?_⟩
  have h := congrArg (Subgroup.comap π) hjoin
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
  exact h.symm.le

theorem exists_eight_normalizers_of_on
    {P R : Subgroup G} (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan) (hR : IsSylowTwoIn R P) :
    ∃ F₀ F₁ : Subgroup G, F₀ ≤ R ∧ F₁ ≤ R ∧ IsElemTwo F₀ ∧ Nat.card F₀ = 8 ∧
      IsElemTwo F₁ ∧ Nat.card F₁ = 8 ∧
      P ≤ P ⊓ normalizer (F₀ : Set G) ⊔ P ⊓ normalizer (F₁ : Set G) ⊔ oddIn P := by
  classical
  obtain ⟨S, hS⟩ := hR.2
  obtain ⟨F0', F1', hF0S, hF1S, helemF0', hcardF0', helemF1', hcardF1', htop⟩ :=
    exists_eight_normalizers_top_of_on hON S
  let F0 : Subgroup G := F0'.map P.subtype
  let F1 : Subgroup G := F1'.map P.subtype
  have hSR : (S : Subgroup ↥P).map P.subtype = R := by
    rw [hS, Subgroup.subgroupOf_map_subtype, inf_of_le_left hR.1]
  have hF0R : F0 ≤ R := by
    rw [← hSR]
    exact Subgroup.map_mono hF0S
  have hF1R : F1 ≤ R := by
    rw [← hSR]
    exact Subgroup.map_mono hF1S
  have hcardF0 : Nat.card F0 = 8 := by
    show Nat.card (F0'.map P.subtype) = 8
    rw [Subgroup.card_map_of_injective P.subtype_injective, hcardF0']
  have hcardF1 : Nat.card F1 = 8 := by
    show Nat.card (F1'.map P.subtype) = 8
    rw [Subgroup.card_map_of_injective P.subtype_injective, hcardF1']
  have helemF0 : IsElemTwo F0 := isElemTwo_map P.subtype helemF0'
  have helemF1 : IsElemTwo F1 := isElemTwo_map P.subtype helemF1'
  refine ⟨F0, F1, hF0R, hF1R, helemF0, hcardF0, helemF1, hcardF1, ?_⟩
  have hN0G : (normalizer (F0' : Set ↥P)).map P.subtype ≤
      P ⊓ normalizer (F0 : Set G) :=
    le_inf (Subgroup.map_subtype_le _) (Subgroup.le_normalizer_map (f := P.subtype))
  have hN1G : (normalizer (F1' : Set ↥P)).map P.subtype ≤
      P ⊓ normalizer (F1 : Set G) :=
    le_inf (Subgroup.map_subtype_le _) (Subgroup.le_normalizer_map (f := P.subtype))
  have hle : (normalizer (F0' : Set ↥P) ⊔ normalizer (F1' : Set ↥P) ⊔
      pPrimeCore 2 ↥P).map P.subtype ≤
      P ⊓ normalizer (F0 : Set G) ⊔ P ⊓ normalizer (F1 : Set G) ⊔ oddIn P := by
    rw [Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le_sup (sup_le_sup hN0G hN1G) le_rfl
  calc P = (⊤ : Subgroup ↥P).map P.subtype := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
    _ ≤ (normalizer (F0' : Set ↥P) ⊔ normalizer (F1' : Set ↥P) ⊔
          pPrimeCore 2 ↥P).map P.subtype := Subgroup.map_mono htop
    _ ≤ _ := hle

private theorem exists_isSylowTwoIn_normalized_of_isPGroup {H X : Subgroup G}
    (hX : IsPGroup 2 X) (hXN : X ≤ normalizer (H : Set G)) :
    ∃ D : Subgroup G, IsSylowTwoIn D H ∧ X ≤ normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulDistribMulAction X H := Subgroup.conjMulDistribMulActionOfLeNormalizer X H hXN
  have hcard : ¬ 2 ∣ Nat.card (Sylow 2 H) := by
    intro h2
    have h1 : Nat.card (Sylow 2 H) % 2 = 1 % 2 := card_sylow_modEq_one 2 H
    omega
  obtain ⟨S, hS⟩ := hX.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 H) hcard
  refine ⟨(S : Subgroup H).map H.subtype, ⟨map_subtype_le _, S, by
    rw [subgroupOf_map_subtype_eq]⟩, fun a ha => mem_normalizer_iff.2 fun x => ?_⟩
  have hfix : (⟨a, ha⟩ : X) • (S : Subgroup H) = S := by
    rw [← Sylow.pointwise_smul_def]
    exact congrArg Sylow.toSubgroup (hS ⟨a, ha⟩)
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (⟨a, ha⟩ : X) • s ∈ (S : Subgroup H) :=
      hfix ▸ Subgroup.smul_mem_pointwise_smul s _ _ hs
    exact ⟨_, hs', rfl⟩
  · rintro ⟨s', hs', hs'x⟩
    rw [← hfix] at hs'
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hs'
    refine ⟨s, hs, ?_⟩
    have h1 : a * (s : G) * a⁻¹ = a * x * a⁻¹ := hs'x
    simpa using h1

omit [Finite G] in
private theorem mem_normalizer_wGroup_of_mem_normalizer {E : Subgroup G} {g : G}
    (hg : g ∈ normalizer (E : Set G)) : g ∈ normalizer (wGroup E : Set G) := by
  have hg' : E.map (MulAut.conj g).toMonoidHom = E := mem_normalizer_iff_map_conj_eq.mp hg
  have h1 : wGroup (E.map (MulAut.conj g).toMonoidHom) = wGroup E := by rw [hg']
  rw [wGroup_map_conj] at h1
  exact mem_normalizer_iff_map_conj_eq.mpr h1

omit [Finite G] in
theorem omSub_sqSub_le (R : Subgroup G) : omSub (sqSub R) ≤ R := by
  have h1 : omSub (sqSub R) ≤ sqSub R :=
    (Subgroup.closure_le (sqSub R)).mpr fun _ hx => hx.1
  have h2 : sqSub R ≤ R :=
    (Subgroup.closure_le R).mpr fun x ⟨t, ht, htx⟩ => htx ▸ R.pow_mem ht 2
  exact h1.trans h2

omit [Finite G] in
theorem mem_normalizer_omSub_sqSub {R : Subgroup G} {g : G} (hg : g ∈ normalizer (R : Set G)) :
    g ∈ normalizer (omSub (sqSub R) : Set G) := by
  have hR : R.map (MulAut.conj g) = R := mem_normalizer_iff_map_conj_eq.mp hg
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [omSub_map _ (MulAut.conj g).injective, sqSub_map, hR]

theorem exists_wGroup_of_eights_of_balanced
    {t : G} {P : Subgroup G}
    (hC : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemTwo E → TwoBalancedWrt E)
    (ht : orderOf t = 2) (hPt : P ≤ centralizer ({t} : Set G))
    (hCP : centralizer ({t} : Set G) ≤ normalizer (P : Set G))
    (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan)
    (hE8 : ∀ R : Subgroup G, IsSylowTwoIn R P →
      IsElemTwo (omSub (sqSub R)) ∧ Nat.card (omSub (sqSub R)) = 8)
    (hF1 : ∀ R : Subgroup G, IsSylowTwoIn R P → ∃ F₀ F₁ : Subgroup G, F₀ ≤ R ∧ F₁ ≤ R ∧
      IsElemTwo F₀ ∧ Nat.card F₀ = 8 ∧ IsElemTwo F₁ ∧ Nat.card F₁ = 8 ∧
      P ≤ P ⊓ normalizer (F₀ : Set G) ⊔ P ⊓ normalizer (F₁ : Set G) ⊔ oddIn P) :
    ∃ W : Subgroup G, Odd (Nat.card W) ∧ normalizer (P : Set G) ≤ normalizer (W : Set G) ∧
      ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemTwo E → 8 ≤ Nat.card E →
        wGroup E = W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R₀⟩ := Sylow.nonempty (p := 2) (G := ↥P)
  let R : Subgroup G := (R₀ : Subgroup ↥P).map P.subtype
  have hR : IsSylowTwoIn R P := ⟨map_subtype_le _, R₀, by rw [subgroupOf_map_subtype_eq]⟩
  have hR2 : IsPGroup 2 R := hR.isPGroup
  obtain ⟨hEe₀, hEcard₀⟩ := hE8 R hR
  set E : Subgroup G := omSub (sqSub R) with hEdef
  have hEe : IsElemTwo E := hEe₀
  have hEcard : Nat.card E = 8 := hEcard₀
  have hER : E ≤ R := omSub_sqSub_le R
  have hEP : E ≤ P := hER.trans hR.1
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hcommPt : ∀ p ∈ P, p * t = t * p := fun p hp =>
    mem_centralizer_singleton_iff.mp (hPt hp)
  have hRt : ∀ r ∈ R, r * t = t * r := fun r hr => hcommPt r (hR.1 hr)
  have hAt : IsElemTwo (E ⊔ zpowers t) ∧ Nat.card ↥(E ⊔ zpowers t) = 16 :=
    card_sup_zpowers_of_on ht hPt hON hEP hEe hEcard
  have htE : t ∉ E := by
    intro htE
    have hsup : E ⊔ zpowers t = E := sup_eq_left.mpr (zpowers_le.mpr htE)
    have h16 := hAt.2
    rw [hsup, hEcard] at h16
    omega
  have htC' : t ∈ centralizer (R : Set G) :=
    mem_centralizer_iff.mpr fun r hr => hRt r hr
  have htNR : t ∈ normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer (R : Set G) htC'
  have hzt2 : IsPGroup 2 ↥(zpowers t) :=
    (isElemTwo_zpowers htt).isPGroup
  have hztN : zpowers t ≤ normalizer (R : Set G) := zpowers_le.mpr htNR
  have hT2 : IsPGroup 2 ↥(R ⊔ zpowers t) := hR2.to_sup_of_normal_left' hzt2 hztN
  have hRN : R ≤ normalizer (E : Set G) := fun r hr =>
    mem_normalizer_omSub_sqSub (R.le_normalizer hr)
  have hEN : zpowers t ≤ normalizer (E : Set G) :=
    zpowers_le.mpr (mem_normalizer_omSub_sqSub htNR)
  have hTN : R ⊔ zpowers t ≤ normalizer (E : Set G) := sup_le hRN hEN
  have htT : t ∈ R ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hTc : R ⊔ zpowers t ≤ centralizer ({t} : Set G) := by
    refine sup_le ?_ ?_
    · intro r hr
      exact mem_centralizer_singleton_iff.mpr (hRt r hr)
    · intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact mem_centralizer_singleton_iff.mpr ((Commute.refl t).zpow_right k).eq.symm
  have hztC : zpowers t ≤ centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_centralizer_singleton_iff.mpr rfl
  have hAtC : E ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le (hEP.trans hPt) hztC
  have htc : ∀ y ∈ R ⊔ zpowers t, t * y = y * t := fun y hy =>
    (mem_centralizer_singleton_iff.mp (hTc hy)).symm
  have hconn : ∀ F : Subgroup G, F ≤ R ⊔ zpowers t → IsAbelianTwoOfRank 3 F →
      wGroup F = wGroup (E ⊔ zpowers t) := by
    intro F hFT hF
    exact wGroup_eq_of_abelianConnectedIn
      (S := R ⊔ zpowers t)
      (fun B hB hBe => hC B (hB.trans hTc) hBe)
      (abelianConnectedIn_of_normal_eight (E := E) (z := t) (A := F) hT2
        (hER.trans le_sup_left) hTN hEe hEcard htT htc htt htE hFT hF)
  have hWA : wGroup (E ⊔ zpowers t) = wGroup E := by
    exact wGroup_eq_of_le_eight_of_twoBalancedWrt (hC (E ⊔ zpowers t) hAtC hAt.1)
      hAt.1 (le_sup_left : E ≤ E ⊔ zpowers t) hEcard
  have hodd : Odd (Nat.card (wGroup (E ⊔ zpowers t))) := by
    rw [wGroup_eq_completion hAt.1]
    exact Nat.coprime_two_left.mp
      (CFSG.ClassicalInvolution.Balance.isComplete_deltaCore hAt.1.isElemAbelian (by omega)
        (hC (E ⊔ zpowers t) hAtC hAt.1)).1.1
  have hNR : normalizer (R : Set G) ≤ normalizer (wGroup (E ⊔ zpowers t) : Set G) := by
    intro g hg
    rw [hWA]
    exact mem_normalizer_wGroup_of_mem_normalizer (mem_normalizer_omSub_sqSub hg)
  obtain ⟨F₀, F₁, hF₀R, hF₁R, hF₀e, hF₀c, hF₁e, hF₁c, hgen⟩ := hF1 R hR
  have hF₀T : F₀ ≤ R ⊔ zpowers t := hF₀R.trans le_sup_left
  have hF₁T : F₁ ≤ R ⊔ zpowers t := hF₁R.trans le_sup_left
  have hF₀3 : IsAbelianTwoOfRank 3 F₀ := hF₀e.isAbelianTwoOfRank (by omega)
  have hF₁3 : IsAbelianTwoOfRank 3 F₁ := hF₁e.isAbelianTwoOfRank (by omega)
  have hNF₀ : wGroup F₀ = wGroup (E ⊔ zpowers t) := hconn F₀ hF₀T hF₀3
  have hNF₁ : wGroup F₁ = wGroup (E ⊔ zpowers t) := hconn F₁ hF₁T hF₁3
  have hN₀ : P ⊓ normalizer (F₀ : Set G) ≤
      normalizer (wGroup (E ⊔ zpowers t) : Set G) := by
    intro g hg
    rw [← hNF₀]
    exact mem_normalizer_wGroup_of_mem_normalizer hg.2
  have hN₁ : P ⊓ normalizer (F₁ : Set G) ≤
      normalizer (wGroup (E ⊔ zpowers t) : Set G) := by
    intro g hg
    rw [← hNF₁]
    exact mem_normalizer_wGroup_of_mem_normalizer hg.2
  have hoddP : oddIn P ≤ normalizer (wGroup (E ⊔ zpowers t) : Set G) :=
    oddIn_le_normalizer_wGroup_of_on_of_twoBalanced (hC (E ⊔ zpowers t) hAtC hAt.1)
      ht hPt hON hEP hEe hEcard
  have hPN : P ≤ normalizer (wGroup (E ⊔ zpowers t) : Set G) :=
    hgen.trans (sup_le (sup_le hN₀ hN₁) hoddP)
  have hPNP : normalizer (P : Set G) ≤ normalizer (wGroup (E ⊔ zpowers t) : Set G) := by
    intro g hg
    have hgP : R.map (MulAut.conj g).toMonoidHom ≤ P := by
      rintro _ ⟨r, hr, rfl⟩
      exact (mem_normalizer_iff.mp hg r).mp (hR.1 hr)
    obtain ⟨d, hdP, hd⟩ := hR.exists_conj_le hgP (hR2.map _)
    have hdg : R.map (MulAut.conj (d * g)).toMonoidHom = R := by
      have hcard : Nat.card ↥(R.map (MulAut.conj (d * g)).toMonoidHom) = Nat.card R :=
        card_map_of_injective (f := MulEquiv.toMonoidHom (MulAut.conj (d * g)))
          (MulAut.conj (d * g)).injective
      refine eq_of_le_of_card_ge ?_ (by omega)
      rintro _ ⟨r, hr, rfl⟩
      have h := hd _ ⟨r, hr, rfl⟩
      convert h using 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
      group
    have hmem : d * g ∈ normalizer (wGroup (E ⊔ zpowers t) : Set G) :=
      hNR (mem_normalizer_iff_map_conj_eq.mpr hdg)
    have hdmem : d ∈ normalizer (wGroup (E ⊔ zpowers t) : Set G) := hPN hdP
    have hgd : g = d⁻¹ * (d * g) := by group
    rw [hgd]
    exact mul_mem (inv_mem hdmem) hmem
  refine ⟨wGroup (E ⊔ zpowers t), hodd, hPNP, ?_⟩
  intro E' hE't hE'e hE'card
  have hE'e2 : IsElemTwo (E' ⊔ zpowers t) :=
    hE'e.sup (isElemTwo_zpowers htt) fun x hx y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hE't hx)) k).eq
  have htC : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hE'P : E' ⊔ zpowers t ≤ normalizer (P : Set G) :=
    sup_le (hE't.trans hCP) (zpowers_le.mpr (hCP htC))
  obtain ⟨D, hD, hE'D⟩ := exists_isSylowTwoIn_normalized_of_isPGroup hE'e2.isPGroup hE'P
  have hD2 : IsPGroup 2 D := hD.isPGroup
  obtain ⟨hEDe₀, hEDcard₀⟩ := hE8 D hD
  set E_D : Subgroup G := omSub (sqSub D) with hEDdef
  have hEDe : IsElemTwo E_D := hEDe₀
  have hEDcard : Nat.card E_D = 8 := hEDcard₀
  have hEDD : E_D ≤ D := omSub_sqSub_le D
  have hEDP : E_D ≤ P := hEDD.trans hD.1
  have hT'2 : IsPGroup 2 ↥(D ⊔ (E' ⊔ zpowers t)) := hD2.to_sup_of_normal_left' hE'e2.isPGroup hE'D
  have hDN : D ≤ normalizer (E_D : Set G) := fun d hd =>
    mem_normalizer_omSub_sqSub (D.le_normalizer hd)
  have hE'N : E' ⊔ zpowers t ≤ normalizer (E_D : Set G) := fun x hx =>
    mem_normalizer_omSub_sqSub (hE'D hx)
  have hT'N : D ⊔ (E' ⊔ zpowers t) ≤ normalizer (E_D : Set G) := sup_le hDN hE'N
  have htT' : t ∈ D ⊔ (E' ⊔ zpowers t) := mem_sup_right (mem_sup_right (mem_zpowers t))
  have hT'c : D ⊔ (E' ⊔ zpowers t) ≤ centralizer ({t} : Set G) := by
    refine sup_le ?_ ?_
    · intro y hy
      exact mem_centralizer_singleton_iff.mpr (hcommPt y (hD.1 hy))
    · refine sup_le ?_ ?_
      · intro y hy
        exact hE't hy
      · intro y hy
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        exact mem_centralizer_singleton_iff.mpr ((Commute.refl t).zpow_right k).eq.symm
  have htc' : ∀ y ∈ D ⊔ (E' ⊔ zpowers t), t * y = y * t := fun y hy =>
    (mem_centralizer_singleton_iff.mp (hT'c hy)).symm
  have hAED : IsElemTwo (E_D ⊔ zpowers t) ∧ Nat.card ↥(E_D ⊔ zpowers t) = 16 :=
    card_sup_zpowers_of_on ht hPt hON hEDP hEDe hEDcard
  have htED : t ∉ E_D := by
    intro htED
    have hsup : E_D ⊔ zpowers t = E_D := sup_eq_left.mpr (zpowers_le.mpr htED)
    have h16 := hAED.2
    rw [hsup, hEDcard] at h16
    omega
  have hconn' : ∀ F : Subgroup G, F ≤ D ⊔ (E' ⊔ zpowers t) → IsAbelianTwoOfRank 3 F →
      wGroup F = wGroup (E_D ⊔ zpowers t) := by
    intro F hFT hF
    exact wGroup_eq_of_abelianConnectedIn
      (S := D ⊔ (E' ⊔ zpowers t))
      (fun B hB hBe => hC B (hB.trans hT'c) hBe)
      (abelianConnectedIn_of_normal_eight (E := E_D) (z := t) (A := F) hT'2
        (hEDD.trans le_sup_left) hT'N hEDe hEDcard htT' htc' htt htED hFT hF)
  have h1 : wGroup E' = wGroup (E_D ⊔ zpowers t) :=
    hconn' E' (le_sup_left.trans le_sup_right) (hE'e.isAbelianTwoOfRank hE'card)
  have hAEDC : E_D ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le (hEDP.trans hPt) hztC
  have h2 : wGroup (E_D ⊔ zpowers t) = wGroup E_D :=
    wGroup_eq_of_le_eight_of_twoBalancedWrt (hC (E_D ⊔ zpowers t) hAEDC hAED.1)
      hAED.1 le_sup_left hEDcard
  obtain ⟨c, hcP, hcD⟩ := hR.exists_conj_le hD.1 hD.isPGroup
  have hcardD : Nat.card D = Nat.card R := by
    obtain ⟨hDP, Q', hQ'⟩ := hD
    obtain ⟨hRP, Q, hQ⟩ := hR
    calc Nat.card D = Nat.card ↥(D.subgroupOf P) :=
          (Nat.card_congr (subgroupOfEquivOfLe hDP).toEquiv).symm
      _ = Nat.card ↥(Q' : Subgroup ↥P) := by rw [hQ']
      _ = 2 ^ Nat.factorization (Nat.card ↥P) 2 := Sylow.card_eq_multiplicity Q'
      _ = Nat.card ↥(Q : Subgroup ↥P) := (Sylow.card_eq_multiplicity Q).symm
      _ = Nat.card ↥(R.subgroupOf P) := by rw [hQ]
      _ = Nat.card R := Nat.card_congr (subgroupOfEquivOfLe hRP).toEquiv
  have hDR : D.map (MulAut.conj c).toMonoidHom = R := by
    have hcard : Nat.card ↥(D.map (MulAut.conj c).toMonoidHom) = Nat.card D :=
      card_map_of_injective (f := MulEquiv.toMonoidHom (MulAut.conj c))
        (MulAut.conj c).injective
    refine eq_of_le_of_card_ge ?_ (by omega)
    rintro _ ⟨x, hx, rfl⟩
    exact hcD x hx
  have hEDmap : E_D.map (MulAut.conj c).toMonoidHom = E := by
    have hsq : (sqSub D).map (MulAut.conj c).toMonoidHom
        = sqSub (D.map (MulAut.conj c).toMonoidHom) := sqSub_map _ D
    rw [hEDdef, hEdef]
    calc (omSub (sqSub D)).map (MulAut.conj c).toMonoidHom
        = omSub ((sqSub D).map (MulAut.conj c).toMonoidHom) :=
        omSub_map _ (MulAut.conj c).injective _
      _ = omSub (sqSub (D.map (MulAut.conj c).toMonoidHom)) := by rw [hsq]
      _ = omSub (sqSub R) := by rw [hDR]
  have hWmap : (wGroup E_D).map (MulAut.conj c).toMonoidHom =
      wGroup (E ⊔ zpowers t) := by
    have hwit : wGroup (E_D.map (MulAut.conj c).toMonoidHom) =
        (wGroup E_D).map (MulAut.conj c).toMonoidHom :=
      wGroup_map_conj c E_D
    rw [← hwit, hEDmap, hWA]
  have hWc : (wGroup (E ⊔ zpowers t)).map (MulAut.conj c).toMonoidHom =
      wGroup (E ⊔ zpowers t) :=
    mem_normalizer_iff_map_conj_eq.mp (hPN hcP)
  have h3 : wGroup E_D = wGroup (E ⊔ zpowers t) :=
    Subgroup.map_injective (f := MulEquiv.toMonoidHom (MulAut.conj c))
      (MulAut.conj c).injective (hWmap.trans hWc.symm)
  exact h1.trans (h2.trans h3)

theorem exists_wGroup_of_on_of_balanced
    {t : G} {P : Subgroup G}
    (hC : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemTwo E → TwoBalancedWrt E)
    (ht : orderOf t = 2) (hPt : P ≤ centralizer ({t} : Set G))
    (hCP : centralizer ({t} : Set G) ≤ normalizer (P : Set G))
    (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan) :
    ∃ W : Subgroup G, Odd (Nat.card W) ∧ normalizer (P : Set G) ≤ normalizer (W : Set G) ∧
      ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemTwo E → 8 ≤ Nat.card E →
        wGroup E = W :=
  exists_wGroup_of_eights_of_balanced hC ht hPt hCP hON
    (fun _ hR => omSub_sqSub_of_on hON hR)
    (fun _ hR => exists_eight_normalizers_of_on hON hR)

theorem exists_wGroup_of_on
    (hGW : GWTwoBalanced G) {t : G} {P : Subgroup G}
    (ht : orderOf t = 2) (hPt : P ≤ centralizer ({t} : Set G))
    (hCP : centralizer ({t} : Set G) ≤ normalizer (P : Set G))
    (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan) :
    ∃ W : Subgroup G, Odd (Nat.card W) ∧ normalizer (P : Set G) ≤ normalizer (W : Set G) ∧
      ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemTwo E → 8 ≤ Nat.card E →
        wGroup E = W :=
  exists_wGroup_of_on_of_balanced
    (fun _ _ hE => twoBalancedWrt_of_gwTwoBalanced hGW hE) ht hPt hCP hON

end CFSG.ComponentClassification.GrSLit.L34Sec5S

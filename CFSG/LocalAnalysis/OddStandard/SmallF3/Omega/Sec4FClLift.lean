module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDSetting
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInner
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G Pr : Type} [Group G] [Group Pr] {L : Subgroup G} {s : G} {X : Subgroup Pr} [X.Normal]
  {y : Pr} {ρ : ↥L →* ↥X}

private theorem oddCentralCover_of_ker_le {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hsurj : Function.Surjective φ) {N : Subgroup A} (hker : φ.ker ≤ N) (hNc : N ≤ center A)
    (hNodd : Odd (Nat.card N)) : OddCentralCover φ :=
  ⟨hsurj, hker.trans hNc, hNodd.of_dvd_nat (Subgroup.card_dvd_of_le hker)⟩

private theorem isComponentIn_map_iff' {A M : Type} [Group A] [Group M] (f : A →* M)
    (hf : Function.Injective f) {K H : Subgroup A} :
    IsComponentIn (K.map f) (H.map f) ↔ IsComponentIn K H := by
  constructor
  · intro h
    have hle : K ≤ H := (Subgroup.map_le_map_iff_of_injective hf).mp h.1
    refine ⟨hle, ?_⟩
    let e : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
    have heq : (K.subgroupOf H).map e.toMonoidHom = (K.map f).subgroupOf (H.map f) := by
      apply Subgroup.map_injective (Subgroup.subtype_injective (H.map f))
      rw [Subgroup.map_map]
      have hcomp : ((H.map f).subtype).comp e.toMonoidHom = f.comp H.subtype := by
        ext m
        rfl
      rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hle,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono hle)]
    have h' : IsComponent ((K.subgroupOf H).map e.toMonoidHom) := by
      rw [heq]
      exact h.2
    have hc := CFSG.LocalCores.isComponent_map_mulEquiv e.symm h'
    have heq' : ((K.map f).subgroupOf (H.map f)).map e.symm.toMonoidHom = K.subgroupOf H := by
      rw [← heq, CFSG.LocalCores.map_map_symm]
    rw [heq] at hc
    rw [heq'] at hc
    exact hc
  · intro h
    refine ⟨Subgroup.map_mono h.1, ?_⟩
    let e : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
    have heq : (K.subgroupOf H).map e.toMonoidHom = (K.map f).subgroupOf (H.map f) := by
      apply Subgroup.map_injective (Subgroup.subtype_injective (H.map f))
      rw [Subgroup.map_map]
      have hcomp : ((H.map f).subtype).comp e.toMonoidHom = f.comp H.subtype := by
        ext m
        rfl
      rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h.1,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono h.1)]
    rw [← heq]
    exact CFSG.LocalCores.isComponent_map_mulEquiv e h.2

theorem sec4FCl_lift [Finite G] [Finite Pr] (h : Sec4FDCover L s X y ρ) {K : Subgroup Pr}
    {w : Pr} (hK : IsComponentIn K (X ⊓ centralizer ({y} : Set Pr))) (hoc : oddCore ↥K = ⊥)
    (hlie : LieModel ↥K .PSL 4 3 1) (hwX : w ∈ X) (hwy : w * y = y * w) (hww : w * w = 1)
    (hsup : X ⊓ centralizer ({y} : Set Pr) ≤ K ⊔ Subgroup.zpowers w) :
    ∃ (K' : Subgroup G) (v : G) (hvL : v ∈ L),
      IsComponentIn K' (L ⊓ centralizer ({s} : Set G)) ∧
      LieModel (↥K' ⧸ oddCore ↥K') .PSL 4 3 1 ∧ v * s = s * v ∧ v * v = 1 ∧
      ((ρ ⟨v, hvL⟩ : ↥X) : Pr) = w ∧
      L ⊓ centralizer ({s} : Set G) ≤ (K' ⊔ Subgroup.zpowers v) ⊔ ρ.ker.map L.subtype := by
  let Y : Subgroup G := L ⊓ centralizer ({s} : Set G)
  let Z : Subgroup Pr := X ⊓ centralizer ({y} : Set Pr)
  have hmemY : ∀ d : ↥Y, (d : G) ∈ L ∧ (d : G) * s = s * (d : G) := by
    intro d
    obtain ⟨hdL, hds⟩ := Subgroup.mem_inf.mp d.2
    exact ⟨hdL, Subgroup.mem_centralizer_singleton_iff.mp hds⟩
  let f : ↥Y →* ↥L := Y.subtype.codRestrict L (fun d => (hmemY d).1)
  have hf_inj : Function.Injective f := fun _ _ hab =>
    Subtype.ext (congrArg (fun x : ↥L => (x : G)) hab)
  let g : ↥Y →* ↥X := ρ.comp f
  have hg_coe : ∀ d : ↥Y,
      ((g d : ↥X) : Pr) = ((ρ ⟨(d : G), (hmemY d).1⟩ : ↥X) : Pr) := fun _ => rfl
  have hgZ : ∀ d : ↥Y, ((g d : ↥X) : Pr) ∈ Z := by
    intro d
    obtain ⟨hdL, hds⟩ := hmemY d
    exact Subgroup.mem_inf.mpr ⟨(g d).2, by
      rw [Subgroup.mem_centralizer_singleton_iff, hg_coe d]
      exact h.image_comm hdL hds⟩
  let ρY : ↥Y →* ↥Z := (X.subtype.comp g).codRestrict Z hgZ
  have hρY_coe : ∀ d : ↥Y, ((ρY d : ↥Z) : Pr) = ((g d : ↥X) : Pr) := fun _ => rfl
  have hsurj : Function.Surjective ρY := by
    intro z
    obtain ⟨hzX, hzy⟩ := Subgroup.mem_inf.mp z.2
    have hzy' : (z : Pr) * y = y * (z : Pr) :=
      Subgroup.mem_centralizer_singleton_iff.mp hzy
    obtain ⟨d, hdL, hds, hρd⟩ := h.exists_lift hzX hzy'
    have hdY : d ∈ Y := Subgroup.mem_inf.mpr
      ⟨hdL, Subgroup.mem_centralizer_singleton_iff.mpr hds⟩
    refine ⟨⟨d, hdY⟩, Subtype.ext ?_⟩
    show ((g ⟨d, hdY⟩ : ↥X) : Pr) = (z : Pr)
    rw [hg_coe]
    have hpir : ((ρ ⟨d, (hmemY ⟨d, hdY⟩).1⟩ : ↥X) : Pr) =
        ((ρ ⟨d, hdL⟩ : ↥X) : Pr) :=
      congrArg (fun x : ↥X => (x : Pr)) (congrArg (fun t : ↥L => ρ t) (Subtype.ext rfl))
    rw [hpir]
    exact hρd
  have hρY : OddCentralCover ρY := by
    refine oddCentralCover_of_ker_le ρY hsurj (N := (ρ.ker).comap f) ?_ ?_ ?_
    · intro n hn
      rw [Subgroup.mem_comap]
      have hgn : g n = 1 := by
        apply Subtype.ext
        have h1 : ((ρY n : ↥Z) : Pr) = 1 := by rw [hn]; rfl
        rwa [hρY_coe n] at h1
      exact MonoidHom.mem_ker.mpr hgn
    · intro n hn
      have hn' : f n ∈ ρ.ker := Subgroup.mem_comap.mp hn
      have hnc : f n ∈ center ↥L := h.cover.ker_le_center hn'
      rw [Subgroup.mem_center_iff]
      intro m
      apply hf_inj
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hnc (f m)
    · exact h.cover.odd_card_ker.of_dvd_nat
        (Subgroup.card_comap_dvd_of_injective (ρ.ker) f hf_inj)
  haveI : Finite ↥Y := Subtype.finite
  haveI : Finite ↥Z := Subtype.finite
  have htopZ : ((⊤ : Subgroup ↥Z).map Z.subtype) = Z := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hK₁ : IsComponentIn (K.subgroupOf Z) ⊤ := by
    refine (isComponentIn_map_iff' Z.subtype Z.subtype_injective).mp ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le hK.1, htopZ]
  have hoc₁ : oddCore ↥(K.subgroupOf Z) = ⊥ :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hK.1).symm hoc
  have htopZc : centralizer ({(1 : ↥Z)} : Set ↥Z) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.one_mem _
  have hKc : IsComponentIn (K.subgroupOf Z) (centralizer ({(ρY (1 : ↥Y))} : Set ↥Z)) := by
    rw [map_one, htopZc]
    exact hK₁
  have hXq : CFSG.IsQuasisimple ↥(K.subgroupOf Z) := hK₁.isQuasisimple
  let K₂ : Subgroup ↥Y := coverDerived ρY (K.subgroupOf Z)
  have htopYc : centralizer ({(1 : ↥Y)} : Set ↥Y) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.one_mem _
  have hK₂ : IsComponentIn K₂ ⊤ := by
    have hK₂c : IsComponentIn K₂ (centralizer ({(1 : ↥Y)} : Set ↥Y)) :=
      hρY.isComponentIn_coverDerived (w := (1 : ↥Y)) (one_mul 1) hKc
    rwa [htopYc] at hK₂c
  have hcov : OddCentralCover (coverDerivedHom ρY (K.subgroupOf Z)) :=
    hρY.oddCentralCover_coverDerivedHom hXq
  have hker : oddCore ↥K₂ = (coverDerivedHom ρY (K.subgroupOf Z)).ker :=
    hcov.oddCore_eq_ker hoc₁
  let e4 : ↥K₂ ⧸ oddCore ↥K₂ ≃* ↥(K.subgroupOf Z) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hcov.surjective)
  let K' : Subgroup G := K₂.map Y.subtype
  have htopY : ((⊤ : Subgroup ↥Y).map Y.subtype) = Y := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hK' : IsComponentIn K' Y := by
    have hm := isComponentIn_map_of_injective Y.subtype Y.subtype_injective hK₂
    rwa [htopY] at hm
  let e0 : ↥(K.subgroupOf Z) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK.1
  let e2 : ↥K₂ ≃* ↥K' := K₂.equivMapOfInjective Y.subtype Y.subtype_injective
  obtain ⟨e3⟩ := nonempty_quotient_oddCore_mulEquiv e2
  have hlie' : LieModel (↥K' ⧸ oddCore ↥K') .PSL 4 3 1 :=
    LieModel.of_mulEquiv ((e3.symm.trans e4).trans e0).symm hlie
  obtain ⟨v, hvL, hvs, hvv, hρv⟩ := h.exists_lift_invol hwX hwy hww
  let M : Subgroup G := (K' ⊔ Subgroup.zpowers v) ⊔ ρ.ker.map L.subtype
  let ML : Subgroup ↥L := M.comap L.subtype
  have hkerML : ρ.ker ≤ ML := by
    intro k hk
    show (k : G) ∈ M
    exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem L.subtype hk)
  have hvML : (⟨v, hvL⟩ : ↥L) ∈ ML := by
    show v ∈ M
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  have hfML : ∀ a : ↥K₂, f (a : ↥Y) ∈ ML := by
    intro a
    show ((f (a : ↥Y) : ↥L) : G) ∈ M
    rw [show ((f (a : ↥Y) : ↥L) : G) = ((a : ↥Y) : G) from rfl]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.mem_map_of_mem Y.subtype a.2))
  have hP' : K ≤ (ML.map ρ).map X.subtype := by
    intro k hk
    have hkZ : k ∈ Z := hK.1 hk
    have hkK : (⟨k, hkZ⟩ : ↥Z) ∈ K.subgroupOf Z := Subgroup.mem_subgroupOf.mpr hk
    obtain ⟨a, haK₂, haq⟩ := hρY.exists_mem_coverDerived hXq hkK
    have hfa : f (a : ↥Y) ∈ ML := hfML ⟨a, haK₂⟩
    have hval : ((ρ (f (a : ↥Y)) : ↥X) : Pr) = k := by
      have h1 : ((ρY (a : ↥Y) : ↥Z) : Pr) = k := congrArg Subtype.val haq
      have h2 : ((ρ (f (a : ↥Y)) : ↥X) : Pr) = ((ρY (a : ↥Y) : ↥Z) : Pr) := rfl
      rw [h2, h1]
    exact Subgroup.mem_map.mpr ⟨ρ (f (a : ↥Y)), Subgroup.mem_map_of_mem ρ hfa, hval⟩
  have hwP' : w ∈ (ML.map ρ).map X.subtype := by
    rw [← hρv]
    exact Subgroup.mem_map.mpr ⟨ρ ⟨v, hvL⟩, Subgroup.mem_map_of_mem ρ hvML, rfl⟩
  have hZP : Z ≤ (ML.map ρ).map X.subtype :=
    hsup.trans (sup_le hP' (Subgroup.zpowers_le.mpr hwP'))
  have hfin : Y ≤ M := by
    intro d hd
    have hdL : (d : G) ∈ L := (hmemY ⟨d, hd⟩).1
    have hds : (d : G) * s = s * (d : G) := (hmemY ⟨d, hd⟩).2
    have hdZ : ((ρ ⟨(d : G), hdL⟩ : ↥X) : Pr) ∈ Z := by
      refine Subgroup.mem_inf.mpr ⟨(ρ ⟨(d : G), hdL⟩).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.image_comm hdL hds
    have hdP : ((ρ ⟨(d : G), hdL⟩ : ↥X) : Pr) ∈ (ML.map ρ).map X.subtype := hZP hdZ
    obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hdP
    obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hu
    have hρm : ρ m = ρ ⟨(d : G), hdL⟩ := by
      apply Subtype.ext
      rw [hmeq]
      exact hueq
    have hdm : (⟨(d : G), hdL⟩ : ↥L) * m⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρm]
      group
    have hdML : (⟨(d : G), hdL⟩ : ↥L) ∈ ML := by
      have h1 : (⟨(d : G), hdL⟩ : ↥L) * m⁻¹ ∈ ML := hkerML hdm
      have h2 : ((⟨(d : G), hdL⟩ : ↥L) * m⁻¹) * m ∈ ML := ML.mul_mem h1 hm
      simpa using h2
    exact hdML
  exact ⟨K', v, hvL, hK', hlie', hvs, hvv, hρv, hfin⟩

end CFSG.OddStandard.SmallF3.Omega

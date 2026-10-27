module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParCA
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCMap
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTransLayerAux
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Goldschmidt.BasicG
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverActConv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate} {φ : ↥L →* omegaGroup hQ}

@[expose] noncomputable def om6par_embed (φ : ↥L →* omegaGroup hQ) : ↥L →* OGroup Q :=
  (omegaGroup hQ).subtype.comp φ

theorem om6par_embed_injective (hinj : Function.Injective φ) :
    Function.Injective (om6par_embed φ) :=
  Subtype.val_injective.comp hinj

theorem om6par_embed_range (hφ : Function.Surjective φ) :
    (om6par_embed φ).range = omegaGroup hQ := by
  rw [om6par_embed, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem om6par_pocket_map (hφ : Function.Surjective φ) (hinj : Function.Injective φ) {z : G}
    (hzL : z ∈ L) {K : Subgroup G} (hK : Sl23PocketIn L z K) :
    Sl23PocketIn (omegaGroup hQ) ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)
      ((K.subgroupOf L).map (om6par_embed φ)) := by
  have hKL : K ≤ L := hK.2.1.trans inf_le_left
  have h1 : Sl23PocketIn (⊤ : Subgroup ↥L) ⟨z, hzL⟩ (K.subgroupOf L) := by
    refine (sec63PC_sl23PocketIn_map_iff L.subtype L.subtype_injective).mp ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hKL, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hK
  have h2 := (sec63PC_sl23PocketIn_map_iff (om6par_embed φ) (om6par_embed_injective hinj)).mpr h1
  rwa [← MonoidHom.range_eq_map, om6par_embed_range hφ] at h2

theorem om6par_twoRes_map (hinj : Function.Injective φ) {z : G} (hzL : z ∈ L) {K : Subgroup G}
    (hK : K ≤ twoRes (L ⊓ centralizer ({z} : Set G))) :
    (K.subgroupOf L).map (om6par_embed φ) ≤ twoRes (omegaGroup hQ ⊓
      centralizer ({((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)} : Set (OGroup Q))) := by
  let A : Subgroup ↥L := (L ⊓ centralizer ({z} : Set G)).subgroupOf L
  have hKL : K ≤ L := hK.trans ((Subgroup.closure_le _).2 fun g hg => hg.1.1)
  have hA : A.map L.subtype = L ⊓ centralizer ({z} : Set G) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have h1 : K.subgroupOf L ≤ twoRes A := by
    rw [← Subgroup.map_le_map_iff_of_injective L.subtype_injective,
      ff_map_twoRes _ L.subtype_injective, hA, Subgroup.map_subgroupOf_eq_of_le hKL]
    exact hK
  have hle : A.map (om6par_embed φ) ≤ omegaGroup hQ ⊓
      centralizer ({((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)} : Set (OGroup Q)) := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨(φ l).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hc : l * ⟨z, hzL⟩ = (⟨z, hzL⟩ : ↥L) * l :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hl).2)
    show om6par_embed φ l * om6par_embed φ ⟨z, hzL⟩ = om6par_embed φ ⟨z, hzL⟩ * om6par_embed φ l
    rw [← map_mul, ← map_mul, hc]
  refine (Subgroup.map_mono h1).trans ?_
  rw [ff_map_twoRes _ (om6par_embed_injective hinj)]
  exact (Subgroup.closure_le _).2 fun g hg => Subgroup.subset_closure ⟨hle hg.1, hg.2⟩

theorem om6par_iso_of_eq (hinj : Function.Injective φ) {K : Subgroup G} (hKL : K ≤ L)
    {P : Subgroup (OGroup Q)} (h : (K.subgroupOf L).map (om6par_embed φ) = P)
    (hP : Nonempty (↥P ≃* SL23)) : Nonempty (↥K ≃* SL23) :=
  hP.map fun e => (Subgroup.subgroupOfEquivOfLe hKL).symm.trans
    ((Subgroup.equivMapOfInjective _ _ (om6par_embed_injective hinj)).trans
      ((MulEquiv.subgroupCongr h).trans e))

theorem om6par_conj_mem {K : Subgroup G} {g : G} (h : CFSG.conjugate K g = K) {x : G} :
    g⁻¹ * x * g ∈ K ↔ x ∈ K := by
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    have : a = x := by simpa [MulAut.conj_apply] using hax
    rwa [← this]
  · intro hx
    rw [← h]
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem om6par_mem_twoCoreIn_iff {K : Subgroup G} (e : ↥K ≃* SL23) {x : G} (hx : x ∈ K) :
    x ∈ twoCoreIn K ↔ x ^ 4 = 1 := by
  have h1 : (⟨x, hx⟩ : ↥K) ∈ CFSG.pCore 2 ↥K ↔ e ⟨x, hx⟩ ∈ CFSG.pCore 2 SL23 := by
    rw [← CFSG.pCore_map_iso 2 e, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [mem_twoCoreIn_iff_pCore hx, h1, sl23_pCore_eq_Q8, mem_sl23Q8, ← map_pow, ← map_one e,
    e.injective.eq_iff]
  constructor
  · intro h
    simpa using congrArg Subtype.val h
  · intro h
    exact Subtype.ext (by simpa using h)

theorem om6par_conj_formula {g : G} {x : simGroup Q} (hx : CoverAct L φ g x) (l : ↥L) :
    ∃ m : ↥L, (m : G) = g⁻¹ * (l : G) * g * (l : G)⁻¹ ∧
      om6par_embed φ m = simAct Q x⁻¹ (om6par_embed φ l) * (om6par_embed φ l)⁻¹ := by
  have hx' := om6par_coverAct_inv hx
  let l' : ↥L := ⟨g⁻¹ * (l : G) * (g⁻¹)⁻¹, (Subgroup.mem_normalizer_iff.mp hx'.1 (l : G)).mp l.2⟩
  refine ⟨l' * l⁻¹, by simp [l'], ?_⟩
  rw [map_mul, map_inv]
  exact congrArg (· * (om6par_embed φ l)⁻¹) (hx'.2 l l' rfl)

theorem om6par_outer_iff (hinj : Function.Injective φ) {K : Subgroup G} (hKL : K ≤ L)
    (he : Nonempty (↥K ≃* SL23)) {g : G} {x : simGroup Q} (hx : CoverAct L φ g x)
    (hgK : CFSG.conjugate K g = K) {P : Subgroup (OGroup Q)}
    (hP : (K.subgroupOf L).map (om6par_embed φ) = P) :
    (∃ k ∈ K, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn K) ↔
      ∃ u ∈ P, ¬ (simAct Q x⁻¹ u * u⁻¹) ^ 4 = 1 := by
  subst hP
  obtain ⟨e⟩ := he
  have key : ∀ l : ↥L, (l : G) ∈ K → ∀ m : ↥L, (m : G) = g⁻¹ * (l : G) * g * (l : G)⁻¹ →
      ((m : G) ∈ twoCoreIn K ↔ om6par_embed φ m ^ 4 = 1) := by
    intro l hl m hm
    have hmK : (m : G) ∈ K := by
      rw [hm]
      exact K.mul_mem ((om6par_conj_mem hgK).mpr hl) (K.inv_mem hl)
    rw [om6par_mem_twoCoreIn_iff e hmK, ← map_pow, ← map_one (om6par_embed φ),
      (om6par_embed_injective hinj).eq_iff, Subtype.ext_iff]
    simp
  constructor
  · rintro ⟨k, hk, hnot⟩
    obtain ⟨m, hm, hfm⟩ := om6par_conj_formula hx ⟨k, hKL hk⟩
    refine ⟨om6par_embed φ ⟨k, hKL hk⟩, ⟨_, hk, rfl⟩, ?_⟩
    rw [← hfm, ← key ⟨k, hKL hk⟩ hk m hm, hm]
    exact hnot
  · rintro ⟨_, ⟨l, hl, rfl⟩, hnot⟩
    obtain ⟨m, hm, hfm⟩ := om6par_conj_formula hx l
    refine ⟨l, hl, fun hmem => hnot ?_⟩
    rw [← hfm, ← key l hl m hm, hm]
    exact hmem

theorem om6par_map_mem {K : Subgroup G} {g : G} {x : simGroup Q} (hx : CoverAct L φ g x)
    (hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K) {u : OGroup Q}
    (hu : u ∈ (K.subgroupOf L).map (om6par_embed φ)) :
    simAct Q x u ∈ (K.subgroupOf L).map (om6par_embed φ) := by
  obtain ⟨l, hl, rfl⟩ := hu
  exact ⟨⟨g * (l : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hx.1 (l : G)).mp l.2⟩,
    hgK _ hl, hx.2 l _ rfl⟩

theorem om6par_normalized {K : Subgroup G} {g : G} {x : simGroup Q} (hx : CoverAct L φ g x)
    (hgK : CFSG.conjugate K g = K) {P : Subgroup (OGroup Q)}
    (hP : (K.subgroupOf L).map (om6par_embed φ) = P) (u : OGroup Q) :
    simAct Q x u ∈ P ↔ u ∈ P := by
  subst hP
  refine ⟨fun h => ?_, om6par_map_mem hx fun k hk => (om6par_conj_mem hgK).mp (by
    rwa [show g⁻¹ * (g * k * g⁻¹) * g = k by group])⟩
  have h' := om6par_map_mem (om6par_coverAct_inv hx) (fun k hk => by
    rw [inv_inv]
    exact (om6par_conj_mem hgK).mpr hk) h
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h'

theorem om6par_fix {K : Subgroup G} {y : G} {x : simGroup Q} (hx : CoverAct L φ y x)
    (hK : K ≤ centralizer ({y} : Set G)) {P : Subgroup (OGroup Q)}
    (hP : (K.subgroupOf L).map (om6par_embed φ) = P) : ∀ u ∈ P, simAct Q x u = u := by
  subst hP
  rintro _ ⟨l, hl, rfl⟩
  exact t5_cent_map_mem hx (Subgroup.mem_centralizer_singleton_iff.mp (hK hl)).symm

theorem om6par_fix_sup {x : simGroup Q} {P₁ P₂ : Subgroup (OGroup Q)}
    (h₁ : ∀ u ∈ P₁, simAct Q x u = u) (h₂ : ∀ u ∈ P₂, simAct Q x u = u) :
    ∀ u ∈ P₁ ⊔ P₂, simAct Q x u = u := fun u hu =>
  mem_fixSub_iff.mp ((sup_le (fun v hv => mem_fixSub_iff.mpr (h₁ v hv))
    (fun v hv => mem_fixSub_iff.mpr (h₂ v hv)) : P₁ ⊔ P₂ ≤ fixSub (simAct Q x)) hu)

theorem om6par_cent_comm (hφ : Function.Surjective φ) (hinj : Function.Injective φ)
    (h3 : 3 ≤ Module.finrank (ZMod 3) V) {e g y : G} {xe xg xy : simGroup Q}
    (he : CoverAct L φ e xe) (hg : CoverAct L φ g xg) (hy : CoverAct L φ y xy) :
    e⁻¹ * (g⁻¹ * y * g) ∈ centralizer (L : Set G) ↔ xe⁻¹ * (xg⁻¹ * xy * xg) ∈ piSim Q :=
  om6par_cent_iff hφ hinj h3 (om6par_coverAct_mul (om6par_coverAct_inv he)
    (om6par_coverAct_mul (om6par_coverAct_mul (om6par_coverAct_inv hg) hy) hg))

end CFSG.OddStandard.SmallF3.Omega

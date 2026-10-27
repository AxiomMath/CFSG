module

public import CFSG.GF2Type.Smith1980Orth.S3Bad
import CFSG.GF2Type.Smith1980Orth.S3Count
import CFSG.GF2Type.Smith1980Orth.S3CaseB
import CFSG.GF2Type.Smith1980Orth.S3ThmALin
import CFSG.LargeExtraspecial.S14SMKDeltaLin
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.Fischer.NoF25.Local
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.PSL10Fix
public import CFSG.LargeExtraspecial.S12InspUse
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.LargeExtraspecial.S14SMFMain
public import CFSG.LargeExtraspecial.S14W4LocCase
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocLeaf
public import CFSG.LargeExtraspecial.S3cOddCore
public import CFSG.LargeExtraspecial.S3cSix
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S9GenA
public import CFSG.LargeExtraspecial.S9GenG
public import CFSG.LargeExtraspecial.S9PD
public import CFSG.LargeExtraspecial.S9RBQOdd
public import CFSG.LargeExtraspecial.S9TwoB
public import CFSG.LargeExtraspecial.S9TwoN
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.Open.QuasithinDefs
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.RankThree.Literature.FSmith (zmod2_cases)
open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

namespace CaseII

section LinAlg

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem exists_sub_one {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] M) : ∃ N : M →ₗ[ZMod 2] M, ∀ u, N u = e u - u :=
  ⟨(e : M →ₗ[ZMod 2] M) - 1, fun u => by
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]⟩

private theorem finrank_map_le_add_one [FiniteDimensional (ZMod 2) V] (f : V →ₗ[ZMod 2] V)
    {W W' : Submodule (ZMod 2) V} (hW : W ≤ W')
    (hdim : finrank (ZMod 2) W' ≤ finrank (ZMod 2) W + 1) :
    finrank (ZMod 2) (W'.map f) ≤ finrank (ZMod 2) (W.map f) + 1 := by
  have h1 := S14.SMK.finrank_map_add_finrank_inf_ker f W
  have h2 := S14.SMK.finrank_map_add_finrank_inf_ker f W'
  have h3 : finrank (ZMod 2) (W ⊓ LinearMap.ker f : Submodule (ZMod 2) V) ≤
      finrank (ZMod 2) (W' ⊓ LinearMap.ker f : Submodule (ZMod 2) V) :=
    Submodule.finrank_mono (inf_le_inf_right _ hW)
  omega

end LinAlg

end CaseII

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private instance instFiniteDimensionalVtCaseII (g : G) (t : S.O) :
    FiniteDimensional (ZMod 2) (Vt S g t) :=
  Module.Finite.of_finite

private theorem Lbar_apply_sub_mem {k : G} {y : S.O} (hy : y ∈ S.Lbar k) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G))) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub (S.QG ⊓ S.Qa k) := by
  obtain ⟨⟨g, hgM⟩, hgL, rfl⟩ := hy
  obtain ⟨u, hu, huQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.ρ_cl ⟨g, hgM⟩ huQ]
  have hc := S14.SMK.commutator_mem_Dl S (mem_subgroupOf.mp hgL) hu
  have := S.cl_mem_clSub hc hc.1
  rwa [S.cl_commutator hgM huQ, S.ρ_cl ⟨g, hgM⟩ huQ] at this

private theorem commute_of_cl_mem_commQt {x u : G} (hxM : x ∈ S.M) (hx2 : x ^ 2 = 1)
    (hq : ∀ v ∈ S.commQt x, S.q v = 0) (hu : u ∈ S.QG) (hv : S.cl u ∈ S.commQt x) :
    u * x = x * u := by
  have hxx : x * x = 1 := by rw [← pow_two, hx2]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  obtain ⟨y, hy, hcl⟩ := (S.mem_commQt_iff hxM).mp hv
  have hcQ := S.commutator_mem_QG hxM hy
  have hc2 : (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 :=
    (S.q_cl_eq_zero_iff hcQ).mp (hq _ ((S.mem_commQt_iff hxM).mpr ⟨y, hy, rfl⟩))
  have hinv : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
    have e1 : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ = (x * x) * y * x⁻¹ * y⁻¹ * x⁻¹ := by group
    have e2 : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    rw [e1, e2, hxx, one_mul, hxi]
  have hinv2 : (x * y * x⁻¹ * y⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hc2)
  have hcomm : x * y * x⁻¹ * y⁻¹ * x = x * (x * y * x⁻¹ * y⁻¹) := by
    calc x * y * x⁻¹ * y⁻¹ * x = x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ * x := by
          rw [hinv, hinv2]
      _ = x * (x * y * x⁻¹ * y⁻¹) := by group
  rcases (S.cl_eq_cl_iff hcQ hu).mp hcl with h | h
  · rw [h]
    exact hcomm
  · rw [h]
    calc x * y * x⁻¹ * y⁻¹ * S.z * x = x * y * x⁻¹ * y⁻¹ * (S.z * x) := by group
      _ = x * y * x⁻¹ * y⁻¹ * (x * S.z) := by rw [S.z_comm hxM]
      _ = (x * y * x⁻¹ * y⁻¹ * x) * S.z := by group
      _ = x * (x * y * x⁻¹ * y⁻¹) * S.z := by rw [hcomm]
      _ = x * (x * y * x⁻¹ * y⁻¹ * S.z) := by group

private theorem Lbar_apply_eq_of_mem_commQt {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M)
    (hx2 : (k * S.z * k⁻¹) ^ 2 = 1) (hq : ∀ v ∈ S.commQt (k * S.z * k⁻¹), S.q v = 0)
    (hJ : ∀ d ∈ S.QG ⊓ S.Qa k, d ∈ S.clPre (S.commQt (k * S.z * k⁻¹)) → d = 1)
    {y : S.O} (hy : y ∈ S.Lbar k) {v : S.Qt} (hv : v ∈ S.commQt (k * S.z * k⁻¹)) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have hxy := S14.SMK.commute_of_mem_Lbar S hxM hy
  obtain ⟨⟨g, hgM⟩, hgL, rfl⟩ := hy
  obtain ⟨u, huQ, rfl⟩ := S.exists_cl v
  have huC : u ∈ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G) :=
    ⟨huQ, mem_centralizer_singleton_iff.mpr (commute_of_cl_mem_commQt hxM hx2 hq huQ hv)⟩
  have hc := S14.SMK.commutator_mem_Dl S (mem_subgroupOf.mp hgL) huC
  have hcl := S.cl_commutator hgM huQ
  have hinv : (S.ρ ⟨g, hgM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) ∈ S.commQt (k * S.z * k⁻¹) := by
    rw [S.commQt_of_mem hxM] at hv ⊢
    exact S7.apply_mem_commSpace_of_comm hxy hv
  have hmem : g * u * g⁻¹ * u⁻¹ ∈ S.clPre (S.commQt (k * S.z * k⁻¹)) :=
    ⟨hc.1, by rw [hcl]; exact Submodule.sub_mem _ hinv hv⟩
  rw [hJ _ hc hmem, S.cl_one] at hcl
  exact sub_eq_zero.mp hcl.symm

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

local notation "ρV" => D.resC

private noncomputable def cs (A : Submodule (ZMod 2) (Vt S D.g D.t)) : Submodule (ZMod 2) S.Qt :=
  LinearMap.range ((D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt).comp
    (LinearMap.prodMap A.subtype A.subtype))

private theorem mem_cs {A : Submodule (ZMod 2) (Vt S D.g D.t)} {x : S.Qt} :
    x ∈ D.cs A ↔ ∃ u ∈ A, ∃ w ∈ A, x = D.coord (u, w) := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨a.1, a.2, b.1, b.2, rfl⟩
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩

private theorem coord_mem_cs {A : Submodule (ZMod 2) (Vt S D.g D.t)} {u w : Vt S D.g D.t} :
    D.coord (u, w) ∈ D.cs A ↔ u ∈ A ∧ w ∈ A := by
  rw [D.mem_cs]
  constructor
  · rintro ⟨u', hu, w', hw, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.coord.injective h)
    exact ⟨hu, hw⟩
  · rintro ⟨hu, hw⟩
    exact ⟨u, hu, w, hw, rfl⟩

private theorem finrank_cs (A : Submodule (ZMod 2) (Vt S D.g D.t)) :
    finrank (ZMod 2) (D.cs A) = 2 * finrank (ZMod 2) A := by
  have hinj : Function.Injective ((D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt).comp
      (LinearMap.prodMap A.subtype A.subtype)) := by
    intro a b hab
    have h1 := D.coord.injective hab
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h1)) (Subtype.ext (congrArg Prod.snd h1))
  rw [cs, LinearMap.finrank_range_of_inj hinj, Module.finrank_prod]
  ring

private theorem coord_sub_coord (u w u' w' : Vt S D.g D.t) :
    D.coord (u, w) - D.coord (u', w') = D.coord (u - u', w - w') := by
  rw [← map_sub]
  rfl

private theorem coord_add_coord (a b a' b' : Vt S D.g D.t) :
    D.coord (a, b) + D.coord (a', b') = D.coord (a + a', b + b') := by
  rw [← map_add]
  rfl

private theorem coord_zero_zero : D.coord (0, 0) = 0 := by
  rw [Prod.mk_zero_zero]
  exact D.coord.map_zero

private theorem commSpace_Cbar_eq_cs (c : D.Cbar) :
    commSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = D.cs (commSpace (ρV c)) := by
  refine Submodule.ext fun x => ?_
  constructor
  · intro hx
    obtain ⟨u, v, hu, hv, h⟩ := (D.mem_commSpace_Cbar_iff_coord c).mp hx
    exact D.mem_cs.mpr ⟨u, hu, v, hv, h⟩
  · intro hx
    obtain ⟨u, hu, v, hv, h⟩ := D.mem_cs.mp hx
    exact (D.mem_commSpace_Cbar_iff_coord c).mpr ⟨u, v, hu, hv, h⟩

private theorem fixSpace_Cbar_eq_cs (c : D.Cbar) :
    fixSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = D.cs (fixSpace (ρV c)) := by
  refine Submodule.ext fun x => ?_
  obtain ⟨⟨u, w⟩, rfl⟩ := D.coord.surjective x
  constructor
  · intro h
    have h1 := Prod.mk.inj (D.coord.injective
      ((D.Cbar_apply_coord c u w).symm.trans (mem_fixSpace.mp h)))
    exact D.coord_mem_cs.mpr ⟨mem_fixSpace.mpr h1.1, mem_fixSpace.mpr h1.2⟩
  · intro h
    obtain ⟨h1, h2⟩ := D.coord_mem_cs.mp h
    exact mem_fixSpace.mpr ((D.Cbar_apply_coord c u w).trans
      (congrArg D.coord (Prod.ext (mem_fixSpace.mp h1) (mem_fixSpace.mp h2))))

private theorem Cbar_apply_coord_left (c : D.Cbar) (u : Vt S D.g D.t) :
    ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, 0)) = D.coord (ρV c u, 0) := by
  have := D.Cbar_apply_coord c u 0
  rwa [map_zero] at this

private theorem Cbar_apply_coord_right (c : D.Cbar) (u : Vt S D.g D.t) :
    ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, u)) = D.coord (0, ρV c u) := by
  have := D.Cbar_apply_coord c 0 u
  rwa [map_zero] at this

private theorem resC_mul_self {c : D.Cbar} (hcc : (c : S.O) * c = 1) :
    ρV c * ρV c = 1 :=
  ((map_mul (ρV) c c).symm.trans (congrArg (ρV) (Subtype.ext hcc : c * c = 1))).trans (map_one _)

private theorem polar_eq_zero_of_mem_commSpace {c : D.Cbar} (hcc : (c : S.O) * c = 1)
    {a b : Vt S D.g D.t} (ha : a ∈ commSpace (ρV c)) (hb : b ∈ commSpace (ρV c)) :
    polar D.QV a b = 0 :=
  polar_commSpace_eq_zero (D.resC_mem_orthogonalGroup c) (D.resC_mul_self hcc) ha hb

private theorem fixSpace_eq_orthogonal {c : D.Cbar} (hcc : (c : S.O) * c = 1) :
    fixSpace (ρV c) = LinearMap.BilinForm.orthogonal D.QV.polarBilin (commSpace (ρV c)) :=
  fixSpace_eq_orthogonal_commSpace D.QV_nondegenerate (D.resC_mem_orthogonalGroup c)
    (D.resC_mul_self hcc)

private theorem polar_eq_zero_of_mem_fixSpace {c : D.Cbar} (hcc : (c : S.O) * c = 1)
    {p a : Vt S D.g D.t} (hp : p ∈ commSpace (ρV c)) (ha : a ∈ fixSpace (ρV c)) :
    polar D.QV p a = 0 := by
  have h := ((congrArg (a ∈ ·) (D.fixSpace_eq_orthogonal hcc)).mp ha) p hp
  rwa [polarBilin_apply_apply] at h

private theorem orthogonal_fixSpace_le {c : D.Cbar} (hcc : (c : S.O) * c = 1) :
    LinearMap.BilinForm.orthogonal D.QV.polarBilin (fixSpace (ρV c)) ≤ fixSpace (ρV c) :=
  (congrArg (LinearMap.BilinForm.orthogonal D.QV.polarBilin (fixSpace (ρV c)) ≤ ·)
    (D.fixSpace_eq_orthogonal hcc)).mpr
    (LinearMap.BilinForm.orthogonal_le (B := D.QV.polarBilin)
      (commSpace_le_fixSpace (D.resC_mul_self hcc)))

private theorem exists_mem_fixSpace_not_mem_span {c : D.Cbar} (hcc : (c : S.O) * c = 1)
    (p : Vt S D.g D.t) : ∃ a ∈ fixSpace (ρV c), a ∉ (ZMod 2) ∙ p := by
  by_contra hno
  push Not at hno
  have hle : fixSpace (ρV c) ≤ (ZMod 2) ∙ p := fun a ha => hno a ha
  have h1 : finrank (ZMod 2) (fixSpace (ρV c)) ≤ 1 := by
    refine (Submodule.finrank_mono hle).trans ?_
    by_cases hp : p = 0
    · rw [hp, Submodule.span_zero_singleton, finrank_bot]
      exact Nat.zero_le _
    · rw [finrank_span_singleton hp]
  have h2 : 2 * finrank (ZMod 2) (commSpace (ρV c)) ≤ S.width :=
    (two_mul_finrank_commSpace_le (D.resC_mul_self hcc)).trans D.finrank_Vt.le
  have h3 : finrank (ZMod 2) (commSpace (ρV c)) + finrank (ZMod 2) (fixSpace (ρV c)) =
      S.width := (finrank_commSpace_add_finrank_fixSpace (ρV c)).trans D.finrank_Vt
  have := D.four_le
  omega

private theorem eq_one_of_sub_mem_cs {s : S.O} (hs : s ∈ D.Obar ⊔ zpowers D.t)
    {a b : Vt S D.g D.t} {L : Submodule (ZMod 2) (Vt S D.g D.t)} (haL : a ∉ L)
    (h1 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (b, 0)) - D.coord (a, 0) ∈ D.cs L)
    (h2 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, b)) - D.coord (0, a) ∈ D.cs L) : s = 1 := by
  have key : ∀ {u : Vt S D.g D.t}, u ∈ L → u - a ∈ L → a ∈ L := fun hu hua => by
    have := L.sub_mem hu hua
    rwa [sub_sub_cancel] at this
  rcases D.mem_sup_cases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    simp only [D.k_apply_coord, add_zero] at h1
    rw [D.coord_sub_coord, D.coord_mem_cs] at h1
    apply haL
    have := h1.1
    rwa [zero_sub, neg_mem_iff] at this
  · exfalso
    simp only [coe_mul_apply, D.k_apply_coord, add_zero, zero_add] at h1
    rw [D.coord_sub_coord, D.coord_mem_cs] at h1
    exact haL (key (by simpa using h1.2) h1.1)
  · exfalso
    simp only [D.t_apply_coord, zero_add] at h2
    rw [D.coord_sub_coord, D.coord_mem_cs] at h2
    exact haL (key (by simpa using h2.1) h2.2)
  · exfalso
    simp only [coe_mul_apply, D.t_apply_coord, D.k_apply_coord, add_zero] at h1
    rw [D.coord_sub_coord, D.coord_mem_cs] at h1
    apply haL
    have := h1.1
    rwa [zero_sub, neg_mem_iff] at this
  · exfalso
    simp only [coe_mul_apply, D.t_apply_coord, D.k_apply_coord, add_zero, zero_add] at h1
    rw [D.coord_sub_coord, D.coord_mem_cs] at h1
    exact haL (key (by simpa using h1.2) h1.1)

private theorem mem_Cbar_and_fix {y : S.O} (hy : y ∈ S.Mbar) {c : D.Cbar}
    (hcc : (c : S.O) * c = 1) {p : Vt S D.g D.t} (hpP : p ∈ commSpace (ρV c))
    (hp : p = 0 ∨ D.QV p = 1)
    (hy' : ∀ v ∈ fixSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ D.cs ((ZMod 2) ∙ p)) :
    ∃ hyC : y ∈ D.Cbar, ∀ v ∈ fixSpace (ρV c), ρV ⟨y, hyC⟩ v = v := by
  refine (D.exists_mem_fixSpace_not_mem_span hcc p).elim fun a ha => ?_
  have hρ2 : ρV c * ρV c = 1 := LinearEquiv.ext fun w => D.resC_resC_apply hcc w
  have haC : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt) = (a : S.Qt) := by
    rw [← D.coe_resC_apply c a]
    exact congrArg Subtype.val (mem_fixSpace.mp ha.1)
  have hck : (c : S.O) * D.k = D.k * (c : S.O) :=
    (mem_centralizer_iff.mp c.2.2 D.k (Subgroup.mem_sup_left D.k_mem_Obar)).symm
  have hkaC : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt)) =
      (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt) := by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hck, Subgroup.coe_mul,
      LinearEquiv.mul_apply, haC]
  have hcs_le : ∀ p' : Vt S D.g D.t, D.cs ((ZMod 2) ∙ p') ≤
      Submodule.span (ZMod 2)
        ({(p' : S.Qt), (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p' : S.Qt)} : Set S.Qt) := by
    intro p' v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := D.mem_cs.mp hv
    rw [Submodule.mem_span_singleton] at hu hw
    obtain ⟨α, hα⟩ := hu
    obtain ⟨β, hβ⟩ := hw
    have hu' : (u : S.Qt) = α • (p' : S.Qt) := by rw [← hα, Submodule.coe_smul]
    have hw' : (w : S.Qt) = β • (p' : S.Qt) := by rw [← hβ, Submodule.coe_smul]
    rw [D.coord_apply, hu', hw', map_smul]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ α (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ β (Submodule.subset_span (by simp)))
  have hcs_bot : ∀ z : S.Qt, z ∈ D.cs (⊥ : Submodule (ZMod 2) (Vt S D.g D.t)) → z = 0 := by
    intro z hz
    obtain ⟨u, hu, w, hw, rfl⟩ := D.mem_cs.mp hz
    rw [Submodule.mem_bot] at hu hw
    rw [hu, hw, D.coord_zero_zero]
  have hyM1 : y ∈ M1 := by
    rcases hp with hp0 | hp1
    · have ha0 : a ≠ 0 := by
        intro h0
        apply ha.2
        rw [hp0, Submodule.span_zero_singleton, Submodule.mem_bot]
        exact h0
      have h1a := hy' (a : S.Qt) (by rw [mem_fixSpace]; exact haC)
      rw [hp0, Submodule.span_zero_singleton] at h1a
      have hya : ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt)) = (a : S.Qt) := by
        have h0 : ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt)) - (a : S.Qt) = 0 := hcs_bot _ h1a
        rwa [sub_eq_zero] at h0
      have h1k := hy' ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt))
        (by rw [mem_fixSpace]; exact hkaC)
      rw [hp0, Submodule.span_zero_singleton] at h1k
      have hyka : ((y : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt))) =
          (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt) := by
        have h0 : ((y : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt))) -
            (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (a : S.Qt) = 0 := hcs_bot _ h1k
        rwa [sub_eq_zero] at h0
      exact D.rel.stab_le y hy (a : S.Qt) a.2 (fun h => ha0 (Subtype.ext h))
        (by rw [hya]; exact Submodule.subset_span (by simp))
        (by rw [hyka]; exact Submodule.subset_span (by simp))
    · have hp0 : (p : S.Qt) ≠ 0 := by
        intro h
        have h0 : p = 0 := Subtype.ext h
        rw [h0, map_zero] at hp1
        exact zero_ne_one hp1
      have hpC : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt) = (p : S.Qt) := by
        rw [← D.coe_resC_apply c p]
        exact congrArg Subtype.val (mem_fixSpace.mp (commSpace_le_fixSpace hρ2 hpP))
      have hkpC : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt)) =
          (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt) := by
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hck, Subgroup.coe_mul,
          LinearEquiv.mul_apply, hpC]
      have hya : ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt)) ∈
          Submodule.span (ZMod 2)
            ({(p : S.Qt), (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt)} : Set S.Qt) := by
        have h1 := hcs_le p (hy' (p : S.Qt) (by rw [mem_fixSpace]; exact hpC))
        have h2 : (p : S.Qt) ∈ Submodule.span (ZMod 2)
            ({(p : S.Qt), (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt)} : Set S.Qt) :=
          Submodule.subset_span (by simp)
        have h3 := Submodule.add_mem _ h1 h2
        rwa [sub_add_cancel] at h3
      have hyka : ((y : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt))) ∈
          Submodule.span (ZMod 2)
            ({(p : S.Qt), (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt)} : Set S.Qt) := by
        have h1 := hcs_le p (hy' ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt))
          (by rw [mem_fixSpace]; exact hkpC))
        have h2 : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt) ∈ Submodule.span (ZMod 2)
            ({(p : S.Qt), (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (p : S.Qt)} : Set S.Qt) :=
          Submodule.subset_span (by simp)
        have h3 := Submodule.add_mem _ h1 h2
        rwa [sub_add_cancel] at h3
      exact D.rel.stab_le y hy p p.2 hp0 hya hyka
  obtain ⟨s, hs, c', hc', hyeq⟩ := D.exists_mul_Cbar_of_mem_M1 hyM1
  have hF : ∀ u ∈ fixSpace (ρV c), D.coord (u, 0) ∈ fixSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      D.coord (0, u) ∈ fixSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun u hu =>
    ⟨(congrArg (_ ∈ ·) (D.fixSpace_Cbar_eq_cs c)).mpr
      (D.coord_mem_cs.mpr ⟨hu, Submodule.zero_mem _⟩),
     (congrArg (_ ∈ ·) (D.fixSpace_Cbar_eq_cs c)).mpr
      (D.coord_mem_cs.mpr ⟨Submodule.zero_mem _, hu⟩)⟩
  have e1 : ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, 0)) =
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (ρV ⟨c', hc'⟩ a, 0)) :=
    (congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, 0))) hyeq).trans
      (congrArg (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.Cbar_apply_coord_left ⟨c', hc'⟩ a))
  have e2 : ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, a)) =
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, ρV ⟨c', hc'⟩ a)) :=
    (congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, a))) hyeq).trans
      (congrArg (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.Cbar_apply_coord_right ⟨c', hc'⟩ a))
  have hs1 : s = 1 := D.eq_one_of_sub_mem_cs hs ha.2
    ((congrArg (· - D.coord (a, 0) ∈ D.cs ((ZMod 2) ∙ p)) e1).mp (hy' _ (hF a ha.1).1))
    ((congrArg (· - D.coord (0, a) ∈ D.cs ((ZMod 2) ∙ p)) e2).mp (hy' _ (hF a ha.1).2))
  have hyc' : y = c' := by rw [hyeq, hs1, one_mul]
  subst hyc'
  refine ⟨hc', fun a' ha' => ?_⟩
  have h3 := (congrArg (· ∈ D.cs ((ZMod 2) ∙ p)) (D.coord_sub_coord _ _ _ _)).mp
    ((congrArg (· - D.coord (a', 0) ∈ D.cs ((ZMod 2) ∙ p))
      (D.Cbar_apply_coord_left ⟨y, hc'⟩ a')).mp (hy' _ (hF a' ha').1))
  have h4 := mem_span_cl_iff.mp (D.coord_mem_cs.mp h3).1
  rcases h4 with h4 | h4
  · exact sub_eq_zero.mp h4
  · have h5 : ρV ⟨y, hc'⟩ a' = a' + p := by rw [← h4]; abel
    have h6 : D.QV a' + D.QV p + polar D.QV a' p = D.QV a' :=
      (map_add_eq D.QV a' p).symm.trans ((congrArg D.QV h5.symm).trans (D.QV_resC ⟨y, hc'⟩ a'))
    have h7 : polar D.QV a' p = 0 := by
      rw [polar_comm]
      exact D.polar_eq_zero_of_mem_fixSpace hcc hpP ha'
    rw [h7, add_zero] at h6
    have h8 : D.QV p = 0 := by simpa using h6
    rcases hp with hp | hp
    · exact sub_eq_zero.mp (h4.trans hp)
    · exact absurd (h8.symm.trans hp) zero_ne_one

theorem lbar_fix_of_fixQt_eq {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M)
    (_hxQ : k * S.z * k⁻¹ ∉ S.QG) (hxC : S.ρ ⟨k * S.z * k⁻¹, hxM⟩ ∈ D.Cbar)
    (hfix : S.fixQt (k * S.z * k⁻¹) = S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)))
    (hΔ : S.QG ⊓ S.Qa k = ⊥ ∨ ∃ p : Vt S D.g D.t,
      p ∈ commSpace (D.resC ⟨_, hxC⟩) ∧ D.QV p = 1 ∧
      ∀ v : S.Qt, v ∈ S.clSub (S.QG ⊓ S.Qa k) ↔ ∃ α β : ZMod 2, v = D.coord (α • p, β • p)) :
    ∀ a ∈ S.Lbar k, ∃ ha : a ∈ D.Cbar,
      ∀ v ∈ fixSpace (D.resC ⟨_, hxC⟩),
        D.resC ⟨a, ha⟩ v = v := by
  intro a ha
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hcc : ((⟨_, hxC⟩ : D.Cbar) : S.O) * (⟨_, hxC⟩ : D.Cbar) = 1 :=
    Subtype.ext (S.ρ_mul_self hxM hx2)
  have hv' : ∀ v ∈ fixSpace (((⟨_, hxC⟩ : D.Cbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
      v ∈ S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)) := fun v hv =>
    (congrArg (v ∈ ·) hfix).mp ((congrArg (v ∈ ·) (S.fixQt_of_mem hxM)).mpr hv)
  rcases hΔ with hbot | ⟨p, hpP, hpQ, hZp⟩
  · refine D.mem_Cbar_and_fix (S.Lbar_le_Mbar k ha) hcc (Submodule.zero_mem _) (Or.inl rfl)
      fun v hv => ?_
    have h := Lbar_apply_sub_mem ha (hv' v hv)
    obtain ⟨d, hd, hdQ, hdv⟩ := S.mem_clSub_iff.mp h
    rw [hbot, Subgroup.mem_bot] at hd
    rw [← hdv, hd, S.cl_one]
    exact Submodule.zero_mem _
  · refine D.mem_Cbar_and_fix (S.Lbar_le_Mbar k ha) hcc hpP (Or.inr hpQ) fun v hv => ?_
    obtain ⟨α, β, hαβ⟩ := (hZp _).mp (Lbar_apply_sub_mem ha (hv' v hv))
    rw [hαβ]
    exact D.mem_cs.mpr ⟨α • p, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p),
      β • p, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p), rfl⟩

private theorem exists_eq_cs {Z : Submodule (ZMod 2) S.Qt}
    (hZk : ∀ v ∈ Z, (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Z)
    (hZt : ∀ v ∈ Z, (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Z) :
    ∃ T : Submodule (ZMod 2) (Vt S D.g D.t), Z = D.cs T := by
  have hk0 : ∀ u, D.coord (u, 0) ∈ Z → D.coord (0, u) ∈ Z := fun u hu => by
    have h := hZk _ hu
    rwa [D.k_apply_coord, add_zero] at h
  have hcoordT : ∀ u v, D.coord (u, v) ∈ Z → D.coord (u, 0) ∈ Z ∧ D.coord (v, 0) ∈ Z := by
    intro u v hw
    have h1 : D.coord (v, 0) ∈ Z := by
      have h := Z.add_mem hw (hZt _ hw)
      rwa [D.t_apply_coord, D.coord_add_coord, ← add_assoc, ZModModule.add_self u, zero_add,
        ZModModule.add_self v] at h
    have h3 : D.coord (u, 0) ∈ Z := by
      have h := Z.add_mem hw (hk0 v h1)
      rwa [D.coord_add_coord, add_zero, ZModModule.add_self v] at h
    exact ⟨h3, h1⟩
  refine ⟨Z.comap ((D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt).comp
    (LinearMap.inl (ZMod 2) (Vt S D.g D.t) (Vt S D.g D.t))), Submodule.ext fun x => ?_⟩
  obtain ⟨⟨u, w⟩, rfl⟩ := D.coord.surjective x
  constructor
  · intro hx
    exact D.coord_mem_cs.mpr (hcoordT u w hx)
  · intro hx
    obtain ⟨hu, hw⟩ := D.coord_mem_cs.mp hx
    have hu' : D.coord (u, 0) ∈ Z := hu
    have hw' : D.coord (w, 0) ∈ Z := hw
    have h := Z.add_mem hu' (hk0 w hw')
    rwa [D.coord_add_coord, add_zero, zero_add] at h

private theorem false_of_mem_clSub_of_singular {k : G} (hbad : Bad S k) {s : Vt S D.g D.t}
    (hs0 : s ≠ 0) (hsQ : D.QV s = 0) {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa k))
    (hcoord : v = D.coord (s, 0) ∨ v = D.coord (0, s) ∨ v = D.coord (s, s)) : False := by
  obtain ⟨d, hd, hdQ, rfl⟩ := S.mem_clSub_iff.mp hv
  have hdz : d ≠ S.z := fun h => S14.SMK.z_not_mem_Dl S hbad.not_mem_QG (h ▸ hd)
  exact hbad.not_mem ((D.isConj_z_iff_coord hdQ hdz).mpr ⟨s, hs0, hsQ, hcoord⟩) hd

theorem residual_of_bad {k : G} (hbad : Bad S k)
    (hxC : S.ρ ⟨k * S.z * k⁻¹, hbad.mem_M⟩ ∈ D.Cbar) :
    (¬ IsConj S.z (k * S.z * k⁻¹ * S.z) ∧ S.QG ⊓ S.Qa k = ⊥) ∨
    (¬ IsConj S.z (k * S.z * k⁻¹ * S.z) ∧ ∃ p : Vt S D.g D.t,
      p ∈ commSpace (D.resC ⟨_, hxC⟩) ∧ D.QV p = 1 ∧
      ∀ v : S.Qt, v ∈ S.clSub (S.QG ⊓ S.Qa k) ↔ ∃ α β : ZMod 2, v = D.coord (α • p, β • p)) ∨
    (IsConj S.z (k * S.z * k⁻¹ * S.z) ∧
      ∀ d ∈ S.QG ⊓ S.Qa k, d ∈ S.clPre (S.commQt (k * S.z * k⁻¹)) → d = 1) := by
  have hxM := hbad.mem_M
  have hxQ := hbad.not_mem_QG
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  by_cases hxz : IsConj S.z (k * S.z * k⁻¹ * S.z)
  · refine Or.inr (Or.inr ⟨hxz, fun d hd hdJ => ?_⟩)
    by_contra hd1
    have hyJ : d ∈ (⁅zpowers (k * S.z * k⁻¹), S.QG⁆ : Subgroup G) := by
      rw [S.commutator_zpowers_eq_clPre hxM hxQ hx2]
      exact hdJ
    have hyx : Commute (k * S.z * k⁻¹) d :=
      (mem_centralizer_singleton_iff.mp (S14.SMK.mem_centralizer_of_mem_Qa S hd.2)).symm
    rcases S14.SMF.isConj_of_mem_J S hxM hxQ hd1 hyJ hyx hd.2 with h | h
    · exact hbad.not_mem h hd
    · exact hbad.not_mem (hxz.trans h) hd
  · set c : D.Cbar := ⟨_, hxC⟩ with hcdef
    have hcc : (c : S.O) * c = 1 := Subtype.ext (S.ρ_mul_self hxM hx2)
    set Z := S.clSub (S.QG ⊓ S.Qa k) with hZdef
    have hZc : Z ≤ D.cs (commSpace (ρV c)) := by
      have h := S14.SMK.clSub_Dl_le_commQt S hxM hxQ hxz
      rw [S.commQt_of_mem hxM] at h
      rw [← D.commSpace_Cbar_eq_cs c]
      exact h
    have hZinv : ∀ y ∈ S.Mbar, y * S.ρ ⟨k * S.z * k⁻¹, hxM⟩ = S.ρ ⟨k * S.z * k⁻¹, hxM⟩ * y →
        ∀ v ∈ Z, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Z :=
      fun y hy hyx v hv => clSub_Dl_apply_mem hxM hxz hy hyx hv
    have hZk : ∀ v ∈ Z, (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Z := fun v hv =>
      hZinv D.k D.k_mem_Mbar (D.Cbar_comm_k hxC).symm v hv
    have hZt : ∀ v ∈ Z, (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Z := fun v hv =>
      hZinv D.t D.t_mem_Mbar (D.comm_of_mem_Cbar hxC).symm v hv
    obtain ⟨T, hZT⟩ := D.exists_eq_cs hZk hZt
    have hT0Z : ∀ a ∈ T, D.coord (a, 0) ∈ Z := fun a ha =>
      (congrArg (_ ∈ ·) hZT).mpr (D.coord_mem_cs.mpr ⟨ha, Submodule.zero_mem _⟩)
    have hTP : ∀ a ∈ T, a ∈ commSpace (ρV c) := fun a ha =>
      (D.coord_mem_cs.mp (hZc (hT0Z a ha))).1
    by_cases hT0 : ∀ a ∈ T, a = 0
    ·
      refine Or.inl ⟨hxz, ?_⟩
      rw [eq_bot_iff]
      intro d hd
      rw [Subgroup.mem_bot]
      obtain ⟨⟨u, w⟩, hcl'⟩ := D.coord.surjective (S.cl d)
      have hcl : D.coord (u, w) ∈ D.cs T :=
        (congrArg (_ ∈ ·) hZT).mp (hcl' ▸ S.cl_mem_clSub hd hd.1)
      obtain ⟨hu, hw⟩ := D.coord_mem_cs.mp hcl
      rw [hT0 u hu, hT0 w hw, D.coord_zero_zero] at hcl'
      rcases (S.cl_eq_zero_iff hd.1).mp hcl'.symm with h | h
      · exact h
      · exact absurd (h ▸ hd) (S14.SMK.z_not_mem_Dl S hxQ)
    · push Not at hT0
      obtain ⟨p, hpT, hp0⟩ := hT0
      have hQ1 : ∀ a ∈ T, a ≠ 0 → D.QV a = 1 := by
        intro a ha ha0
        by_contra hne
        have hq0 : D.QV a = 0 := by
          rcases zmod2_cases (D.QV a) with h | h
          · exact h
          · exact absurd h hne
        exact D.false_of_mem_clSub_of_singular hbad ha0 hq0 (hT0Z a ha) (Or.inl rfl)
      have hQp := hQ1 p hpT hp0
      have hTpp : ∀ a ∈ T, a = 0 ∨ a = p := by
        intro a ha
        by_contra hne
        push Not at hne
        have hsum : a + p ∈ T := T.add_mem ha hpT
        have hsum0 : a + p ≠ 0 := fun h =>
          hne.2 ((eq_neg_of_add_eq_zero_left h).trans (ZModModule.neg_eq_self p))
        have h1 := hQ1 _ hsum hsum0
        rw [map_add_eq, hQ1 a ha hne.1, hQp,
          D.polar_eq_zero_of_mem_commSpace hcc (hTP a ha) (hTP p hpT)] at h1
        exact absurd h1 (by decide)
      have hex : ∀ a ∈ T, ∃ α : ZMod 2, a = α • p := fun a ha => by
        rcases hTpp a ha with rfl | rfl
        · exact ⟨0, (zero_smul _ _).symm⟩
        · exact ⟨1, (one_smul _ _).symm⟩
      refine Or.inr (Or.inl ⟨hxz, p, hTP p hpT, hQp, fun v => ?_⟩)
      constructor
      · intro hv
        obtain ⟨u, hu, w, hw, rfl⟩ := D.mem_cs.mp ((congrArg (v ∈ ·) hZT).mp hv)
        obtain ⟨α, rfl⟩ := hex u hu
        obtain ⟨β, rfl⟩ := hex w hw
        exact ⟨α, β, rfl⟩
      · rintro ⟨α, β, rfl⟩
        exact (congrArg (_ ∈ ·) hZT).mpr
          (D.coord_mem_cs.mpr ⟨T.smul_mem α hpT, T.smul_mem β hpT⟩)

private theorem mul_comm_of_resC {a b : D.Cbar} (h : ρV a * ρV b = ρV b * ρV a) :
    (a : S.O) * b = b * a :=
  congrArg Subtype.val
    (D.resC_injective ((map_mul (ρV) a b).trans (h.trans (map_mul (ρV) b a).symm)))

private theorem lbar_comm_of_fixQt_eq {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M)
    (hxQ : k * S.z * k⁻¹ ∉ S.QG) (hxC : S.ρ ⟨k * S.z * k⁻¹, hxM⟩ ∈ D.Cbar)
    (hfix : S.fixQt (k * S.z * k⁻¹) = S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)))
    (hΔ : S.QG ⊓ S.Qa k = ⊥ ∨ ∃ p : Vt S D.g D.t,
      p ∈ commSpace (D.resC ⟨_, hxC⟩) ∧ D.QV p = 1 ∧
      ∀ v : S.Qt, v ∈ S.clSub (S.QG ⊓ S.Qa k) ↔ ∃ α β : ZMod 2, v = D.coord (α • p, β • p)) :
    ∀ a ∈ S.Lbar k, ∀ b ∈ S.Lbar k, a * b = b * a := by
  intro a ha b hb
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hcc : ((⟨_, hxC⟩ : D.Cbar) : S.O) * (⟨_, hxC⟩ : D.Cbar) = 1 :=
    Subtype.ext (S.ρ_mul_self hxM hx2)
  obtain ⟨haC, hafix⟩ := D.lbar_fix_of_fixQt_eq hxM hxQ hxC hfix hΔ a ha
  obtain ⟨hbC, hbfix⟩ := D.lbar_fix_of_fixQt_eq hxM hxQ hxC hfix hΔ b hb
  exact D.mul_comm_of_resC (S14.SMK.commute_of_fix (D.resC_mem_orthogonalGroup _)
    (D.resC_mem_orthogonalGroup _) (D.orthogonal_fixSpace_le hcc) hafix hbfix)

private theorem q_eq_zero_of_mem_cs_commSpace {c : D.Cbar} (hcc : (c : S.O) * c = 1)
    {v : S.Qt} (hv : v ∈ D.cs (commSpace (ρV c))) : S.q v = 0 := by
  obtain ⟨u, hu, w, hw, rfl⟩ := D.mem_cs.mp hv
  rw [D.q_coord, ← D.polar_QV]
  exact D.polar_eq_zero_of_mem_commSpace hcc hu hw

private theorem mem_Cbar_of_fix_coord {y : S.O} (hy : y ∈ S.Mbar) {a : Vt S D.g D.t} (ha : a ≠ 0)
    (h1 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, 0)) = D.coord (a, 0))
    (h2 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, a)) = D.coord (0, a)) :
    y ∈ D.Cbar := by
  have h1a := h1
  rw [D.coord_apply_zero_right] at h1a
  have h2a := h2
  rw [D.coord_apply_zero_left] at h2a
  have hyM1 : y ∈ M1 := D.rel.stab_le y hy (a : S.Qt) a.2 (fun h => ha (Subtype.ext h))
    (by rw [h1a]; exact Submodule.subset_span (by simp))
    (by rw [h2a]; exact Submodule.subset_span (by simp))
  obtain ⟨s, hs, c', hc', hyeq⟩ := D.exists_mul_Cbar_of_mem_M1 hyM1
  have e1 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (ρV ⟨c', hc'⟩ a, 0)) = D.coord (a, 0) :=
    ((congrArg (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.Cbar_apply_coord_left ⟨c', hc'⟩ a)).symm.trans
      ((congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, 0))) hyeq).symm.trans h1))
  have e2 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, ρV ⟨c', hc'⟩ a)) = D.coord (0, a) :=
    ((congrArg (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.Cbar_apply_coord_right ⟨c', hc'⟩ a)).symm.trans
      ((congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, a))) hyeq).symm.trans h2))
  have hs1 : s = 1 := D.eq_one_of_apply_coord hs ha ha e1 e2
  rw [hyeq, hs1, one_mul]
  exact hc'

private theorem exists_ne_zero_mem_commSpace {c : D.Cbar} (hc1 : (c : S.O) ≠ 1) :
    ∃ a ∈ commSpace (ρV c), a ≠ 0 := by
  have hĉ1 : ρV c ≠ 1 := fun h =>
    hc1 (congrArg Subtype.val (D.resC_injective (h.trans (map_one _).symm)))
  have h2 : commSpace (ρV c) ≠ ⊥ :=
    Submodule.one_le_finrank_iff.mp (one_le_finrank_commSpace hĉ1)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h2
  exact ⟨a, ha, ha0⟩

private theorem R3_fix {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    {c : D.Cbar} (hcoe : (c : S.O) = S.ρ ⟨k * S.z * k⁻¹, hxM⟩)
    (hJ : ∀ d ∈ S.QG ⊓ S.Qa k, d ∈ S.clPre (S.commQt (k * S.z * k⁻¹)) → d = 1)
    {y : S.O} (hy : y ∈ S.Lbar k) :
    ∃ y' : D.Cbar, (y' : S.O) = y ∧ ∀ p ∈ commSpace (ρV c), ρV y' p = p := by
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hcc : (c : S.O) * c = 1 :=
    (congrArg₂ (· * ·) hcoe hcoe).trans (Subtype.ext (S.ρ_mul_self hxM hx2))
  have hcomm : S.commQt (k * S.z * k⁻¹) = D.cs (commSpace (ρV c)) :=
    (S.commQt_of_mem hxM).trans ((congrArg (fun e : S.O => commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt))
      hcoe).symm.trans (D.commSpace_Cbar_eq_cs c))
  have hq : ∀ v ∈ S.commQt (k * S.z * k⁻¹), S.q v = 0 := fun v hv =>
    D.q_eq_zero_of_mem_cs_commSpace hcc (hcomm ▸ hv)
  have hfixY : ∀ {v : S.Qt}, v ∈ D.cs (commSpace (ρV c)) → (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
    fun {v} hv => Lbar_apply_eq_of_mem_commQt hxM hx2 hq hJ hy (hcomm ▸ hv)
  have hc1 : (c : S.O) ≠ 1 := fun h => hxQ ((S.ρ_eq_one_iff ⟨_, hxM⟩).mp (hcoe.symm.trans h))
  refine (D.exists_ne_zero_mem_commSpace hc1).elim fun a₀ ha₀ => ?_
  have h0P : ∀ p ∈ commSpace (ρV c), D.coord (p, 0) ∈ D.cs (commSpace (ρV c)) ∧
      D.coord (0, p) ∈ D.cs (commSpace (ρV c)) := fun p hp =>
    ⟨D.coord_mem_cs.mpr ⟨hp, Submodule.zero_mem _⟩, D.coord_mem_cs.mpr ⟨Submodule.zero_mem _, hp⟩⟩
  have hyC : y ∈ D.Cbar :=
    D.mem_Cbar_of_fix_coord (S.Lbar_le_Mbar k hy) ha₀.2 (hfixY (h0P a₀ ha₀.1).1)
      (hfixY (h0P a₀ ha₀.1).2)
  refine ⟨⟨y, hyC⟩, rfl, fun p hp => ?_⟩
  have h1 := (D.Cbar_apply_coord_left ⟨y, hyC⟩ p).symm.trans (hfixY (h0P p hp).1)
  exact (Prod.mk.inj (D.coord.injective h1)).1

private theorem finrank_map_cs_le {F : Submodule (ZMod 2) (Vt S D.g D.t)}
    {N : Vt S D.g D.t →ₗ[ZMod 2] Vt S D.g D.t} {φ : S.Qt →ₗ[ZMod 2] S.Qt}
    (hφ : ∀ u w, φ (D.coord (u, w)) = D.coord (N u, N w))
    {H Z : Submodule (ZMod 2) S.Qt} (hHF : H ≤ D.cs F)
    (hdimF : finrank (ZMod 2) (D.cs F) ≤ finrank (ZMod 2) H + 1)
    (hφH : H.map φ ≤ Z) (hZ1 : finrank (ZMod 2) Z ≤ 1) :
    finrank (ZMod 2) (F.map N) ≤ 1 ∧ (F.map N ≠ ⊥ →
      finrank (ZMod 2) (F.map N) = 1 ∧ Z ≠ ⊥ ∧ Z ≤ D.cs (F.map N)) := by
  have hmapcs : (D.cs F).map φ = D.cs (F.map N) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu, w, hw, rfl⟩ := D.mem_cs.mp hv
      rw [hφ]
      exact D.mem_cs.mpr ⟨N u, Submodule.mem_map_of_mem hu, N w, Submodule.mem_map_of_mem hw, rfl⟩
    · intro hx
      obtain ⟨u', hu', w', hw', rfl⟩ := D.mem_cs.mp hx
      obtain ⟨u, hu, rfl⟩ := hu'
      obtain ⟨w, hw, rfl⟩ := hw'
      exact ⟨D.coord (u, w), D.mem_cs.mpr ⟨u, hu, w, hw, rfl⟩, hφ u w⟩
  have h1 := CaseII.finrank_map_le_add_one φ hHF hdimF
  have h2 : finrank (ZMod 2) (H.map φ) ≤ finrank (ZMod 2) Z := Submodule.finrank_mono hφH
  rw [hmapcs, D.finrank_cs] at h1
  have hE : finrank (ZMod 2) (F.map N) ≤ 1 := by omega
  refine ⟨hE, fun hE0 => ?_⟩
  have hE1 : finrank (ZMod 2) (F.map N) = 1 := by
    have := Submodule.one_le_finrank_iff.mpr hE0
    omega
  have hHZ : H.map φ = Z := Submodule.eq_of_le_of_finrank_eq hφH (by omega)
  have hZ1' : finrank (ZMod 2) Z = 1 := by omega
  refine ⟨hE1, fun hb => ?_, ?_⟩
  · rw [hb, finrank_bot] at hZ1'
    exact zero_ne_one hZ1'
  · rw [← hHZ, ← hmapcs]
    exact Submodule.map_mono hHF

private theorem exists_sub_one_Vt (y' : D.Cbar) :
    ∃ N : Vt S D.g D.t →ₗ[ZMod 2] Vt S D.g D.t, ∀ u, N u = ρV y' u - u :=
  CaseII.exists_sub_one (ρV y')

private theorem exists_sub_one_Qt (y' : D.Cbar) :
    ∃ φ : S.Qt →ₗ[ZMod 2] S.Qt, ∀ v, φ v = ((y' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v :=
  CaseII.exists_sub_one ((y' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)

private theorem R3_dich_core {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    {c y' : D.Cbar} (hcoe : (c : S.O) = S.ρ ⟨k * S.z * k⁻¹, hxM⟩)
    (hJ : ∀ d ∈ S.QG ⊓ S.Qa k, d ∈ S.clPre (S.commQt (k * S.z * k⁻¹)) → d = 1)
    (hy : (y' : S.O) ∈ S.Lbar k) (hfixP : ∀ p ∈ commSpace (ρV c), ρV y' p = p)
    {N : Vt S D.g D.t →ₗ[ZMod 2] Vt S D.g D.t} {φ : S.Qt →ₗ[ZMod 2] S.Qt}
    (hNu : ∀ u, N u = ρV y' u - u)
    (hφv : ∀ v, φ v = ((y' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) :
    (∀ a ∈ fixSpace (ρV c), ρV y' a = a) ∨
      (S.clSub (S.QG ⊓ S.Qa k) ≠ ⊥ ∧ ∃ L : Submodule (ZMod 2) (Vt S D.g D.t),
        finrank (ZMod 2) L = 1 ∧ L ≤ fixSpace (ρV c) ∧
        S.clSub (S.QG ⊓ S.Qa k) ≤ D.cs L ∧ ∀ a ∈ fixSpace (ρV c), ρV y' a - a ∈ L) := by
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hcc : (c : S.O) * c = 1 :=
    (congrArg₂ (· * ·) hcoe hcoe).trans (Subtype.ext (S.ρ_mul_self hxM hx2))
  have hfixeq : S.fixQt (k * S.z * k⁻¹) = D.cs (fixSpace (ρV c)) :=
    (S.fixQt_of_mem hxM).trans ((congrArg (fun e : S.O => fixSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt))
      hcoe).symm.trans (D.fixSpace_Cbar_eq_cs c))
  have hφcoord : ∀ u w, φ (D.coord (u, w)) = D.coord (N u, N w) := fun u w =>
    (hφv _).trans ((congrArg (· - D.coord (u, w)) (D.Cbar_apply_coord y' u w)).trans
      ((D.coord_sub_coord _ _ _ _).trans (congrArg D.coord (Prod.ext (hNu u).symm (hNu w).symm))))
  have hφH : (S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G))).map φ ≤
      S.clSub (S.QG ⊓ S.Qa k) := by
    rintro _ ⟨v, hv, rfl⟩
    exact (congrArg (· ∈ S.clSub (S.QG ⊓ S.Qa k)) (hφv v)).mpr (Lbar_apply_sub_mem hy hv)
  have hHF : S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)) ≤ D.cs (fixSpace (ρV c)) :=
    (congrArg (S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)) ≤ ·) hfixeq).mp
      (S.clSub_centralizer_le_fixQt hxM)
  have hdimF : finrank (ZMod 2) (D.cs (fixSpace (ρV c))) ≤
      finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G))) + 1 :=
    (congrArg (fun W : Submodule (ZMod 2) S.Qt => finrank (ZMod 2) W ≤
      finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G))) + 1) hfixeq).mp
      (S14.SMK.finrank_fixQt_le S hxM hxQ hx2)
  have hZ1 : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa k)) ≤ 1 :=
    S14.SMK.finrank_clSub_Dl_le_one S hxM hxQ hJ
  have hres := D.finrank_map_cs_le (F := fixSpace (ρV c)) (N := N) (φ := φ)
    (H := S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)))
    (Z := S.clSub (S.QG ⊓ S.Qa k)) hφcoord hHF hdimF hφH hZ1
  by_cases hE0 : (fixSpace (ρV c)).map N = ⊥
  · left
    intro a ha
    have h3 : N a = 0 := (Submodule.mem_bot _).mp
      ((congrArg (N a ∈ ·) hE0).mp (Submodule.mem_map_of_mem ha))
    exact sub_eq_zero.mp ((hNu a).symm.trans h3)
  · right
    have hE'' := hres.2 hE0
    refine ⟨hE''.2.1, (fixSpace (ρV c)).map N, hE''.1, fun w hw => ?_, hE''.2.2,
      fun a ha => Submodule.mem_map.mpr ⟨a, ha, hNu a⟩⟩
    obtain ⟨a, ha, rfl⟩ := hw
    refine (congrArg (· ∈ fixSpace (ρV c)) (hNu a)).mpr ?_
    exact (congrArg (ρV y' a - a ∈ ·) (D.fixSpace_eq_orthogonal hcc)).mpr
      (S14.SMK.sub_mem_orthogonal (D.resC_mem_orthogonalGroup y') hfixP a)

private theorem R3_dich {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    {c y' : D.Cbar} (hcoe : (c : S.O) = S.ρ ⟨k * S.z * k⁻¹, hxM⟩)
    (hJ : ∀ d ∈ S.QG ⊓ S.Qa k, d ∈ S.clPre (S.commQt (k * S.z * k⁻¹)) → d = 1)
    (hy : (y' : S.O) ∈ S.Lbar k) (hfixP : ∀ p ∈ commSpace (ρV c), ρV y' p = p) :
    (∀ a ∈ fixSpace (ρV c), ρV y' a = a) ∨
      (S.clSub (S.QG ⊓ S.Qa k) ≠ ⊥ ∧ ∃ L : Submodule (ZMod 2) (Vt S D.g D.t),
        finrank (ZMod 2) L = 1 ∧ L ≤ fixSpace (ρV c) ∧
        S.clSub (S.QG ⊓ S.Qa k) ≤ D.cs L ∧ ∀ a ∈ fixSpace (ρV c), ρV y' a - a ∈ L) :=
  (D.exists_sub_one_Vt y').elim fun _ hNu => (D.exists_sub_one_Qt y').elim fun _ hφv =>
    D.R3_dich_core hxM hxQ hcoe hJ hy hfixP hNu hφv

private theorem R3_elt {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    {c : D.Cbar} (hcoe : (c : S.O) = S.ρ ⟨k * S.z * k⁻¹, hxM⟩)
    (hJ : ∀ d ∈ S.QG ⊓ S.Qa k, d ∈ S.clPre (S.commQt (k * S.z * k⁻¹)) → d = 1)
    {y : S.O} (hy : y ∈ S.Lbar k) :
    ∃ y' : D.Cbar, (y' : S.O) = y ∧ (∀ p ∈ commSpace (ρV c), ρV y' p = p) ∧
      ((∀ a ∈ fixSpace (ρV c), ρV y' a = a) ∨
        (S.clSub (S.QG ⊓ S.Qa k) ≠ ⊥ ∧ ∃ L : Submodule (ZMod 2) (Vt S D.g D.t),
          finrank (ZMod 2) L = 1 ∧ L ≤ fixSpace (ρV c) ∧
          S.clSub (S.QG ⊓ S.Qa k) ≤ D.cs L ∧ ∀ a ∈ fixSpace (ρV c), ρV y' a - a ∈ L)) :=
  (D.R3_fix hxM hxQ hcoe hJ hy).elim fun y' hy' =>
    ⟨y', hy'.1, hy'.2, D.R3_dich hxM hxQ hcoe hJ (hy'.1 ▸ hy) hy'.2⟩

private theorem R3_pair {k : G} (hbad : Bad S k) {c a' b' : D.Cbar}
    (hcc : (c : S.O) * c = 1)
    (hfa : ∀ p ∈ commSpace (ρV c), ρV a' p = p) (hfb : ∀ p ∈ commSpace (ρV c), ρV b' p = p)
    (ha : S.clSub (S.QG ⊓ S.Qa k) ≠ ⊥ ∧ ∃ L : Submodule (ZMod 2) (Vt S D.g D.t),
      finrank (ZMod 2) L = 1 ∧ L ≤ fixSpace (ρV c) ∧
      S.clSub (S.QG ⊓ S.Qa k) ≤ D.cs L ∧ ∀ a ∈ fixSpace (ρV c), ρV a' a - a ∈ L)
    (hb : (∀ a ∈ fixSpace (ρV c), ρV b' a = a) ∨
      (S.clSub (S.QG ⊓ S.Qa k) ≠ ⊥ ∧ ∃ L : Submodule (ZMod 2) (Vt S D.g D.t),
        finrank (ZMod 2) L = 1 ∧ L ≤ fixSpace (ρV c) ∧
        S.clSub (S.QG ⊓ S.Qa k) ≤ D.cs L ∧ ∀ a ∈ fixSpace (ρV c), ρV b' a - a ∈ L)) :
    ρV a' * ρV b' = ρV b' * ρV a' := by
  refine (Submodule.exists_mem_ne_zero_of_ne_bot ha.1).elim fun ζ hζ' => ?_
  refine ha.2.elim fun La hLa => ?_
  have hζZ := hζ'.1
  have hζ0 := hζ'.2
  have hLa1 := hLa.1
  have hLaF := hLa.2.1
  have hNa := hLa.2.2.2
  refine (D.mem_cs.mp (hLa.2.2.1 hζZ)).elim fun u hu' => ?_
  refine hu'.2.elim fun w hw' => ?_
  have hu := hu'.1
  have hw := hw'.1
  have hζ := hw'.2
  have hFo := D.fixSpace_eq_orthogonal hcc
  have hPP : commSpace (ρV c) ≤ LinearMap.BilinForm.orthogonal D.QV.polarBilin
      (commSpace (ρV c)) :=
    (congrArg (commSpace (ρV c) ≤ ·) hFo).mp (commSpace_le_fixSpace (D.resC_mul_self hcc))
  have key : ∀ e ∈ La, e ≠ 0 → (u = 0 ∨ u = e) → (w = 0 ∨ w = e) →
      ρV a' * ρV b' = ρV b' * ρV a' := by
    intro e heLa he0 hue hwe
    have hLaspan : La = (ZMod 2) ∙ e := eq_span_singleton_of_mem_of_finrank_eq_one hLa1 heLa he0
    have hpure : ζ = D.coord (e, 0) ∨ ζ = D.coord (0, e) ∨ ζ = D.coord (e, e) := by
      rcases hue with hu' | hu' <;> rcases hwe with hw' | hw'
      · exact absurd (by rw [hζ, hu', hw']; exact D.coord_zero_zero) hζ0
      · exact Or.inr (Or.inl (by rw [hζ, hu', hw']))
      · exact Or.inl (by rw [hζ, hu', hw'])
      · exact Or.inr (Or.inr (by rw [hζ, hu', hw']))
    have hQe : D.QV e = 1 := by
      by_contra hne
      exact D.false_of_mem_clSub_of_singular hbad he0
        ((zmod2_cases (D.QV e)).resolve_right hne) hζZ hpure
    have hNb : ∀ a ∈ fixSpace (ρV c), ρV b' a - a ∈ (ZMod 2) ∙ e := by
      rcases hb with hfb' | ⟨_, Lb, hLb1, _, hZLb, hNb⟩
      · intro a ha'
        rw [hfb' a ha', sub_self]
        exact Submodule.zero_mem _
      · obtain ⟨u', hu', w', hw', hζ'⟩ := D.mem_cs.mp (hZLb hζZ)
        have heLb : e ∈ Lb := by
          rcases hpure with h | h | h
          · exact (Prod.mk.inj (D.coord.injective (hζ'.symm.trans h))).1 ▸ hu'
          · exact (Prod.mk.inj (D.coord.injective (hζ'.symm.trans h))).2 ▸ hw'
          · exact (Prod.mk.inj (D.coord.injective (hζ'.symm.trans h))).1 ▸ hu'
        have hLbspan : Lb = (ZMod 2) ∙ e :=
          eq_span_singleton_of_mem_of_finrank_eq_one hLb1 heLb he0
        intro a ha'
        exact (congrArg (ρV b' a - a ∈ ·) hLbspan).mp (hNb a ha')
    exact commute_of_sub_mem_span (P := commSpace (ρV c)) hPP (e := e)
      ((congrArg (e ∈ ·) hFo).mp (hLaF heLa)) hQe (D.QV_resC a') (D.QV_resC b') hfa hfb
      (fun a ha' => (congrArg (ρV a' a - a ∈ ·) hLaspan).mp
        (hNa a ((congrArg (a ∈ ·) hFo).mpr ha')))
      (fun a ha' => hNb a ((congrArg (a ∈ ·) hFo).mpr ha'))
  by_cases hu0 : u = 0
  · have hw0 : w ≠ 0 := fun h => hζ0 (by rw [hζ, hu0, h]; exact D.coord_zero_zero)
    exact key w hw hw0 (Or.inl hu0) (Or.inr rfl)
  · exact key u hu hu0 (Or.inr rfl) ((mem_span_cl_iff.mp (by
      rw [← eq_span_singleton_of_mem_of_finrank_eq_one hLa1 hu hu0]; exact hw)))

private theorem lbar_comm_of_R3 {k : G} (hbad : Bad S k) {c : D.Cbar}
    (hcoe : (c : S.O) = S.ρ ⟨k * S.z * k⁻¹, hbad.mem_M⟩)
    (hJ : ∀ d ∈ S.QG ⊓ S.Qa k, d ∈ S.clPre (S.commQt (k * S.z * k⁻¹)) → d = 1) :
    ∀ a ∈ S.Lbar k, ∀ b ∈ S.Lbar k, a * b = b * a := by
  intro a ha b hb
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hcc : (c : S.O) * c = 1 :=
    (congrArg₂ (· * ·) hcoe hcoe).trans (Subtype.ext (S.ρ_mul_self hbad.mem_M hx2))
  refine (D.R3_elt hbad.mem_M hbad.not_mem_QG hcoe hJ ha).elim fun a' ha' =>
    (D.R3_elt hbad.mem_M hbad.not_mem_QG hcoe hJ hb).elim fun b' hb' => ?_
  have key : ρV a' * ρV b' = ρV b' * ρV a' :=
    ha'.2.2.elim
      (fun hfa => hb'.2.2.elim
        (fun hfb => S14.SMK.commute_of_fix (D.resC_mem_orthogonalGroup a')
          (D.resC_mem_orthogonalGroup b') (D.orthogonal_fixSpace_le hcc) hfa hfb)
        (fun hnb => (D.R3_pair hbad hcc hb'.2.1 ha'.2.1 hnb (Or.inl hfa)).symm))
      (fun hna => D.R3_pair hbad hcc ha'.2.1 hb'.2.1 hna hb'.2.2)
  exact (congrArg₂ (· * ·) ha'.1 hb'.1).symm.trans
    ((D.mul_comm_of_resC key).trans (congrArg₂ (· * ·) hb'.1 ha'.1))

theorem lbar_comm_of_bad {k : G} (hbad : Bad S k)
    (hxC : S.ρ ⟨k * S.z * k⁻¹, hbad.mem_M⟩ ∈ D.Cbar) :
    ∀ a ∈ S.Lbar k, ∀ b ∈ S.Lbar k, a * b = b * a := by
  rcases D.residual_of_bad hbad hxC with ⟨hxz, hΔ⟩ | ⟨hxz, p, hpP, hpQ, hZp⟩ | ⟨-, hJ⟩
  · exact D.lbar_comm_of_fixQt_eq hbad.mem_M hbad.not_mem_QG hxC
      (S14.SMK.fixQt_eq_of_not_isConj S hbad.mem_M hxz) (Or.inl hΔ)
  · exact D.lbar_comm_of_fixQt_eq hbad.mem_M hbad.not_mem_QG hxC
      (S14.SMK.fixQt_eq_of_not_isConj S hbad.mem_M hxz) (Or.inr ⟨p, hpP, hpQ, hZp⟩)
  · exact D.lbar_comm_of_R3 hbad (c := ⟨_, hxC⟩) rfl hJ

end S2Data

end CFSG.GF2Type.Smith1980Orth

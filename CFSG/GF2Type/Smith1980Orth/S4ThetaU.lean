module

public import CFSG.GF2Type.Smith1980Orth.S3Types
public import CFSG.GF2Type.Smith1980Orth.S4Siegel
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.Fischer.NoF25.Local
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.PSL10Fix
public import CFSG.LargeExtraspecial.S12InspUse
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.LargeExtraspecial.S14SMEPath
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

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private theorem finrank_le_two_mul_finrank_inf_fixSpace {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {h : V ≃ₗ[ZMod 2] V} (hh : h * h = 1)
    {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, h u ∈ U) :
    finrank (ZMod 2) U ≤ 2 * finrank (ZMod 2) (U ⊓ fixSpace h : Submodule (ZMod 2) V) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (((h : V →ₗ[ZMod 2] V) - 1).domRestrict U)
  have h2 : U.map ((h : V →ₗ[ZMod 2] V) - 1) ≤ U ⊓ fixSpace h := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨?_, commSpace_le_fixSpace hh (LinearMap.mem_range_self _ u)⟩
    simpa using U.sub_mem (hU u hu) hu
  have h3 : finrank (ZMod 2) (Submodule.comap U.subtype (LinearMap.ker
        ((h : V →ₗ[ZMod 2] V) - 1))) =
      finrank (ZMod 2) (U ⊓ fixSpace h : Submodule (ZMod 2) V) := by
    rw [← Submodule.finrank_map_subtype_eq U, Submodule.map_comap_subtype]
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  have h4 := Submodule.finrank_mono h2
  omega

private theorem mul_comm_of_cl_mem_fixSpace {θ q : G} (hθM : θ ∈ S.M) (hθ3 : θ ^ 3 = 1)
    (hq : q ∈ S.QG)
    (hfix : S.cl q ∈ fixSpace ((S.ρ ⟨θ, hθM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    q * θ = θ * q := by
  have h1 : S.cl (θ * q * θ⁻¹) = S.cl q := by
    rw [← S.ρ_cl ⟨θ, hθM⟩ hq]
    exact mem_fixSpace.mp hfix
  rcases (S.cl_eq_cl_iff hq (S.conj_mem_QG hθM hq)).mp h1.symm with e | e
  · rw [mul_inv_eq_iff_eq_mul] at e
    exact e.symm
  · exfalso
    have hθ3' : θ * θ * θ = 1 := by rw [← pow_three']; exact hθ3
    have hθz : θ * S.z * θ⁻¹ = S.z := by
      rw [S.z_comm hθM, mul_assoc, mul_inv_cancel, mul_one]
    have e2 : θ * (q * S.z) * θ⁻¹ = q := by
      calc θ * (q * S.z) * θ⁻¹ = (θ * q * θ⁻¹) * (θ * S.z * θ⁻¹) := by group
        _ = q := by rw [e, hθz, mul_assoc, S.z_mul_z, mul_one]
    have e3 : θ * (θ * (θ * q * θ⁻¹) * θ⁻¹) * θ⁻¹ = q * S.z := by rw [e, e2, e]
    have e4 : θ * (θ * (θ * q * θ⁻¹) * θ⁻¹) * θ⁻¹ = q := by
      calc θ * (θ * (θ * q * θ⁻¹) * θ⁻¹) * θ⁻¹ = (θ * θ * θ) * q * (θ * θ * θ)⁻¹ := by group
        _ = q := by rw [hθ3']; group
    exact S.z_ne_one (mul_left_cancel (a := q) (by rw [mul_one]; exact e3.symm.trans e4))

private theorem card_le_two_mul_card_commute {g : G} (hgM : g ∈ S.M) {E : Subgroup G}
    (hE : E ≤ S.QG) (hfix : ∀ q ∈ E, S.cl (g * q * g⁻¹) = S.cl q) :
    Nat.card E ≤ 2 * Nat.card {q : G // q ∈ E ∧ q * g = g * q} := by
  have hc : ∀ q ∈ E, g * q * g⁻¹ * q⁻¹ = 1 ∨ g * q * g⁻¹ * q⁻¹ = S.z := by
    intro q hq
    rcases (S.cl_eq_cl_iff (hE hq) (S.conj_mem_QG hgM (hE hq))).mp (hfix q hq).symm with e | e
    · left
      rw [e, mul_inv_cancel]
    · right
      rw [e, S.z_comm_QG (hE hq), mul_assoc, mul_inv_cancel, mul_one]
  have hmul : ∀ q q' : E, g * ((q * q' : E) : G) * g⁻¹ * ((q * q' : E) : G)⁻¹ =
      (g * q * g⁻¹ * (q : G)⁻¹) * (g * q' * g⁻¹ * (q' : G)⁻¹) := by
    intro q q'
    have hcen : (q : G)⁻¹ * (g * q' * g⁻¹ * (q' : G)⁻¹) =
        (g * q' * g⁻¹ * (q' : G)⁻¹) * (q : G)⁻¹ := by
      rcases hc q' q'.2 with h | h
      · rw [h, mul_one, one_mul]
      · rw [h]
        exact S.z_comm_QG (S.QG.inv_mem (hE q.2))
    calc g * ((q * q' : E) : G) * g⁻¹ * ((q * q' : E) : G)⁻¹
        = (g * q * g⁻¹) * ((g * q' * g⁻¹ * (q' : G)⁻¹) * (q : G)⁻¹) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group
      _ = (g * q * g⁻¹) * ((q : G)⁻¹ * (g * q' * g⁻¹ * (q' : G)⁻¹)) := by rw [hcen]
      _ = (g * q * g⁻¹ * (q : G)⁻¹) * (g * q' * g⁻¹ * (q' : G)⁻¹) := by group
  obtain ⟨f, hf⟩ : ∃ f : E →* G, ∀ q : E, f q = g * q * g⁻¹ * (q : G)⁻¹ :=
    ⟨MonoidHom.mk' (fun q : E => g * q * g⁻¹ * (q : G)⁻¹) hmul, fun _ => rfl⟩
  have hker : ∀ q : E, q ∈ f.ker ↔ (q : G) * g = g * (q : G) := by
    intro q
    rw [MonoidHom.mem_ker, hf, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, eq_comm]
  have hrange : f.range ≤ zpowers S.z := by
    rintro _ ⟨q, rfl⟩
    rw [hf]
    rcases hc q q.2 with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  have hidx : f.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card f.range ≤ Nat.card (zpowers S.z) := Subgroup.card_le_of_le hrange
      _ = 2 := by rw [Nat.card_zpowers, S.orderOf_z]
  have hinj : Nat.card f.ker ≤ Nat.card {q : G // q ∈ E ∧ q * g = g * q} :=
    Nat.card_le_card_of_injective
      (fun q : f.ker => (⟨((q : E) : G), (q : E).2, (hker q).mp q.2⟩ :
        {q : G // q ∈ E ∧ q * g = g * q}))
      (fun q q' h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)))
  calc Nat.card E = Nat.card f.ker * f.ker.index := (Subgroup.card_mul_index f.ker).symm
    _ ≤ Nat.card {q : G // q ∈ E ∧ q * g = g * q} * 2 := Nat.mul_le_mul hinj hidx
    _ = 2 * Nat.card {q : G // q ∈ E ∧ q * g = g * q} := mul_comm _ _

private theorem two_pow_le_card_of_finrank {θ g : G} (hgM : g ∈ S.M) (hg2 : g ^ 2 = 1)
    {U : Submodule (ZMod 2) S.Qt} (hU : ∀ u ∈ U, (S.ρ ⟨g, hgM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U)
    (hcomm : ∀ q ∈ S.QG, S.cl q ∈ U → q * θ = θ * q) {m : ℕ}
    (hm : 2 * m ≤ finrank (ZMod 2) U) :
    2 ^ m ≤ Nat.card {q : G // q ∈ S.QG ∧ q * θ = θ * q ∧ q * g = g * q} := by
  obtain ⟨W, hW⟩ : ∃ W : Submodule (ZMod 2) S.Qt,
      W = U ⊓ fixSpace (S.ρ ⟨g, hgM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨_, rfl⟩
  have hgg : (S.ρ ⟨g, hgM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (S.ρ ⟨g, hgM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul]
    have : (⟨g, hgM⟩ : S.M) * ⟨g, hgM⟩ = 1 := Subtype.ext (by rw [← pow_two]; exact hg2)
    rw [this, map_one]
    rfl
  have h1 : finrank (ZMod 2) U ≤ 2 * finrank (ZMod 2) W := by
    rw [hW]
    exact finrank_le_two_mul_finrank_inf_fixSpace hgg hU
  have hE : Nat.card (S.clPre W) = 2 * 2 ^ finrank (ZMod 2) W := by
    rw [S.card_clPre, S.card_submodule]
  have hfix : ∀ q ∈ S.clPre W, S.cl (g * q * g⁻¹) = S.cl q := by
    intro q hq
    have h2 := mem_fixSpace.mp (Submodule.mem_inf.mp (hW.le hq.2)).2
    rw [S.ρ_cl ⟨g, hgM⟩ hq.1] at h2
    exact h2
  have hK := card_le_two_mul_card_commute hgM (S.clPre_le_QG W) hfix
  have hinj : Nat.card {q : G // q ∈ S.clPre W ∧ q * g = g * q} ≤
      Nat.card {q : G // q ∈ S.QG ∧ q * θ = θ * q ∧ q * g = g * q} :=
    Nat.card_le_card_of_injective
      (fun q => ⟨q.1, q.2.1.1, hcomm q.1 q.2.1.1 (Submodule.mem_inf.mp (hW.le q.2.1.2)).1, q.2.2⟩)
      (fun q q' h => Subtype.ext (Subtype.mk.inj h))
  have hpow : 2 ^ m ≤ 2 ^ finrank (ZMod 2) W := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

namespace S2Data

variable (D : S2Data S)

local notation "ρV" => D.resC

private theorem two_mul_finrank_fixSpace_resC_le (c : D.Cbar) :
    2 * finrank (ZMod 2) (fixSpace (ρV c)) ≤
      finrank (ZMod 2) (fixSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  obtain ⟨ι, hι⟩ : ∃ ι : (fixSpace (ρV c) × fixSpace (ρV c)) →ₗ[ZMod 2] S.Qt,
      ι = (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt) ∘ₗ
        ((fixSpace (ρV c)).subtype.prodMap (fixSpace (ρV c)).subtype) := ⟨_, rfl⟩
  have happ : ∀ u v : fixSpace (ρV c),
      ι (u, v) = D.coord ((u : Vt S D.g D.t), (v : Vt S D.g D.t)) := fun u v => by
    rw [hι]
    rfl
  have hinj : Function.Injective ι := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    obtain ⟨hu, hv⟩ :=
      Prod.mk.inj (D.coord.injective ((happ u v).symm.trans (h.trans (happ u' v'))))
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hv)
  have hle : LinearMap.range ι ≤ fixSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rintro _ ⟨⟨u, v⟩, rfl⟩
    refine mem_fixSpace.mpr ?_
    have e1 := happ u v
    have e2 := D.Cbar_apply_coord c (u : Vt S D.g D.t) (v : Vt S D.g D.t)
    have e3 : ρV c (u : Vt S D.g D.t) = u := mem_fixSpace.mp u.2
    have e4 : ρV c (v : Vt S D.g D.t) = v := mem_fixSpace.mp v.2
    exact ((congrArg _ e1).trans (e2.trans (congrArg D.coord (Prod.ext e3 e4)))).trans e1.symm
  calc 2 * finrank (ZMod 2) (fixSpace (ρV c))
      = finrank (ZMod 2) (fixSpace (ρV c) × fixSpace (ρV c)) := by
        rw [Module.finrank_prod, two_mul]
    _ = finrank (ZMod 2) (LinearMap.range ι) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ _ := Submodule.finrank_mono hle

private theorem resC_mul_pow_eq_one_iff_mem_QG {a b : G} (haM : a ∈ S.M) (hbM : b ∈ S.M)
    (hsa : S.ρ ⟨a, haM⟩ ∈ D.Cbar) (hsb : S.ρ ⟨b, hbM⟩ ∈ D.Cbar) (n : ℕ) :
    (ρV ⟨_, hsa⟩ * ρV ⟨_, hsb⟩) ^ n = 1 ↔ (a * b) ^ n ∈ S.QG := by
  refine (D.resC_mul_pow_eq_one_iff ⟨_, hsa⟩ ⟨_, hsb⟩ n).trans ?_
  show (S.ρ ⟨a, haM⟩ * S.ρ ⟨b, hbM⟩) ^ n = 1 ↔ _
  rw [← map_mul, ← map_pow, S.ρ_eq_one_iff]
  rfl

theorem card_centralizer_theta_ge {a b g : G} (haM : a ∈ S.M) (hbM : b ∈ S.M)
    (haU : D.IsUInv (S.ρ ⟨a, haM⟩)) (hbU : D.IsUInv (S.ρ ⟨b, hbM⟩))
    (h3 : orderOf (a * b) = 3) (hgM : g ∈ S.M) (hg2 : g ^ 2 = 1)
    (hgθ : g * (a * b) = (a * b) * g) :
    2 ^ (S.width - 4) ≤
      Nat.card {q : G // q ∈ S.QG ∧ q * (a * b) = (a * b) * q ∧ q * g = g * q} := by
  obtain ⟨hsa, hρa⟩ := haU
  obtain ⟨hsb, hρb⟩ := hbU
  have hθM : a * b ∈ S.M := S.M.mul_mem haM hbM
  have hθ : S.ρ ⟨a * b, hθM⟩ = S.ρ ⟨a, haM⟩ * S.ρ ⟨b, hbM⟩ := by
    rw [← map_mul]
    rfl
  have hθ3 : (a * b) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (a * b)
    rwa [h3] at this
  have hab3 : (ρV ⟨_, hsa⟩ * ρV ⟨_, hsb⟩) ^ 3 = 1 :=
    (D.resC_mul_pow_eq_one_iff_mem_QG haM hbM hsa hsb 3).mpr (by rw [hθ3]; exact S.QG.one_mem)
  have hab1 : ρV ⟨_, hsa⟩ * ρV ⟨_, hsb⟩ ≠ 1 := by
    intro h
    have h1 : (a * b) ^ 1 ∈ S.QG :=
      (D.resC_mul_pow_eq_one_iff_mem_QG haM hbM hsa hsb 1).mp (by rw [pow_one]; exact h)
    rw [pow_one] at h1
    have h4 := orderOf_dvd_of_pow_eq_one (S.pow_four_eq_one h1)
    rw [h3] at h4
    omega
  obtain ⟨hF, -⟩ := exists_siegel_of_pow_three D.QV_nondegenerate hρa hρb hab3 hab1
  rw [D.finrank_Vt] at hF
  have hU : 2 * finrank (ZMod 2) (fixSpace (ρV ⟨_, hsa⟩ * ρV ⟨_, hsb⟩)) ≤
      finrank (ZMod 2) (fixSpace ((S.ρ ⟨a * b, hθM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
    have hcoe : ((((⟨_, hsa⟩ : D.Cbar) * (⟨_, hsb⟩ : D.Cbar) : D.Cbar) :
        S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = (S.ρ ⟨a * b, hθM⟩ : S.O) := by
      rw [hθ]
      rfl
    have h1 := D.two_mul_finrank_fixSpace_resC_le
      ((⟨_, hsa⟩ : D.Cbar) * (⟨_, hsb⟩ : D.Cbar))
    rw [hcoe, map_mul] at h1
    exact h1
  have hgθ' : (S.ρ ⟨g, hgM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (S.ρ ⟨a * b, hθM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (S.ρ ⟨a * b, hθM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (S.ρ ⟨g, hgM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have h : (⟨g, hgM⟩ : S.M) * ⟨a * b, hθM⟩ = ⟨a * b, hθM⟩ * ⟨g, hgM⟩ := Subtype.ext hgθ
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h]
  refine two_pow_le_card_of_finrank hgM hg2
    (U := fixSpace ((S.ρ ⟨a * b, hθM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) (fun u hu => ?_)
    (fun q hq hfix => mul_comm_of_cl_mem_fixSpace hθM hθ3 hq hfix) (m := S.width - 4) (by omega)
  rw [mem_fixSpace] at hu ⊢
  have h := LinearEquiv.congr_fun hgθ' u
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hu] at h
  exact h.symm

end S2Data

end CFSG.GF2Type.Smith1980Orth

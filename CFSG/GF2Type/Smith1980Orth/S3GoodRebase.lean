module

public import CFSG.GF2Type.Smith1980Orth.S2Seven
public import CFSG.GF2Type.Smith1980Orth.S3GoodLin
public import CFSG.LargeExtraspecial.S14SMELocal
public import CFSG.Sporadic.ThSchreier.Row
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.Fischer.NoF25.Local
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.PSL10Fix
public import CFSG.LargeExtraspecial.S12InspUse
public import CFSG.LargeExtraspecial.S14C12Lit
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
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
  CFSG.Open
open CFSG.ClassicalGroups.Orthogonal (eichler HypPair)
open TauCeti.QuadraticMap (orthogonalGroup)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private instance instFiniteDimensionalVtGood (g : G) (t : S.O) :
    FiniteDimensional (ZMod 2) (Vt S g t) :=
  Module.Finite.of_finite

namespace S2Data

structure Rebase (D : S2Data S) where
  g₁ : G
  hg₁ : g₁ * S.z * g₁⁻¹ = D.g * S.z * D.g⁻¹
  hcl : S.cl (g₁⁻¹ * S.z * g₁) = D.coord (aV D.good.ht, 0)
  P : HypPair D.QV
  hP : P.e = aV D.good.ht

namespace Rebase

variable {D : S2Data S} (T : Rebase D)

@[expose] def c : G := T.g₁⁻¹ * S.z * T.g₁

theorem cl_c : S.cl T.c = D.coord (aV D.good.ht, 0) := T.hcl

theorem g₁_conj_mem : T.g₁ * S.z * T.g₁⁻¹ ∈ S.QG := T.hg₁ ▸ D.good.H.conj_mem

theorem g₁_conj_ne : T.g₁ * S.z * T.g₁⁻¹ ≠ S.z := T.hg₁ ▸ D.good.H.conj_ne

theorem Qa_g₁ : S.Qa T.g₁ = S.Qa D.g := S.Qa_eq_of_conj_eq T.hg₁

theorem Lbar_g₁ : S.Lbar T.g₁ = S.Lbar D.g := S.Lbar_eq_of_conj_eq T.hg₁

theorem z_mem_Qa : S.z ∈ S.Qa T.g₁ := S.z_mem_Qa T.g₁_conj_mem T.g₁_conj_ne

theorem c_mem_QG : T.c ∈ S.QG := (SME.mem_Qa_iff S T.g₁ S.z).mp T.z_mem_Qa

theorem c_ne_z : T.c ≠ S.z := by
  intro h
  apply T.g₁_conj_ne
  have h' : T.g₁⁻¹ * S.z * T.g₁ = S.z := h
  have h2 : T.g₁ * S.z = S.z * T.g₁ := by
    calc T.g₁ * S.z = T.g₁ * (T.g₁⁻¹ * S.z * T.g₁) := by rw [h']
      _ = S.z * T.g₁ := by group
  calc T.g₁ * S.z * T.g₁⁻¹ = S.z * T.g₁ * T.g₁⁻¹ := by rw [h2]
    _ = S.z := by group

theorem c_ne_one : T.c ≠ 1 := by
  intro h
  apply S.z_ne_one
  have h' : T.g₁⁻¹ * S.z * T.g₁ = 1 := h
  calc S.z = T.g₁ * (T.g₁⁻¹ * S.z * T.g₁) * T.g₁⁻¹ := by group
    _ = 1 := by rw [h']; group

theorem c_eq : T.g₁⁻¹ * S.z * T.g₁⁻¹⁻¹ = T.c := by
  rw [inv_inv]
  rfl

theorem z_mem_Qa_inv : S.z ∈ S.Qa T.g₁⁻¹ :=
  S.z_mem_Qa (g := T.g₁⁻¹) (by rw [T.c_eq]; exact T.c_mem_QG) (by rw [T.c_eq]; exact T.c_ne_z)

theorem conj_mem_M_iff {n : G} : T.g₁ * n * T.g₁⁻¹ ∈ S.M ↔ n * T.c = T.c * n := by
  rw [S.mem_M_iff]
  constructor
  · intro h
    calc n * T.c = T.g₁⁻¹ * (T.g₁ * n * T.g₁⁻¹ * S.z) * T.g₁ := by unfold c; group
      _ = T.g₁⁻¹ * (S.z * (T.g₁ * n * T.g₁⁻¹)) * T.g₁ := by rw [h]
      _ = T.c * n := by unfold c; group
  · intro h
    calc T.g₁ * n * T.g₁⁻¹ * S.z = T.g₁ * (n * T.c) * T.g₁⁻¹ := by unfold c; group
      _ = T.g₁ * (T.c * n) * T.g₁⁻¹ := by rw [h]
      _ = S.z * (T.g₁ * n * T.g₁⁻¹) := by unfold c; group

@[expose] def H : Subgroup G := S.M ⊓ S.M.comap (MulAut.conj T.g₁).toMonoidHom

theorem mem_H {n : G} : n ∈ T.H ↔ n ∈ S.M ∧ T.g₁ * n * T.g₁⁻¹ ∈ S.M := Iff.rfl

theorem mem_H_iff {n : G} : n ∈ T.H ↔ n ∈ S.M ∧ n * T.c = T.c * n := by
  rw [mem_H, T.conj_mem_M_iff]

theorem mem_H_of_QG {y : G} (hy : y ∈ S.QG) (hyc : y * T.c = T.c * y) : y ∈ T.H :=
  T.mem_H_iff.mpr ⟨S.QG_le_M hy, hyc⟩

theorem comm_c_of_mem_H {n : G} (hn : n ∈ T.H) : n * T.c = T.c * n :=
  (T.mem_H_iff.mp hn).2

theorem z_mem_H : S.z ∈ T.H :=
  T.mem_H_of_QG S.z_mem_QG (S.z_comm_QG T.c_mem_QG).symm

@[expose] noncomputable def Psi : T.H →* S.O :=
  S.ρ.comp (((MulAut.conj T.g₁).toMonoidHom.comp T.H.subtype).codRestrict S.M (fun n => n.2.2))

theorem Psi_apply (n : T.H) : T.Psi n = S.ρ ⟨T.g₁ * (n : G) * T.g₁⁻¹, n.2.2⟩ := rfl

theorem Psi_mem_Mbar (n : T.H) : T.Psi n ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem Psi_z : T.Psi ⟨S.z, T.z_mem_H⟩ = 1 := by
  rw [Psi_apply]
  exact (S.ρ_eq_one_iff _).mpr T.g₁_conj_mem

theorem Psi_eq_of_cl_eq {a b : T.H} (ha : (a : G) ∈ S.QG) (hb : (b : G) ∈ S.QG)
    (h : S.cl a = S.cl b) : T.Psi a = T.Psi b := by
  rcases (S.cl_eq_cl_iff ha hb).mp h with h1 | h1
  · rw [show b = a from Subtype.ext h1]
  · have : b = a * ⟨S.z, T.z_mem_H⟩ := Subtype.ext h1
    rw [this, map_mul, T.Psi_z, mul_one]

theorem exists_Phi : ∃ Φ : S.Qt → S.O, ∀ (y : G) (hyQ : y ∈ S.QG) (hy : y ∈ T.H),
    Φ (S.cl y) = T.Psi ⟨y, hy⟩ := by
  classical
  refine ⟨fun w => if h : ∃ yh : T.H, (yh : G) ∈ S.QG ∧ S.cl yh = w then T.Psi h.choose else 1,
    fun y hyQ hy => ?_⟩
  have h : ∃ yh : T.H, (yh : G) ∈ S.QG ∧ S.cl yh = S.cl y := ⟨⟨y, hy⟩, hyQ, rfl⟩
  dsimp only
  rw [dif_pos h]
  exact T.Psi_eq_of_cl_eq h.choose_spec.1 hyQ h.choose_spec.2

@[expose] noncomputable def Phi : S.Qt → S.O := Classical.choose T.exists_Phi

theorem Phi_cl {y : G} (hyQ : y ∈ S.QG) (hy : y ∈ T.H) : T.Phi (S.cl y) = T.Psi ⟨y, hy⟩ :=
  Classical.choose_spec T.exists_Phi y hyQ hy

@[expose] noncomputable def perp : Submodule (ZMod 2) S.Qt :=
  LinearMap.ker (S.q.polarBilin (S.cl T.c))

theorem mem_perp {w : S.Qt} : w ∈ T.perp ↔ polar S.q (S.cl T.c) w = 0 := by
  rw [perp, LinearMap.mem_ker, polarBilin_apply_apply]

theorem exists_pre {w : S.Qt} (hw : w ∈ T.perp) :
    ∃ y : G, ∃ _ : y ∈ S.QG, ∃ _ : y ∈ T.H, S.cl y = w := by
  obtain ⟨y, hyQ, rfl⟩ := S.exists_cl w
  have hc := (S.polar_cl_eq_zero_iff T.c_mem_QG hyQ).mp (T.mem_perp.mp hw)
  exact ⟨y, hyQ, T.mem_H_of_QG hyQ hc.symm, rfl⟩

theorem Phi_mul {w w' : S.Qt} (hw : w ∈ T.perp) (hw' : w' ∈ T.perp) :
    T.Phi (w + w') = T.Phi w * T.Phi w' := by
  obtain ⟨y, hyQ, hy, rfl⟩ := T.exists_pre hw
  obtain ⟨y', hy'Q, hy', rfl⟩ := T.exists_pre hw'
  have e : (⟨y * y', T.H.mul_mem hy hy'⟩ : T.H) = ⟨y, hy⟩ * ⟨y', hy'⟩ := rfl
  rw [← S.cl_mul hyQ hy'Q, T.Phi_cl (S.QG.mul_mem hyQ hy'Q) (T.H.mul_mem hy hy'),
    T.Phi_cl hyQ hy, T.Phi_cl hy'Q hy', e, map_mul]

theorem Phi_zero : T.Phi 0 = 1 := by
  rw [← S.cl_one, T.Phi_cl S.QG.one_mem T.H.one_mem]
  exact map_one T.Psi

theorem Phi_mem_Lbar {w : S.Qt} (hw : w ∈ T.perp) : T.Phi w ∈ S.Lbar D.g := by
  obtain ⟨y, hyQ, hy, rfl⟩ := T.exists_pre hw
  rw [T.Phi_cl hyQ hy, T.Psi_apply, ← T.Lbar_g₁]
  have hQa : T.g₁ * y * T.g₁⁻¹ ∈ S.Qa T.g₁ := by
    rw [SME.mem_Qa_iff, show T.g₁⁻¹ * (T.g₁ * y * T.g₁⁻¹) * T.g₁ = y by group]
    exact hyQ
  exact S.ρ_mem_Lbar (y := T.g₁ * y * T.g₁⁻¹) (Subgroup.mem_inf.mpr ⟨hQa, hy.2⟩)

theorem Phi_eq_one_iff {w : S.Qt} (hw : w ∈ T.perp) :
    T.Phi w = 1 ↔ w ∈ S.clSub (S.QG ⊓ S.Qa T.g₁⁻¹) := by
  obtain ⟨y, hyQ, hy, rfl⟩ := T.exists_pre hw
  have hiff : T.Phi (S.cl y) = 1 ↔ y ∈ S.Qa T.g₁⁻¹ := by
    rw [T.Phi_cl hyQ hy, T.Psi_apply, S.ρ_eq_one_iff, SME.mem_Qa_iff, inv_inv]
  rw [hiff]
  constructor
  · intro h
    exact S.cl_mem_clSub ⟨hyQ, h⟩ hyQ
  · intro h
    obtain ⟨y', ⟨hy'Q, hy'a⟩, -, hy'cl⟩ := S.mem_clSub_iff.mp h
    have hza : S.z ∈ S.Qa T.g₁⁻¹ := T.z_mem_Qa_inv
    rcases (S.cl_eq_cl_iff hy'Q hyQ).mp hy'cl with h1 | h1
    · rw [h1]
      exact hy'a
    · rw [h1]
      exact (S.Qa T.g₁⁻¹).mul_mem hy'a hza

theorem exists_Phi_eq {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar D.g) : ∃ w ∈ T.perp, T.Phi w = ℓ := by
  rw [← T.Lbar_g₁, S.mem_Lbar_iff] at hℓ
  obtain ⟨x, hxL, rfl⟩ := hℓ
  have hxQ : T.g₁⁻¹ * (x : G) * T.g₁ ∈ S.QG := (SME.mem_Qa_iff S T.g₁ x).mp hxL.1
  have hxM : (x : G) ∈ S.M := x.2
  have hyH : T.g₁⁻¹ * (x : G) * T.g₁ ∈ T.H := by
    refine T.mem_H.mpr ⟨S.QG_le_M hxQ, ?_⟩
    rw [show T.g₁ * (T.g₁⁻¹ * (x : G) * T.g₁) * T.g₁⁻¹ = x by group]
    exact hxM
  refine ⟨S.cl (T.g₁⁻¹ * (x : G) * T.g₁), ?_, ?_⟩
  · rw [T.mem_perp, S.polar_cl_eq_zero_iff T.c_mem_QG hxQ]
    exact (T.mem_H_iff.mp hyH).2.symm
  · rw [T.Phi_cl hxQ hyH, T.Psi_apply]
    congr 1
    exact Subtype.ext (by group)

theorem Phi_conj (n : T.H) {w : S.Qt} (hw : w ∈ T.perp) :
    (S.ρ ⟨n, n.2.1⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ T.perp ∧
      T.Phi ((S.ρ ⟨n, n.2.1⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = T.Psi n * T.Phi w * (T.Psi n)⁻¹ := by
  obtain ⟨y, hyQ, hy, rfl⟩ := T.exists_pre hw
  have hnyQ : (n : G) * y * (n : G)⁻¹ ∈ S.QG := S.conj_mem_QG n.2.1 hyQ
  have hnyH : (n : G) * y * (n : G)⁻¹ ∈ T.H := T.H.mul_mem (T.H.mul_mem n.2 hy) (T.H.inv_mem n.2)
  rw [S.ρ_cl _ hyQ]
  refine ⟨?_, ?_⟩
  · rw [T.mem_perp, S.polar_cl_eq_zero_iff T.c_mem_QG hnyQ]
    exact (T.comm_c_of_mem_H hnyH).symm
  · rw [T.Phi_cl hnyQ hnyH, T.Phi_cl hyQ hy]
    have e : (⟨(n : G) * y * (n : G)⁻¹, hnyH⟩ : T.H) = n * ⟨y, hy⟩ * n⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]

theorem polar_cl_c_coord (u v : Vt S D.g D.t) :
    polar S.q (S.cl T.c) (D.coord (u, v)) = D.betaV (aV D.good.ht) v := by
  rw [T.cl_c, D.polar_coord]
  simp

theorem coord_mem_perp_iff (u v : Vt S D.g D.t) :
    D.coord (u, v) ∈ T.perp ↔ D.betaV (aV D.good.ht) v = 0 := by
  rw [T.mem_perp, T.polar_cl_c_coord]

theorem betaV_aV (x : Vt S D.g D.t) : D.betaV (aV D.good.ht) x = polar D.QV T.P.e x := by
  rw [T.hP, D.polar_QV]

theorem betaV_aV_perp (τ : T.P.perp) : D.betaV (aV D.good.ht) (τ : Vt S D.g D.t) = 0 := by
  rw [T.betaV_aV]
  exact (HypPair.mem_perp.mp τ.2).1

theorem clSub_eq_Pfst :
    S.clSub (S.QG ⊓ S.Qa T.g₁⁻¹) = D.Pfst (aV D.good.ht) :=
  D.clSub_QG_inf_Qa_eq_Pfst (h := T.g₁⁻¹) (by rw [T.c_eq]; exact T.c_mem_QG)
    (by rw [T.c_eq]; exact T.c_ne_z) (by rw [T.c_eq]; exact T.hcl)

theorem three_le_finrank_Z (hw6 : 6 ≤ S.width) : 3 ≤ finrank (ZMod 2) T.P.perp := by
  have h1 := HypPerp.finrank_perp_add_two T.P
  have h2 := D.finrank_Vt
  omega

@[expose] noncomputable def psi (τ : T.P.perp) : S.O :=
  T.Phi (D.coord (0, (τ : Vt S D.g D.t)))

theorem coord_zero_mem_perp (τ : T.P.perp) : D.coord (0, (τ : Vt S D.g D.t)) ∈ T.perp :=
  (T.coord_mem_perp_iff _ _).mpr (T.betaV_aV_perp τ)

theorem psi_mul (τ τ' : T.P.perp) : T.psi (τ + τ') = T.psi τ * T.psi τ' := by
  unfold psi
  rw [show D.coord (0, ((τ + τ' : T.P.perp) : Vt S D.g D.t)) =
      D.coord (0, (τ : Vt S D.g D.t)) + D.coord (0, (τ' : Vt S D.g D.t)) by
    rw [← map_add]
    congr 1
    simp]
  exact T.Phi_mul (T.coord_zero_mem_perp τ) (T.coord_zero_mem_perp τ')

theorem psi_zero : T.psi 0 = 1 := by
  unfold psi
  rw [show D.coord (0, (((0 : T.P.perp)) : Vt S D.g D.t)) = 0 by
    rw [show ((0 : T.P.perp) : Vt S D.g D.t) = 0 from rfl, Prod.mk_zero_zero, map_zero]]
  exact T.Phi_zero

theorem psi_mul_self (τ : T.P.perp) : T.psi τ * T.psi τ = 1 := by
  rw [← T.psi_mul, OrthoF2.vec_add_self, T.psi_zero]

theorem psi_mem_Lbar (τ : T.P.perp) : T.psi τ ∈ S.Lbar D.g :=
  T.Phi_mem_Lbar (T.coord_zero_mem_perp τ)

theorem psi_eq_one {τ : T.P.perp} (h : T.psi τ = 1) : τ = 0 := by
  have h1 := (T.Phi_eq_one_iff (T.coord_zero_mem_perp τ)).mp h
  rw [T.clSub_eq_Pfst, D.mem_Pfst_iff] at h1
  obtain ⟨u, e, -, hue⟩ := h1
  have h2 := (Prod.mk.inj (D.coord.injective hue)).2
  have h3 : (τ : Vt S D.g D.t) = 0 := by
    refine HypPerp.eq_zero_of_mem_perp_of_mem_span T.P τ.2 ?_
    rw [h2, ← T.hP]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  exact Subtype.ext h3

theorem psi_injective {τ τ' : T.P.perp} (h : T.psi τ = T.psi τ') : τ = τ' := by
  have h1 : T.psi (τ + τ') = 1 := by
    rw [T.psi_mul, ← h, T.psi_mul_self]
  have h2 := T.psi_eq_one h1
  rw [eq_neg_of_add_eq_zero_left h2, OrthoF2.vec_neg]

end Rebase

end S2Data

end CFSG.GF2Type.Smith1980Orth

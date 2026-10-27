module

public import CFSG.ClassicalInvolution.Q3.ModelCenterClassical
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.LieType.Steinberg.Exceptional.Universal
public import CFSG.LieType.TitsSimplicity.Core
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Q3.ClassicalFundamentalModels
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.TitsSimplicity
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.Blueprint.Chevalley

theorem centerExp_adjoint (τ : Tag) (F : Type) [Field F] [Finite F] :
    CenterExp (↥(adjointGroup τ F)) 0 := by
  intro z hz
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  rw [hz]
  exact one_pow _

section Minuscule

theorem diagOp_pow {k : Type*} [Field k] {d : ℕ} (f : Fin d → k) (m : ℕ) :
    (diagOp f) ^ m = diagOp (f ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, diagOp_one]
  | succ m ih => rw [pow_succ, pow_succ, ih, diagOp_mul]

theorem endo_pow {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type) [Field k]
    (g : hV.minGroup k) (m : ℕ) : hV.endo k (g ^ m) = (hV.endo k g) ^ m := by
  induction m with
  | zero => exact hV.endo_one k
  | succ m ih => rw [pow_succ, hV.endo_mul, ih, pow_succ]

theorem pow_eq_one_of_mem_iSup_torus {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type)
    [Field k] [Finite k] {j : ℕ} (hk : Nat.card k = 2 ^ j + 1) {g : hV.minGroup k}
    (hg : g ∈ ⨆ i, hV.torus k i) : g ^ (2 ^ j) = 1 := by
  obtain ⟨μ, hμ⟩ := hV.exists_diagOp_of_mem_iSup_torus k hg
  obtain ⟨ν, hν⟩ := hV.exists_diagOp_of_mem_iSup_torus k (inv_mem hg)
  have hμν : μ * ν = 1 := by
    apply diagOp_injective
    rw [← diagOp_mul, ← hμ, ← hν, hV.endo_mul_inv, diagOp_one]
  have : Fintype k := Fintype.ofFinite k
  have hμk : μ ^ (2 ^ j) = 1 := by
    funext a
    have ha : μ a ≠ 0 := by
      intro h0
      have h1 := congrFun hμν a
      rw [Pi.mul_apply, h0, zero_mul] at h1
      exact zero_ne_one h1
    have h1 := FiniteField.pow_card_sub_one_eq_one (μ a) ha
    rw [Fintype.card_eq_nat_card, hk, Nat.add_sub_cancel] at h1
    simpa using h1
  apply hV.endo_injective k
  rw [endo_pow, hμ, diagOp_pow, hμk, diagOp_one, hV.endo_one]

theorem centerExp_minuscule {τ : Tag} {D : MinData τ} (hV : D.Valid)
    (hA : TauCeti.IsFiniteType τ.cartan) (k : Type) [Field k] [Finite k] {j : ℕ}
    (hk : Nat.card k = 2 ^ j + 1)
    (hct : IsCTGroupDatum (coxeterMatrix (hV.minDatum hA k).isFiniteType).toCoxeterSystem
      (weylAction (hV.minDatum hA k).isFiniteType) (hV.minDatum hA k).roots
      (hV.minDatum hA k).rootGroup (hV.nm k) (hV.torus k))
    (hext : SteinbergExtras (hV.minDatum hA k) (hV.nm k) (hV.torus k))
    (hBU : BruhatExtras (hV.minDatum hA k) (hV.torus k)) :
    CenterExp (hV.minGroup k) j := by
  intro z hz
  have h1 := (center_eq_normalCore_borel hct hext hBU) ▸ hz
  exact pow_eq_one_of_mem_iSup_torus hV k hk (normalCore_borel_le_iSup hct hBU h1)

variable (k : Type) [Field k] [Finite k] {j : ℕ} (hk : Nat.card k = 2 ^ j + 1)
include hk

theorem centerExp_e6 : CenterExp ↥(e6Data_valid.minGroup k) j :=
  centerExp_minuscule e6Data_valid isFiniteType_cartan_E6 k hk (e6Datum_isCTGroupDatum k)
    (e6Datum_steinbergExtras k) (e6Datum_bruhatExtras k)

theorem centerExp_e7 : CenterExp ↥(e7Data_valid.minGroup k) j :=
  centerExp_minuscule e7Data_valid isFiniteType_cartan_E7 k hk (e7Datum_isCTGroupDatum k)
    (e7Datum_steinbergExtras k) (e7Datum_bruhatExtras k)

end Minuscule

section TwistedE6

open CFSG.LieType.Steinberg.TwistedE6

theorem centerExp_fixedGroup {k : Type} [Field k] [Finite k] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) {j : ℕ} (hk : Nat.card k = 2 ^ j + 1) :
    CenterExp (fixedGroup k θ) j := by
  intro z hz
  have hct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  have h1 := (center_eq_normalCore_borel hct (twistedDatum_steinbergExtras θ hθ)
    (twistedDatum_bruhatExtras θ)) ▸ hz
  have hzT : z ∈ ⨆ i, hHat k θ i := normalCore_borel_le_iSup hct (twistedDatum_bruhatExtras θ) h1
  have hle : (⨆ i, hHat k θ i : Subgroup (fixedGroup k θ)) ≤
      (⨆ a, e6Data_valid.torus k a).comap (fixedGroup k θ).subtype :=
    iSup_le fun i x hx => hHatE_le_iSup_torus θ i (Subgroup.mem_subgroupOf.mp hx)
  have hzE := Subgroup.mem_comap.mp (hle hzT)
  exact Subtype.ext (pow_eq_one_of_mem_iSup_torus e6Data_valid k hk hzE)

end TwistedE6

end CFSG.ClassicalInvolution.Q3

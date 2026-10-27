module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95UD
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Glue
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Two
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.NatModZ
public import CFSG.GH74.GLS.IVK.Statements.Sec11
public import CFSG.GH74.GLS.LU.Local.A3Reduce2
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBFixed
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Walter.J1

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Transport

variable {p f : ℕ} {K : Type} [Field K]

theorem ivk95_hyp_false (hud : UnitaryFieldData p f K) (hp : p ≠ 2) {r ε : ℕ}
    (hdim : 2 * r + ε = 4 ∨ 2 * r + ε = 5) {J : Type} [Group J] [Finite J]
    (θ : J ≃* hypPSU hud r ε) {z : J} (hcfg : Ivk95Cfg z) : False := by
  classical
  have : Finite K := hud.finite
  have : Finite (hypPSU hud r ε) := inferInstance
  have hcP : Ivk95Cfg (θ z) := hcfg.of_equiv θ
  have hinj := hypIota_injective hud r ε
  have hz2 : orderOf (hypIota hud r ε (θ z)) = 2 := by
    rw [orderOf_injective (hypIota hud r ε) hinj, MulEquiv.orderOf_eq]
    exact hcfg.ord
  obtain ⟨T, hT⟩ := QuotientGroup.mk_surjective (hypIota hud r ε (θ z))
  have hKP : Ez (θ z) ≤ centralizer ({θ z} : Set (hypPSU hud r ε)) := Ez_le_centralizer (θ z)
  have hX : CFSG.Assembly.IsComponentOf (Ez (θ z)) (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj (θ z))) := by
    rw [fixedSubgroup_conj]
    exact (isComponentOf_iff_isComponent_subgroupOf hKP).2 hcP.isComponent
  have hKc := key_component hud r ε (MulAut.conj (θ z)) (MulAut.conj (hypIota hud r ε (θ z)))
    (fun y => by simp [MulAut.conj_apply]) hX
  have hT' : QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε)) T =
      hypIota hud r ε (θ z) := hT
  have hrange : ∀ d ∈ projSpecial hud (hypForm hud r ε), ∃ c : hypPSU hud r ε,
      hypIota hud r ε c = d := by
    intro d hd
    obtain ⟨c, hc⟩ := (hypModelEquiv hud).surjective ⟨d, hd⟩
    exact ⟨c, by rw [hypIota_apply, hc]⟩
  refine ivk95_unitary_false (h := hud) (B := hypForm hud r ε) hp ?_ (hypForm_isSymm hud)
    (hypForm_separatingLeft hud) (T := T) ?_ (K' := (Ez (θ z)).map (hypIota hud r ε)) ?_ ?_ ?_
    ?_ ?_ ?_
  · rw [UnitaryHigher.finrank_hypIndex_fun]
    exact hdim
  · rw [hT]
    exact hz2
  · rw [hT']
    exact hKc
  · rw [hT]
    exact Subgroup.mem_map_of_mem _ hcP.mem
  · rintro _ ⟨y, hy, rfl⟩ hv
    rw [hT]
    have h1 : y * y = 1 := hinj (by rw [map_mul, hv, map_one])
    rcases hcP.uniq y hy h1 with rfl | rfl
    · left
      exact map_one _
    · right
      rfl
  · intro d hd hdz k hk
    obtain ⟨c, rfl⟩ := hrange d hd
    rw [hT] at hdz
    have hcz : c * θ z = θ z * c := hinj (by rw [map_mul, map_mul]; exact hdz)
    obtain ⟨y, hy, rfl⟩ := hk
    refine ⟨c * y * c⁻¹, hcP.conj_mem c hcz y hy, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · intro a b ha hb ha2 hb2 hab ha1 hb1 hne hac hbc
    obtain ⟨a₀, rfl⟩ := hrange a ha
    obtain ⟨b₀, rfl⟩ := hrange b hb
    have ha₀ : a₀ * a₀ = 1 := hinj (by rw [map_mul, ha2, map_one])
    have hb₀ : b₀ * b₀ = 1 := hinj (by rw [map_mul, hb2, map_one])
    have ha₀1 : a₀ ≠ 1 := fun h1 => ha1 (by rw [h1, map_one])
    have hb₀1 : b₀ ≠ 1 := fun h1 => hb1 (by rw [h1, map_one])
    refine hcP.false_of_two_involutions (a := a₀) (b := b₀)
      (orderOf_eq_prime (by rw [← pow_two] at ha₀; exact ha₀) ha₀1)
      (orderOf_eq_prime (by rw [← pow_two] at hb₀; exact hb₀) hb₀1)
      (hinj (by rw [map_mul, map_mul]; exact hab)) (fun h1 => hne (by rw [h1]))
      (fun k hk => hinj (by rw [map_mul, map_mul]; exact hac _ (Subgroup.mem_map_of_mem _ hk)))
      (fun k hk => hinj (by rw [map_mul, map_mul]; exact hbc _ (Subgroup.mem_map_of_mem _ hk)))
  · by_contra hcon
    apply hcP.not_solvable
    refine Group.isSolvable_of_comm fun x y => ?_
    apply Subtype.ext
    by_contra hne
    refine hcon ⟨hypIota hud r ε x, Subgroup.mem_map_of_mem _ x.2, hypIota hud r ε y,
      Subgroup.mem_map_of_mem _ y.2, fun h1 => hne (hinj ?_)⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact h1

end Transport

end CFSG.GH74.GLS.IVK.Proofs2

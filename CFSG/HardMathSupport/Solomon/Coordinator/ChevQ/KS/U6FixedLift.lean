module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Dickson.I271.Support.Action
import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

theorem uniqComp_lift {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K) {a : X} (ha : a ∈ Subgroup.normalizer (K : Set X))
    {T : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hT : GLAPComponent 3 (fixSubgroup (actHom K ⟨a, ha⟩)) T)
    (hu : ∀ L : Subgroup (↥K ⧸ Subgroup.center ↥K),
      GLAPComponent 3 (fixSubgroup (actHom K ⟨a, ha⟩)) L → L = T)
    (hTq : CFSG.Open.IsQuasisimple ↥T) :
    ∃ J₀ : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₀ ∧
      (∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → J = J₀) ∧
      CFSG.Open.IsQuasisimple ↥J₀ ∧
      Nonempty ((↥J₀ ⧸ Subgroup.center ↥J₀) ≃* (↥T ⧸ Subgroup.center ↥T)) := by
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have hαβ : ∀ k : ↥K, π (K.normalizerMonoidHom ⟨a, ha⟩ k) =
      actHom K ⟨a, ha⟩ (π k) := fun k => (actHom_mk K ⟨a, ha⟩ k).symm
  obtain ⟨J₁, hJ₁, hJ₁map⟩ :=
    exists_glaPComponent_map_fixSubgroup π hker (K.normalizerMonoidHom ⟨a, ha⟩)
      (actHom K ⟨a, ha⟩) hαβ hπ Nat.prime_three hT
  subst hJ₁map
  have hC : fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩) =
      (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K :=
    fixSubgroup_normalizerMonoidHom ha
  have hJ₁' : GLAPComponent 3 ((K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K) J₁ := by
    rw [← hC]
    exact hJ₁
  have hcov : (π.subgroupMap J₁).ker ≤ Subgroup.center ↥J₁ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ker_subgroupMap_le_center π hker J₁
  have hperf₁ : ⁅J₁, J₁⁆ = J₁ := glaPComponent_perfect hJ₁
  have hperf : Group.IsPerfect ↥J₁ := Subgroup.isPerfect_iff.2 hperf₁
  have hQ₁ : CFSG.IsQuasisimple ↥J₁ :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_central_cover (π.subgroupMap J₁)
      (MonoidHom.subgroupMap_surjective π J₁) hperf hcov
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hTq)
  have hQ₁' : CFSG.Open.IsQuasisimple ↥J₁ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQ₁
  let e₂ : ↥J₁ ≃* ↥(J₁.map K.subtype) := J₁.equivMapOfInjective K.subtype K.subtype_injective
  have hJ₀ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) (J₁.map K.subtype) := by
    have hc : ∀ y ∈ ((K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K) ⊓ K.subtype.ker,
        ∀ x ∈ (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K, x * y = y * x := by
      intro y hy x _
      have : y = 1 := Subtype.ext (MonoidHom.mem_ker.1 hy.2)
      rw [this, mul_one, one_mul]
    have h := glaPComponent_map_central Nat.prime_three K.subtype hc hJ₁'
    rwa [Subgroup.map_subgroupOf_eq_of_le
      (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K)] at h
  refine ⟨J₁.map K.subtype, hJ₀, fun J hJ => ?_, ?_, ?_⟩
  ·
    have hJK : J ≤ K := fun y hy => (Subgroup.mem_inf.1 (hJ.1 hy)).1
    have hJ' := glaPComponent_fixSubgroup Nat.prime_three ha hJ
    have hmap := glaPComponent_map_fixSubgroup π hker (K.normalizerMonoidHom ⟨a, ha⟩)
      (actHom K ⟨a, ha⟩) hαβ hπ Nat.prime_three hJ'
    have h1 : (J.subgroupOf K).map π = J₁.map π := hu _ hmap
    have h2 : J.subgroupOf K = J₁ :=
      CFSG.LocalAnalysis.GLTheoremA.glaPComponent_eq_of_map_eq_of_ker_le_center π hker hJ' hJ₁ h1
    calc J = (J.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hJK).symm
      _ = J₁.map K.subtype := by rw [h2]
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂ hQ₁'
  · obtain ⟨e₃⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
        hQ₁'.1 (π.subgroupMap J₁) (MonoidHom.subgroupMap_surjective π J₁) hcov
    exact ⟨(QuotientGroup.congr _ _ e₂.symm (Subgroup.map_center_eq e₂.symm)).trans e₃⟩

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrNormalClosure
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

namespace CFSG.ComponentClassification.UGSChain

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type*} [Group G]

theorem map_centralizer_singleton (φ : G ≃* G) (c : G) :
    (centralizer ({c} : Set G)).map φ.toMonoidHom = centralizer ({φ c} : Set G) := by
  ext z
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hz
    have h1 := congrArg φ hz
    rwa [map_mul, map_mul, φ.apply_symm_apply] at h1
  · intro hz
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply, hz]

theorem map_map_pPrimeCore (φ : G ≃* G) (J : Subgroup G) :
    ((pPrimeCore 2 J).map J.subtype).map φ.toMonoidHom =
      (pPrimeCore 2 (J.map φ.toMonoidHom)).map (J.map φ.toMonoidHom).subtype := by
  let e : J ≃* J.map φ.toMonoidHom := J.equivMapOfInjective φ.toMonoidHom φ.injective
  have hcomm : φ.toMonoidHom.comp J.subtype =
      (J.map φ.toMonoidHom).subtype.comp e.toMonoidHom := by
    ext j
    rfl
  rw [map_map, hcomm, ← map_map, pPrimeCore_map_iso 2 e]

variable [Finite G]

theorem map_gsFixedLayer (φ : G ≃* G) (X : Subgroup G) (t : G) :
    (gsFixedLayer X t).map φ.toMonoidHom = gsFixedLayer (X.map φ.toMonoidHom) (φ t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : (X ⊓ centralizer ({t} : Set G)).map φ.toMonoidHom =
      X.map φ.toMonoidHom ⊓ centralizer ({φ t} : Set G) := by
    rw [map_inf _ _ _ φ.injective, map_centralizer_singleton]
  let ψ : ↥(X ⊓ centralizer ({t} : Set G)) ≃*
      ↥(X.map φ.toMonoidHom ⊓ centralizer ({φ t} : Set G)) :=
    ((X ⊓ centralizer ({t} : Set G)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hY)
  have hcomm : φ.toMonoidHom.comp (X ⊓ centralizer ({t} : Set G)).subtype =
      (X.map φ.toMonoidHom ⊓ centralizer ({φ t} : Set G)).subtype.comp ψ.toMonoidHom := by
    ext y
    rfl
  rw [gsFixedLayer, gsFixedLayer, map_map, hcomm, ← map_map,
    FixedLayerPComponent.map_pLayer_mulEquiv 2 ψ]

end CFSG.ComponentClassification.UGSChain

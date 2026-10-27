module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumann
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellImage

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6 CFSG.Quasithin.BlueprintB2
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped LinearAlgebra.Projectivization

variable {H : Type*} [Group H] {k : Type*} [Field k]

namespace IsNatQuotSetting

variable {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

theorem V_le_R [Finite H] (h : IsNatQuotSetting R M V ρ φ) : V ≤ R := by
  have hVn : V.Normal := h.normal_V
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by
    have := h.reduced.2.2.1.2 (v : H) v.2
    apply Subtype.ext
    simpa using this⟩
  have h1 : V ≤ pCoreOf 2 (⊤ : Subgroup H) :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 V ⊤ le_top
      (by infer_instance) hV2
  exact h1.trans ((pCoreOf_two_le_of_isSylowTwoOf h.sylow).trans le_rfl)

variable [Finite H] [Finite k] [CharP k 2]

theorem NI_data (h : IsNatQuotSetting R M V ρ φ) (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    ∃ ℓ : ℙ k (Fin 2 → k),
      (elemThompsonIn 2 R).map ρ = rootGamma ℓ ∧ (elemBaumannIn 2 R).map ρ = rootGamma ℓ ∧
      (∀ v : V, φ v = 1 →
        (v : H) ∈ Subgroup.centralizer ((elemThompsonIn 2 R : Subgroup H) : Set H)) ∧
      (∀ w : Fin 2 → k, w ∈ ℓ.submodule ↔ ∃ v : V,
        (v : H) ∈ Subgroup.centralizer ((elemThompsonIn 2 R : Subgroup H) : Set H) ∧
          Multiplicative.toAdd (φ v) = w) ∧
      (V ⊓ Subgroup.centralizer ((elemThompsonIn 2 R : Subgroup H) : Set H)).relIndex V =
        Nat.card k ∧
      (∀ A ∈ elemThompsonFamily R 2,
        (A ⊓ Subgroup.centralizer ((V.subgroupOf R : Subgroup R) : Set R)).relIndex A ≤
          ((V.subgroupOf R) ⊓ Subgroup.centralizer (A : Set R)).relIndex (V.subgroupOf R)) := by
  classical
  have hVH := h.not_le_centralizer hJ
  have hVR : V ≤ R := h.V_le_R
  have hVn : V.Normal := h.normal_V
  obtain ⟨-, hCR, -, -, -, -, -⟩ := minimal_parabolic_reduced_module_Frattini_kernel_production
    h.sylow h.nonnormal h.le_M h.M_lt h.M_max h.reduced hVH
  have hRker := h.inf_ker_eq hVH
  set V' : Subgroup R := V.subgroupOf R with hV'
  have hV'n : V'.Normal := inferInstance
  have hV'e : IsElementaryAbelian 2 V' :=
    isElementaryAbelian_subgroupOf ((isElemAbelian_iff_isElementaryAbelian 2).mp h.reduced.2.2.1)
  let ρ' : R →* Gamma k := ρ.comp R.subtype
  let ι : V' ≃* V := Subgroup.subgroupOfEquivOfLe hVR
  let φ' : V' →* Multiplicative (Fin 2 → k) := φ.comp ι.toMonoidHom
  have hφ' : Function.Surjective φ' := h.φ_surj.comp ι.surjective
  have hφρ' : ∀ (r : R) (v v' : V'), (v' : R) = r * v * r⁻¹ →
      Multiplicative.toAdd (φ' v') =
        ((ρ' r : Gamma k) : Equiv.Perm (Fin 2 → k)) (Multiplicative.toAdd (φ' v)) := by
    intro r v v' hv
    exact h.φ_equiv (r : H) (ι v) (ι v') (congrArg Subtype.val hv)
  have hker' : ρ'.ker = Subgroup.centralizer (V' : Set R) := by
    ext r
    constructor
    · intro hr
      have hrN : (r : H) ∈ ρ.ker := hr
      have : (r : H) ∈ R ⊓ ρ.ker := ⟨r.2, hrN⟩
      rw [hRker, ← hCR] at this
      refine Subgroup.mem_centralizer_iff.mpr fun v' hv' => ?_
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp this.2 (v' : H) hv')
    · intro hr
      have hrC : (r : H) ∈ Subgroup.centralizer (V : Set H) := by
        refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have := Subgroup.mem_centralizer_iff.mp hr ⟨v, hVR hv⟩ (Subgroup.mem_subgroupOf.mpr hv)
        exact congrArg Subtype.val this
      have : (r : H) ∈ R ⊓ Subgroup.centralizer (V : Set H) := ⟨r.2, hrC⟩
      rw [hCR, ← hRker] at this
      exact this.2
  have hJ' : ⁅elemThompson R 2, V'⁆ ≠ ⊥ := by
    intro hbot
    apply hJ
    have : ⁅(elemThompson R 2).map R.subtype, V'.map R.subtype⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, hbot, Subgroup.map_bot]
    rwa [hV', Subgroup.map_subgroupOf_eq_of_le hVR] at this
  obtain ⟨ℓ, h1, h2, h3, h4, h5⟩ := natural_quotient_internal_Thompson_Baumann_image
    (R := R) h.sylow.2.1 V' hV'e ρ' φ' hφ' hφρ' hker' hJ'
  have hcent : ∀ v' : V', (v' : R) ∈ Subgroup.centralizer ((elemThompson R 2 : Subgroup R) : Set R) ↔
      ((v' : R) : H) ∈ Subgroup.centralizer ((elemThompsonIn 2 R : Subgroup H) : Set H) := by
    intro v'
    constructor
    · intro hv
      refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
      obtain ⟨j', hj', rfl⟩ := hj
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hv j' hj')
    · intro hv
      refine Subgroup.mem_centralizer_iff.mpr fun j' hj' => ?_
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hv (j' : H) ⟨j', hj', rfl⟩)
  have hι : ∀ v' : V', ((ι v' : V) : H) = ((v' : R) : H) := fun v' => rfl
  refine ⟨ℓ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold elemThompsonIn
    rw [Subgroup.map_map]
    exact h1
  · unfold elemBaumannIn
    rw [Subgroup.map_map]
    exact h2
  · intro v hv
    have := h3 (ι.symm v) (by simpa [φ'] using hv)
    exact (hcent (ι.symm v)).mp this
  · intro w
    rw [h4 w]
    constructor
    · rintro ⟨v', hv', hw⟩
      refine ⟨ι v', ?_, hw⟩
      exact (hcent v').mp hv'
    · rintro ⟨v, hv, hw⟩
      refine ⟨ι.symm v, (hcent (ι.symm v)).mpr hv, ?_⟩
      simpa [φ'] using hw
  · have hmap : (V' ⊓ Subgroup.centralizer ((elemThompson R 2 : Subgroup R) : Set R)).map R.subtype =
        V ⊓ Subgroup.centralizer ((elemThompsonIn 2 R : Subgroup H) : Set H) := by
      ext x
      constructor
      · rintro ⟨y, ⟨hyV, hyC⟩, rfl⟩
        exact ⟨hyV, (hcent ⟨y, hyV⟩).mp hyC⟩
      · rintro ⟨hxV, hxC⟩
        exact ⟨⟨x, hVR hxV⟩, ⟨Subgroup.mem_subgroupOf.mpr hxV,
          (hcent ⟨⟨x, hVR hxV⟩, Subgroup.mem_subgroupOf.mpr hxV⟩).mpr hxC⟩, rfl⟩
    have hV'map : V'.map R.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVR
    rw [← hmap, ← hV'map]
    rw [Subgroup.relIndex_map_map_of_injective _ _ R.subtype_injective]
    exact h5
  · intro A hA
    exact (natural_quotient_per_elementary V' hV'e ρ' φ' hφ' hφρ' hker' hA).1.le

end IsNatQuotSetting

end CFSG.QuasithinUnique.Setup.Campbell

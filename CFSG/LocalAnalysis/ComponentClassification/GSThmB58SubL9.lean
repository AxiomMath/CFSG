module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubDefs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace SubL9Aux

variable {G : Type*} [Group G] [Finite G]

theorem inf_oddCoreIn_eq {V W : Subgroup G} (hVW : V ≤ W) (hWN : W ≤ normalizer (V : Set G)) :
    V ⊓ oddCoreIn W = oddCoreIn V :=
  le_antisymm (B5a.inf_oddCoreIn_le_of_le hVW)
    (le_inf (map_subtype_le _) (B5a.oddCoreIn_le_of_le_normalizer hVW hWN))

theorem sup_oddCoreIn_inf {J V W : Subgroup G} (hJV : J ≤ V) (hVW : V ≤ W)
    (hWN : W ≤ normalizer (V : Set G)) : (J ⊔ oddCoreIn W) ⊓ V = J ⊔ oddCoreIn V := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxJ, hxV⟩ := mem_inf.mp hx
    obtain ⟨j, hj, o, ho, rfl⟩ := B5a.exists_mul_of_mem_sup_oddCoreIn (hJV.trans hVW) hxJ
    have hoV : o ∈ V := by
      have h1 := mul_mem (inv_mem (hJV hj)) hxV
      rwa [inv_mul_cancel_left] at h1
    have hoO : o ∈ oddCoreIn V := by
      rw [← inf_oddCoreIn_eq hVW hWN]
      exact mem_inf.mpr ⟨hoV, ho⟩
    exact mul_mem (mem_sup_left hj) (mem_sup_right hoO)
  · exact le_inf (sup_le_sup_left (B5a.oddCoreIn_le_of_le_normalizer hVW hWN) _)
      (sup_le hJV (map_subtype_le _))

theorem mem_normalizer_sup_oddCoreIn_iff {J V W : Subgroup G} (hJV : J ≤ V) (hVW : V ≤ W)
    (hWN : W ≤ normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    v ∈ normalizer ((J ⊔ oddCoreIn W : Subgroup G) : Set G) ↔
      v ∈ normalizer ((J ⊔ oddCoreIn V : Subgroup G) : Set G) := by
  constructor
  · intro hN
    rw [← sup_oddCoreIn_inf hJV hVW hWN]
    exact inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨hN, le_normalizer hv⟩)
  · intro hN
    have hO : v ∈ normalizer (oddCoreIn W : Set G) :=
      B5a.mem_normalizer_oddCoreIn (le_normalizer (hVW hv))
    have h1 := B5a.mem_normalizer_sup hN hO
    rwa [sup_assoc, sup_eq_right.mpr (B5a.oddCoreIn_le_of_le_normalizer hVW hWN)] at h1

theorem exists_sylow_subgroupOf {R M H : Subgroup G} (hRM : R ≤ M) (hMH : M ≤ H)
    (R₁ : Sylow 2 ↥M) (hR₁ : (R₁ : Subgroup ↥M) = R.subgroupOf M) :
    ∃ R' : Sylow 2 ↥(M.subgroupOf H),
      (R' : Subgroup _) = (R.subgroupOf H).subgroupOf (M.subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (R.subgroupOf M) := by
    rw [← hR₁]
    exact R₁.isPGroup'
  have hp : IsPGroup 2 R := h1.of_equiv (subgroupOfEquivOfLe hRM)
  have hp2 : IsPGroup 2 ((R.subgroupOf H).subgroupOf (M.subgroupOf H)) :=
    (hp.comap_subtype (K := H)).comap_subtype (K := M.subgroupOf H)
  have hidx : ¬ 2 ∣ ((R.subgroupOf H).subgroupOf (M.subgroupOf H)).index := by
    have h2 : ((R.subgroupOf H).subgroupOf (M.subgroupOf H)).index = (R.subgroupOf M).index :=
      relIndex_subgroupOf hMH
    rw [h2, ← hR₁]
    exact R₁.not_dvd_index
  exact ⟨hp2.toSylow hidx, IsPGroup.toSylow_coe _ _⟩

end SubL9Aux

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

private theorem fixedLayer_subJ (hc : h.SecCond y) :
    GSLit.fixedLayer (h.subJ y) (h.subB y) =
      (h.secImage y (GSLit.fixedLayer h.J h.B)).subgroupOf (h.secSubImg y) := by
  rw [← secFixedLayer_B hc]
  exact B5a.fixedLayer_subgroupOf (h.secImage_secJ0_le y) (h.secImage_B_le y)

private theorem oddCoreIn_normalizer_subB :
    oddCoreIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) =
      (oddCoreIn (normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓ h.secSubImg y)).subgroupOf
        (h.secSubImg y) := by
  rw [normalizer_subB, ← B5a.oddCoreIn_subgroupOf (inf_le_right :
    normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓ h.secSubImg y ≤ h.secSubImg y),
    inf_subgroupOf_right]

private theorem layer_normalizer_sub_eq (hc : h.SecCond y) :
    (h.secImage y h.V).subgroupOf (h.secSubImg y) ⊓
        normalizer ((GSLit.fixedLayer (h.subJ y) (h.subB y) ⊔
          oddCoreIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
            Set ↥(h.secSubImg y))) : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) =
      (h.secImage y h.V ⊓ normalizer ((h.secImage y (GSLit.fixedLayer h.J h.B) ⊔
        oddCoreIn (normalizer (h.secImage y h.B : Set (h.secBar y))) :
          Subgroup (h.secBar y)) : Set (h.secBar y))).subgroupOf (h.secSubImg y) := by
  have hJV : h.secImage y (GSLit.fixedLayer h.J h.B) ≤ h.secImage y h.V :=
    secImage_mono (B5a.fixedLayer_le_V h)
  have hVW : h.secImage y h.V ≤ normalizer (h.secImage y h.B : Set (h.secBar y)) := by
    rw [← layerIn_secW hc]
    exact map_subtype_le _
  have hWN : normalizer (h.secImage y h.B : Set (h.secBar y)) ≤
      normalizer (h.secImage y h.V : Set (h.secBar y)) := by
    rw [← layerIn_secW hc]
    exact OddQuot.le_normalizer_layerIn _
  have hVH : h.secImage y h.V ≤ h.secSubImg y := secImage_V_le hc
  have hJH : h.secImage y (GSLit.fixedLayer h.J h.B) ≤ h.secSubImg y := hJV.trans hVH
  have hOH : oddCoreIn (normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓ h.secSubImg y) ≤
      h.secSubImg y := (map_subtype_le _).trans inf_le_right
  have hinf : ∀ A C : Subgroup (h.secBar y), A.subgroupOf (h.secSubImg y) ⊓
      C.subgroupOf (h.secSubImg y) = (A ⊓ C).subgroupOf (h.secSubImg y) :=
    fun A C => (comap_inf _ _ _).symm
  rw [fixedLayer_subJ hc, oddCoreIn_normalizer_subB, ← subgroupOf_sup hJH hOH,
    ← subgroupOf_normalizer_eq (sup_le hJH hOH), hinf]
  congr 1
  ext v
  simp only [mem_inf]
  refine and_congr_right fun hv => ?_
  rw [SubL9Aux.mem_normalizer_sup_oddCoreIn_iff hJV (le_inf hVW hVH) (inf_le_left.trans hWN) hv,
    SubL9Aux.mem_normalizer_sup_oddCoreIn_iff hJV hVW hWN hv]

theorem SecCond.sylow_layer_subBar (hc : h.SecCond y) :
    ∃ R : Subgroup ↥(h.secSubImg y),
      R ≤ h.subS y ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ∧
      R ≤ (h.secImage y h.V).subgroupOf (h.secSubImg y) ⊓
        normalizer ((GSLit.fixedLayer (h.subJ y) (h.subB y) ⊔
          oddCoreIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
            Set ↥(h.secSubImg y))) : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ∧
      ∃ R' : Sylow 2 ↥((h.secImage y h.V).subgroupOf (h.secSubImg y) ⊓
        normalizer ((GSLit.fixedLayer (h.subJ y) (h.subB y) ⊔
          oddCoreIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
            Set ↥(h.secSubImg y))) : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))),
        (R' : Subgroup _) = R.subgroupOf
          ((h.secImage y h.V).subgroupOf (h.secSubImg y) ⊓
          normalizer ((GSLit.fixedLayer (h.subJ y) (h.subB y) ⊔
            oddCoreIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
              Set ↥(h.secSubImg y))) : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) := by
  have key := sylow_layer_secBar hc
  rw [layerIn_secW hc, secFixedLayer_B hc] at key
  obtain ⟨R, hRQ, hRM, R₁, hR₁⟩ := key
  rw [layer_normalizer_sub_eq hc, normalizer_subB]
  refine ⟨R.subgroupOf (h.secSubImg y), fun r hr => ?_,
    fun r hr => mem_subgroupOf.mpr (hRM (mem_subgroupOf.mp hr)),
    SubL9Aux.exists_sylow_subgroupOf hRM (inf_le_left.trans (secImage_V_le hc)) R₁ hR₁⟩
  obtain ⟨h1, h2⟩ := mem_inf.mp (hRQ (mem_subgroupOf.mp hr))
  exact mem_inf.mpr ⟨mem_subgroupOf.mpr h1, mem_subgroupOf.mpr h2⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB

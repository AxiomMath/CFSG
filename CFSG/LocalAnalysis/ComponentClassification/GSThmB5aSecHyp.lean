module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecSyl

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace B5a

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_coreActionKernel {K : Subgroup G} {x : G}
    (hx : x ∈ K ⊔ coreActionKernel K) : ∃ k ∈ K, ∃ c ∈ coreActionKernel K, k * c = x := by
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  have hCN : coreActionKernel K ≤ normalizer (K : Set G) := fun c hc =>
    (mem_coreActionKernel.mp hc).1
  have hxN : x ∈ normalizer (K : Set G) := (sup_le hKN hCN) hx
  have h1 : (K ⊔ coreActionKernel K).subgroupOf (normalizer (K : Set G)) =
      K.subgroupOf (normalizer (K : Set G)) ⊔
        (coreActionKernel K).subgroupOf (normalizer (K : Set G)) := by
    apply map_injective (normalizer (K : Set G)).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hKN hCN), map_subgroupOf_eq_of_le hKN,
      map_subgroupOf_eq_of_le hCN]
  have h2 : (⟨x, hxN⟩ : ↥(normalizer (K : Set G))) ∈
      ((K.subgroupOf (normalizer (K : Set G)) ⊔
        (coreActionKernel K).subgroupOf (normalizer (K : Set G)) : Subgroup _) : Set _) := by
    rw [SetLike.mem_coe, ← h1]
    exact hx
  have : (K.subgroupOf (normalizer (K : Set G))).Normal := normal_in_normalizer
  rw [normal_mul] at h2
  obtain ⟨k, hk, c, hc, hkc⟩ := h2
  exact ⟨k, hk, c, hc, congrArg Subtype.val hkc⟩

theorem nonempty_quotient_equiv_of_surjective {G' : Type*} [Group G'] {T B : Subgroup G}
    {T' B' : Subgroup G'} [(B.subgroupOf T).Normal] [(B'.subgroupOf T').Normal]
    (f : ↥T →* ↥T') (hf : Function.Surjective f)
    (hker : ∀ t : ↥T, ((f t : ↥T') : G') ∈ B' ↔ (t : G) ∈ B) :
    Nonempty (↥T' ⧸ B'.subgroupOf T' ≃* ↥T ⧸ B.subgroupOf T) := by
  set g := (QuotientGroup.mk' (B'.subgroupOf T')).comp f with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgk : g.ker = B.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf, hker]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hgk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)).symm⟩

theorem mem_normalizer_subgroupOf_iff {K G₀ : Subgroup G} (hK : K ≤ G₀) {g : ↥G₀} :
    g ∈ normalizer ((K.subgroupOf G₀ : Subgroup ↥G₀) : Set ↥G₀) ↔
      (g : G) ∈ normalizer (K : Set G) := by
  rw [← subgroupOf_normalizer_eq hK]
  rfl

end B5a

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

@[expose] def SecSylow (h : Hyp52 X) (y : X) : Prop :=
  ∃ R : Sylow 2 ↥(centralizer (h.secImage y (zpowers h.a) : Set (h.secBar y)) ⊓
      normalizer (h.secImage y (GSLit.fixedLayer h.J (h.secB0 y)) : Set (h.secBar y))),
    (R : Subgroup _) = (h.secImage y h.S).subgroupOf
      (centralizer (h.secImage y (zpowers h.a) : Set (h.secBar y)) ⊓
        normalizer (h.secImage y (GSLit.fixedLayer h.J (h.secB0 y)) : Set (h.secBar y)))

theorem a_mem_secG0 (hQ : h.Q ≤ h.secG0 y) : h.a ∈ h.secG0 y := hQ h.a_mem_Q

theorem mem_secG0_of_sq_mem (hy2 : y ^ 2 ∈ h.T) : y ∈ h.secG0 y := by
  have hx2 : y ^ 2 ∈ normalizer (h.B : Set X) := (mem_inf.mp (mem_inf.mp hy2).1).2
  rw [mem_normalizer_iff]
  intro z
  rw [secB0, mem_inf, mem_inf, mem_conjugate_iff, mem_conjugate_iff]
  constructor
  · rintro ⟨hy1, hy2⟩
    refine ⟨hy2, ?_⟩
    rw [show y * (y * z * y⁻¹) * y⁻¹ = y ^ 2 * z * (y ^ 2)⁻¹ by rw [pow_two]; group]
    exact (mem_normalizer_iff.mp hx2 z).mp hy1
  · rintro ⟨hy1, hy2⟩
    refine ⟨?_, hy1⟩
    rw [show y * (y * z * y⁻¹) * y⁻¹ = y ^ 2 * z * (y ^ 2)⁻¹ by rw [pow_two]; group] at hy2
    exact (mem_normalizer_iff.mp hx2 z).mpr hy2

instance secB0_subgroupOf_P0_normal (h : Hyp52 X) (y : X) :
    ((h.secB0 y).subgroupOf (h.S ⊓ h.secG0 y ⊓ h.P)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (le_inf (le_inf ((h.secB0_le_B y).trans
    (h.B_le.trans inf_le_left)) (h.secB0_le_G0 y)) h.secB0_le_P)).mpr
    (inf_le_left.trans inf_le_right)

theorem mem_coreActionKernel_of_secMk_secJ0 {g : X} (hgG : g ∈ h.secG0 y)
    (hgJ : g ∈ normalizer (h.J : Set X))
    (hg : h.secMk y ⟨g, hgG⟩ ∈ coreActionKernel (h.secImage y (h.secJ0 y))) :
    g ∈ coreActionKernel h.J := by
  have : Group.IsPerfect (h.secJ0 y) := isPerfect_secJ0
  have heK0 : g ∈ coreActionKernel (h.secJ0 y) :=
    mem_coreActionKernel_of_secMk (h.secJ0_le_G0 y) ((h.secJ0_le y).trans inf_le_right) hgG
      (mem_normalizer_secJ0 hgG hgJ) hg
  refine B5a.mem_coreActionKernel_of_sup hgJ
    ((GSLit.fixedLayer_le_inf h.J (h.secB0 y)).trans inf_le_left) secJ0_sup_core.1
    fun t ht => ?_
  have h1 : t⁻¹ * g⁻¹ * t * g ∈ oddCoreIn (h.secJ0 y) := (mem_coreActionKernel.mp heK0).2 t ht
  rw [secJ0_sup_core.2] at h1
  exact (mem_inf.mp h1).2

theorem secImage_P :
    h.secImage y h.S ⊓ coreActionKernel (h.secImage y (h.secJ0 y)) = h.secImage y h.P := by
  apply le_antisymm
  · rintro z ⟨hzS, hzK⟩
    obtain ⟨g, hg, rfl⟩ := mem_map.mp hzS
    have hgS : (g : X) ∈ h.S := hg
    have hgJ : (g : X) ∈ coreActionKernel h.J :=
      mem_coreActionKernel_of_secMk_secJ0 g.2 ((mem_inf.mp (h.S_le hgS)).2) hzK
    exact mem_map_of_mem _ (show g ∈ h.P.subgroupOf (h.secG0 y) from mem_inf.mpr ⟨hgS, hgJ⟩)
  · rintro z hz
    obtain ⟨g, hg, rfl⟩ := mem_map.mp hz
    obtain ⟨hgS, hgJ⟩ := mem_inf.mp (show (g : X) ∈ h.P from hg)
    refine mem_inf.mpr ⟨mem_map_of_mem _ (show g ∈ h.S.subgroupOf (h.secG0 y) from hgS), ?_⟩
    exact secMk_mem_coreActionKernel (h.secJ0_le_G0 y) g.2 (mem_coreActionKernel_secJ0 g.2 hgJ)

namespace SecCond

variable (hc : h.SecCond y)
include hc

theorem secImage_Q :
    h.secImage y h.S ⊓ normalizer (h.secImage y h.B : Set (h.secBar y)) = h.secImage y h.Q := by
  rw [hc.normalizer_secB, ← secImage_inf ((h.secB0_le_B y).trans (h.B_le.trans inf_le_left))]

theorem secImage_T :
    (h.secImage y h.S ⊓ normalizer (h.secImage y h.B : Set (h.secBar y))) ⊓
      (h.secImage y h.S ⊓ coreActionKernel (h.secImage y (h.secJ0 y))) = h.secImage y h.T := by
  rw [hc.secImage_Q, secImage_P, ← secImage_inf ((h.secB0_le_B y).trans h.B_le_Q)]

theorem secA_mem_sup_iff :
    hc.secA ∈ h.secImage y h.K ⊔ coreActionKernel (h.secImage y h.K) ↔
      h.a ∈ h.K ⊔ coreActionKernel h.K := by
  have hKG : h.K ≤ h.secG0 y := K_le_secG0
  have hKC : h.K ≤ centralizer (h.secB0 y : Set X) := K_le_centralizer_secB0
  have : Group.IsPerfect h.K :=
    B5a.isPerfect_of_isPComponent_subgroupOf h.isPComponent_K.1 h.isPComponent_K.2
  constructor
  · intro ha
    obtain ⟨k₁, hk₁, c₁, hc₁, hkc⟩ := B5a.exists_mul_of_mem_sup_coreActionKernel ha
    obtain ⟨k, hk, rfl⟩ := mem_map.mp hk₁
    have hkK : (k : X) ∈ h.K := hk
    have hcG : (k : X)⁻¹ * h.a ∈ h.secG0 y := mul_mem (inv_mem k.2) hc.a_mem_G0
    have hc1 : h.secMk y ⟨(k : X)⁻¹ * h.a, hcG⟩ = c₁ := by
      rw [eq_inv_mul_of_mul_eq hkc, ← map_inv, ← map_mul]
      rfl
    have hcN : (k : X)⁻¹ * h.a ∈ normalizer (h.K : Set X) := by
      have h3 : h.secMk y ⟨(k : X)⁻¹ * h.a, hcG⟩ ∈
          normalizer ((h.K.subgroupOf (h.secG0 y)).map (h.secMk y) : Set (h.secBar y)) := by
        rw [hc1]
        exact (mem_coreActionKernel.mp hc₁).1
      have : Group.IsNilpotent ↥(h.secMk y).ker := (h.isPGroup_ker_secMk y).isNilpotent
      have : Group.IsPerfect (h.K.subgroupOf (h.secG0 y)) :=
        Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKG).symm.toMonoidHom)
          (subgroupOfEquivOfLe hKG).symm.surjective
      have h4 := B5a.mem_normalizer_of_map
        (le_centralizer_iff.mp (h.subgroupOf_le_centralizer_ker y hKC)) h3
      exact (B5a.mem_normalizer_subgroupOf_iff hKG).mp h4
    have hcK : (k : X)⁻¹ * h.a ∈ coreActionKernel h.K :=
      mem_coreActionKernel_of_secMk hKG hKC hcG hcN (by rw [hc1]; exact hc₁)
    have hak : h.a = (k : X) * ((k : X)⁻¹ * h.a) := by group
    rw [hak]
    exact mul_mem (mem_sup_left hkK) (mem_sup_right hcK)
  · intro ha
    obtain ⟨k, hk, c, hcK, hkc⟩ := B5a.exists_mul_of_mem_sup_coreActionKernel ha
    have hkG := hKG hk
    have hcG : c ∈ h.secG0 y := by
      have hc' : c = k⁻¹ * h.a := by rw [← hkc]; group
      rw [hc']
      exact mul_mem (inv_mem hkG) hc.a_mem_G0
    have h1 : hc.secA = h.secMk y ⟨k, hkG⟩ * h.secMk y ⟨c, hcG⟩ := by
      rw [← map_mul]
      exact congrArg _ (Subtype.ext hkc.symm)
    rw [h1]
    exact mul_mem (mem_sup_left (mem_map_of_mem _
      (show (⟨k, hkG⟩ : ↥(h.secG0 y)) ∈ h.K.subgroupOf (h.secG0 y) from hk)))
      (mem_sup_right (secMk_mem_coreActionKernel hKG hcG hcK))

end SecCond

@[expose] noncomputable def secHyp52 (hc : h.SecCond y) (hSyl : h.SecSylow y) :
    Hyp52 (h.secBar y) where
  a := hc.secA
  J := h.secImage y (h.secJ0 y)
  S := h.secImage y h.S
  B := h.secImage y h.B
  K := h.secImage y h.K
  x := hc.secX
  kProper := SecCond.kProper_secBar
  kGroup_normalizer := hc.kGroup_normalizer_secB
  normalizer_ne_top := hc.normalizer_secB_ne_top
  orderOf_a := hc.orderOf_secA
  J_le := hc.secJ_le
  isPComponent_J := hc.isPComponent_secJ
  smallType := SecCond.smallType_secJ
  S_le := hc.secS_le
  S_sylow := by
    have hcen : centralizer (h.secImage y (zpowers h.a) : Set (h.secBar y)) =
        centralizer ({hc.secA} : Set (h.secBar y)) := by
      rw [secImage_zpowers hc.a_mem_G0, centralizer_zpowers_eq]
    have hS := hSyl
    unfold SecSylow at hS
    rw [hcen] at hS
    exact hS
  B_le := SecCond.secB_le
  B_ne_bot := hc.secB_ne_bot
  a_mem_normalizer := hc.secA_mem_normalizer
  isComponent_bar := isComponent_secBar hc
  isStandard_bar := isStandard_secBar hc
  conjClosure_eq := conjClosure_secW hc
  commutator_eq := commutator_secW hc
  B_le_kernel := secB_le_kernel hc
  B_sylow_kernel := secB_sylow_kernel hc
  isoCorr_of_lt := hc.isoCorr_secBar
  x_mem := hc.secX_mem
  inf_conjugate_x := hc.secB_inf_conjugate
  x_sq_mem := hc.secX_sq_mem
  sylow_layer := sylow_layer_secBar hc
  isPComponent_K := isPComponent_secK hc (Or.inl rfl)
  layer_eq_K := (secImage_V hc).symm.trans (layerIn_secW hc).symm
  type_K := type_secK hc

section secHyp52

variable (hc : h.SecCond y) (hSyl : h.SecSylow y)

theorem secHyp52_J : (h.secHyp52 hc hSyl).J = h.secImage y (h.secJ0 y) := rfl

theorem secHyp52_S : (h.secHyp52 hc hSyl).S = h.secImage y h.S := rfl

theorem secHyp52_B : (h.secHyp52 hc hSyl).B = h.secImage y h.B := rfl

theorem secHyp52_K : (h.secHyp52 hc hSyl).K = h.secImage y h.K := rfl

theorem secHyp52_P : (h.secHyp52 hc hSyl).P = h.secImage y h.P := secImage_P

theorem secHyp52_Q : (h.secHyp52 hc hSyl).Q = h.secImage y h.Q := hc.secImage_Q

theorem secHyp52_T : (h.secHyp52 hc hSyl).T = h.secImage y h.T := hc.secImage_T

end secHyp52

end Hyp52

end CFSG.ComponentClassification.GSThmB

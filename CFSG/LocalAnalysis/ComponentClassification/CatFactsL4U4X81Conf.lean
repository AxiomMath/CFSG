module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Data
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalOrbits

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace X81

variable {G : Type*} [Group G]

theorem conj_mem_coreActionKernel {J : Subgroup G} {g x : G} (hg : g ∈ normalizer (J : Set G))
    (hx : x ∈ coreActionKernel J) : g * x * g⁻¹ ∈ coreActionKernel J := by
  obtain ⟨hxN, hxJ⟩ := mem_coreActionKernel.mp hx
  refine mem_coreActionKernel.mpr ⟨mul_mem (mul_mem hg hxN) (inv_mem hg), fun j hj => ?_⟩
  have hj' : g⁻¹ * j * g ∈ J := by
    have h := (mem_normalizer_iff.mp (inv_mem hg) j).mp hj
    rwa [inv_inv] at h
  have h1 := Walter.conj_mem_map_of_characteristic hg (hxJ _ hj')
  rwa [show g * ((g⁻¹ * j * g)⁻¹ * x⁻¹ * (g⁻¹ * j * g) * x) * g⁻¹ =
    j⁻¹ * (g * x * g⁻¹)⁻¹ * j * (g * x * g⁻¹) by group] at h1

theorem mem_normalizer_coreActionKernel {J : Subgroup G} {g : G}
    (hg : g ∈ normalizer (J : Set G)) :
    g ∈ normalizer ((coreActionKernel J : Subgroup G) : Set G) :=
  mem_normalizer_iff.mpr fun x => ⟨fun hx => conj_mem_coreActionKernel hg hx, fun hx => by
    have h := conj_mem_coreActionKernel (inv_mem hg) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h⟩

end X81

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

structure FStarFacts (d : Data H₁) : Prop where
  normal : (generalizedFitting H).Normal
  simple : IsSimpleGroup ↥(generalizedFitting H)
  centralizer_eq : centralizer (generalizedFitting H : Set H) = ⊥
  isComponent : IsComponent (generalizedFitting H)
  unique : ∀ L : Subgroup H, IsComponent L → L = generalizedFitting H
  J_le : h.J ≤ generalizedFitting H
  K_le_V : h.K ≤ h.V
  V_le : h.V ≤ generalizedFitting H
  K_ne : h.K ≠ generalizedFitting H
  a_mul_b : h.a * d.b = d.b * h.a
  b_mem : d.b ∈ coreActionKernel h.J
  K_le_C : h.K ≤ centralizer ({d.b} : Set H)
  isPComponent_K : IsPComponent 2 (h.K.subgroupOf (centralizer ({d.b} : Set H)))
  P_le : h.P ≤ centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J
  P_sylow : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J),
    (R : Subgroup _) = h.P.subgroupOf (centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J)

theorem generalizedFitting_normal' : (generalizedFitting H).Normal := by
  have := CFSG.LocalCores.layer_characteristic (G := H)
  have : (fittingSubgroup H).Normal := (CFSG.LocalCores.fitting_nilpotent (G := H)).2.1
  simp only [CFSG.generalizedFitting.eq_sup]
  infer_instance

theorem fstarFacts (d : Data H₁) : d.FStarFacts := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hF, hsimple, hC, hcomp, huniq⟩ := h.generalizedFitting_simple
  have hFn : (generalizedFitting H).Normal := generalizedFitting_normal'
  have hbB : d.b ∈ h.B := d.B_eq ▸ mem_zpowers d.b
  have hJF : h.J ≤ generalizedFitting H := hF ▸ B5a.le_conjClosure h.J (pLayer H 2)
  have hVF : h.V ≤ generalizedFitting H := by
    show layerIn (normalizer (h.B : Set H)) ≤ _
    rw [← h.conjClosure_eq]
    refine B5a.conjClosure_le ((GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_left.trans hJF))
      fun y _ => ?_
    rw [mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hFn.conj_mem x hx y, fun hx => by
      have := hFn.conj_mem _ hx y⁻¹
      rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this⟩
  have hNB : normalizer (h.B : Set H) = centralizer ({d.b} : Set H) := by
    rw [d.B_eq]
    exact normalizer_zpowers_eq_centralizer d.b_ord
  have hKC : h.K ≤ centralizer ({d.b} : Set H) := hNB ▸ h.isPComponent_K.1
  have hCa : centralizer ({h.a} : Set H) ≤ normalizer (h.J : Set H) :=
    (normal_subgroupOf_iff_le_normalizer h.J_le).mp H₁.J_normal
  have hSa : h.S ≤ centralizer ({h.a} : Set H) := h.S_le.trans inf_le_left
  have hPX : h.P ≤ centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J :=
    inf_le_inf_right _ hSa
  refine ⟨hFn, hsimple, ?_, hF ▸ hcomp, fun L hL => (huniq L hL).trans hF.symm, hJF,
    le_sup_left.trans h.layer_eq_K.le, hVF, ?_, (H₁.NP_eq.2.2 d.b hbB).symm, (h.B_le hbB).2, hKC,
    hNB ▸ h.isPComponent_K.2, hPX, ?_⟩
  · rw [hF]
    exact hC
  · intro hKF
    have hb : d.b ∈ centralizer (generalizedFitting H : Set H) := by
      rw [mem_centralizer_iff]
      intro m hm
      have hm' : m ∈ centralizer ({d.b} : Set H) := hKC (hKF ▸ hm)
      exact mem_centralizer_singleton_iff.mp hm'
    rw [hF, hC, mem_bot] at hb
    have := d.b_ord
    rw [hb, orderOf_one] at this
    exact absurd this (by norm_num)
  ·
    obtain ⟨R, hR⟩ := H₁.S_sylow_C
    have hSyl : ABGLocalTools.IsSylowOf 2 h.S (centralizer ({h.a} : Set H)) :=
      ⟨R, by rw [hR, map_subgroupOf_eq_of_le hSa]⟩
    have hle : centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J ≤
        centralizer ({h.a} : Set H) := inf_le_left
    have hnorm : centralizer ({h.a} : Set H) ≤
        normalizer ((centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J : Subgroup H) :
          Set H) := by
      intro g hg
      rw [mem_normalizer_iff]
      intro x
      have hk := X81.mem_normalizer_coreActionKernel (hCa hg)
      rw [mem_normalizer_iff] at hk
      simp only [mem_inf]
      exact and_congr ⟨fun hx => mul_mem (mul_mem hg hx) (inv_mem hg), fun hx => by
        have := mul_mem (mul_mem (inv_mem hg) hx) hg
        rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this⟩ (hk x)
    have h1 := hSyl.inf_of_le_normalizer hle hnorm
    have h2 : h.S ⊓ (centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J) = h.P := by
      rw [← inf_assoc, inf_eq_left.mpr hSa]
    rw [h2] at h1
    exact h1.exists_sylow_eq_subgroupOf

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTMem

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {Gh Zh : Subgroup Γ} {t : Γ}

@[expose] def litConj (Gh : Subgroup Γ) (t : Γ) (ht : t ∈ normalizer (Gh : Set Γ)) :
    ↥Gh ≃* ↥Gh where
  toFun x := ⟨t * x * t⁻¹, (mem_normalizer_iff.mp ht x).mp x.2⟩
  invFun x := ⟨t⁻¹ * x * t, by
    have h := (mem_normalizer_iff.mp (inv_mem ht) (x : Γ)).mp x.2
    simpa using h⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem litConj_coe (ht : t ∈ normalizer (Gh : Set Γ)) (x : ↥Gh) :
    ((litConj Gh t ht x : ↥Gh) : Γ) = t * x * t⁻¹ := rfl

theorem litConj_invol (ht : t ∈ normalizer (Gh : Set Γ)) (ht2 : t * t = 1) (x : ↥Gh) :
    litConj Gh t ht (litConj Gh t ht x) = x := by
  have ht2' : t⁻¹ * t⁻¹ = 1 := by
    rw [inv_eq_of_mul_eq_one_right ht2, ht2]
  ext
  simp only [litConj_coe]
  rw [show t * (t * ↑x * t⁻¹) * t⁻¹ = (t * t) * ↑x * (t⁻¹ * t⁻¹) by group, ht2, ht2']
  simp

theorem litConj_Z (ht : t ∈ normalizer (Gh : Set Γ)) (hZ : t ∈ normalizer (Zh : Set Γ)) :
    ∀ x ∈ Zh.subgroupOf Gh, litConj Gh t ht x ∈ Zh.subgroupOf Gh := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [litConj_coe]
  exact (Subgroup.mem_normalizer_iff.mp hZ (x : Γ)).mp hx

theorem lit_litTSub_eq [(Zh.subgroupOf Gh).Normal] (hZc : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x)
    (hZG : Zh ≤ Gh) (ht : t ∈ normalizer (Gh : Set Γ)) (hZ : t ∈ normalizer (Zh : Set Γ)) :
    litTSub (litConj Gh t ht) (Zh.subgroupOf Gh) =
      (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh).subgroupOf Gh := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hL : x ∈ litTSub (litConj Gh t ht) (Zh.subgroupOf Gh) ↔
      ((litConj Gh t ht x : ↥Gh) : Γ) * (x : Γ)⁻¹ ∈ Zh := by
    change litConj Gh t ht x * x⁻¹ ∈ Zh.subgroupOf Gh ↔
      ((litConj Gh t ht x : ↥Gh) : Γ) * (x : Γ)⁻¹ ∈ Zh
    rw [Subgroup.mem_subgroupOf]
    simp
  rw [hL, lit_mem_T_iff hZc hZG hZ x.2, litConj_coe, commutatorElement_def]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem lit_conj_ne (hZG : Zh ≤ Gh) (ht : t ∈ normalizer (Gh : Set Γ))
    (h8 : ∃ z ∈ Zh, ⁅z, t⁆ ≠ 1) : ∃ z ∈ Zh.subgroupOf Gh, litConj Gh t ht z ≠ z := by
  obtain ⟨z, hz, hcomm⟩ := h8
  refine ⟨⟨z, hZG hz⟩, hz, ?_⟩
  intro h
  have hz' : t * z * t⁻¹ = z := by
    have h' := congrArg (Subtype.val) h
    rwa [litConj_coe] at h'
  have htz : t * z = z * t := by
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [hz']
  exact hcomm (commutatorElement_eq_one_iff_mul_comm.mpr htz.symm)

end CFSG.OddStandard.HigherRank.YamadaG23

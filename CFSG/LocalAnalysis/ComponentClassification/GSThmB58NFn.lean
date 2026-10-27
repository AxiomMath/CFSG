module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3a

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

namespace Hyp52

variable (h : Hyp52 X)

theorem inf_coreActionKernel_le_B {M R : Subgroup X} (hR2 : IsPGroup 2 R) (hBR : h.B ≤ R)
    (hRN : R ≤ normalizer (M : Set X)) (hVM : h.V ≤ M) :
    R ⊓ coreActionKernel M ≤ h.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := R ⊓ coreActionKernel M with hUdef
  have hU2 : IsPGroup 2 U := hR2.to_le inf_le_left
  have hRU : R ≤ normalizer (U : Set X) := fun r hr => by
    rw [hUdef]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (mem_inf.mpr ⟨le_normalizer hr, normalizer_le_normalizer_coreActionKernel M (hRN hr)⟩)
  have hNUB : ∀ u ∈ U, u ∈ normalizer (h.B : Set X) → u ∈ h.B := by
    intro u hu huB
    obtain ⟨-, huK⟩ := mem_inf.mp hu
    have huVN : u ∈ normalizer (h.V : Set X) := le_normalizer_layerIn_self _ huB
    have huV : u ∈ coreActionKernel h.V := by
      refine ⟨huVN, fun v hv => ?_⟩
      have h1 : v⁻¹ * u⁻¹ * v * u ∈ oddCoreIn M := (mem_coreActionKernel.mp huK).2 v (hVM hv)
      have h4 : u⁻¹ * v * u ∈ h.V := by
        have h5 := (mem_normalizer_iff.mp (inv_mem huVN) v).mp hv
        simpa using h5
      have h2 : v⁻¹ * u⁻¹ * v * u ∈ h.V := by
        have h6 := h.V.mul_mem (h.V.inv_mem hv) h4
        simpa [mul_assoc] using h6
      exact inf_oddCoreIn_le hVM (mem_inf.mpr ⟨h2, h1⟩)
    obtain ⟨hBC, R', hR'⟩ := h.sylow_kernel
    have hle : h.B ⊔ zpowers u ≤ coreActionKernel h.V := sup_le hBC (zpowers_le.mpr huV)
    have hp : IsPGroup 2 ((h.B ⊔ zpowers u).subgroupOf (coreActionKernel h.V)) :=
      (IsPGroup.to_sup_of_normal_left' (B5a.isPGroup_B h)
        (hU2.to_le (zpowers_le.mpr hu)) (zpowers_le.mpr huB)).comap_subtype
    have hR'le : (R' : Subgroup _) ≤ (h.B ⊔ zpowers u).subgroupOf (coreActionKernel h.V) := by
      rw [hR']
      exact fun w hw => mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hw))
    have heq := R'.is_maximal' hp hR'le
    have h1 : (⟨u, hle (mem_sup_right (mem_zpowers u))⟩ : ↥(coreActionKernel h.V)) ∈
        (R' : Subgroup _) := by
      rw [← heq]
      exact mem_subgroupOf.mpr (mem_sup_right (mem_zpowers u))
    rw [hR'] at h1
    exact mem_subgroupOf.mp h1
  have hUBset : ((U ⊔ h.B : Subgroup X) : Set X) = (U : Set X) * (h.B : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U h.B (hBR.trans hRU)
  have hP2 : IsPGroup 2 ↥(U ⊔ h.B) :=
    IsPGroup.to_sup_of_normal_left' hU2 (B5a.isPGroup_B h) (hBR.trans hRU)
  set P := U ⊔ h.B with hPdef
  set B' := h.B.subgroupOf P with hB'def
  have hNB : normalizer (B' : Set ↥P) ≤ B' := by
    intro w hw
    have hwP : (w : X) ∈ ((U ⊔ h.B : Subgroup X) : Set X) := w.2
    rw [hUBset] at hwP
    obtain ⟨u, hu, b, hb, hub⟩ := hwP
    have hwB : (w : X) ∈ normalizer (h.B : Set X) := by
      rw [mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have h1 := (mem_normalizer_iff.mp hw ⟨z, mem_sup_right hz⟩).mp (mem_subgroupOf.mpr hz)
        exact mem_subgroupOf.mp h1
      · intro hz
        have hzP : z ∈ P := by
          have h2 : (w : X)⁻¹ * ((w : X) * z * (w : X)⁻¹) * w = z := by group
          rw [← h2]
          exact P.mul_mem (P.mul_mem (P.inv_mem w.2) (mem_sup_right hz)) w.2
        have h1 := (mem_normalizer_iff.mp hw ⟨z, hzP⟩).mpr (mem_subgroupOf.mpr hz)
        exact mem_subgroupOf.mp h1
    have huN : u ∈ normalizer (h.B : Set X) := by
      have h1 : u = (w : X) * b⁻¹ := by rw [← hub]; group
      rw [h1]
      exact mul_mem hwB (le_normalizer (inv_mem hb))
    have huB := hNUB u hu huN
    exact mem_subgroupOf.mpr (by rw [← hub]; exact mul_mem huB hb)
  have hBtop : B' = ⊤ := by
    by_contra hne
    have : Group.IsNilpotent ↥P := hP2.isNilpotent
    have hlt := Group.normalizerCondition_of_isNilpotent B' (lt_top_iff_ne_top.mpr hne)
    exact absurd hNB (not_le_of_gt hlt)
  intro u hu
  have h1 : (⟨u, mem_sup_left hu⟩ : ↥P) ∈ B' := by rw [hBtop]; exact mem_top _
  exact mem_subgroupOf.mp h1

theorem inf_coreActionKernel_le_secB0 {y : X} {M R : Subgroup X} (hR2 : IsPGroup 2 R)
    (hBR : h.B ≤ R) (hyR : y ∈ R) (hRN : R ≤ normalizer (M : Set X)) (hVM : h.V ≤ M) :
    R ⊓ coreActionKernel M ≤ h.secB0 y := by
  have hUB := h.inf_coreActionKernel_le_B hR2 hBR hRN hVM
  intro u hu
  refine mem_inf.mpr ⟨hUB hu, ?_⟩
  rw [mem_conjugate_iff]
  apply hUB
  obtain ⟨huR, huK⟩ := mem_inf.mp hu
  refine mem_inf.mpr ⟨R.mul_mem (R.mul_mem hyR huR) (R.inv_mem hyR), ?_⟩
  exact (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M (hRN hyR)) u).mp huK

theorem isSylowIn_inf_centralizer {y : X}
    (hSyl : Seven.IsSylowIn (h.S ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y))
    {M : Subgroup X} (hMG : M ≤ h.secG0 y)
    (hSN : h.S ⊓ h.secG0 y ≤ normalizer (M : Set X)) :
    Seven.IsSylowIn (h.S ⊓ h.secG0 y ⊓ (M ⊓ centralizer ({h.a} : Set X)))
      (M ⊓ centralizer ({h.a} : Set X)) := by
  set Y₁ := centralizer ({h.a} : Set X) ⊓ h.secG0 y ⊓ normalizer (M : Set X) with hY₁
  have hS₁ : Seven.IsSylowIn (h.S ⊓ h.secG0 y) Y₁ :=
    hSyl.of_le (le_inf hSyl.1 hSN) inf_le_left
  refine hS₁.inf_of_le_normalizer ?_ ?_
  · intro m hm
    obtain ⟨hmM, hma⟩ := mem_inf.mp hm
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hma, hMG hmM⟩, le_normalizer hmM⟩
  · intro x hx
    obtain ⟨hxaG, hxM⟩ := mem_inf.mp hx
    obtain ⟨hxa, -⟩ := mem_inf.mp hxaG
    exact Subgroup.inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨hxM, le_normalizer hxa⟩)

end Hyp52

end CFSG.ComponentClassification.GSThmB

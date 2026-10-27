module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingInheritance

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

theorem strong_embedding_involution_conjugate_in_overgroup
    {Y M : Subgroup G} (hY : IsStronglyEmbedded Y) (hYM : Y ≤ M)
    {x : G} (hxM : x ∈ M) (hx : IsInvolution x) :
    ∃ a : G, a ∈ M ∧ rightConjugateElem x a ∈ Y := by
  obtain ⟨S, hSY⟩ := hY.containsSylowTwo
  let SM : Sylow 2 M := S.subtype (hSY.trans hYM)
  let xM : M := ⟨x, hxM⟩
  have hxMI : IsInvolution xM := IsInvolution.subtype hx hxM
  obtain ⟨P, hxP⟩ := (isPGroup_zpowers_of_involution hxMI).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P SM
  have hconj : g * xM * g⁻¹ ∈ (SM : Subgroup M) := by
    rw [← hg]
    change g * xM * g⁻¹ ∈ (P : Subgroup M).map (MulAut.conj g).toMonoidHom
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
      (hxP (Subgroup.mem_zpowers xM))
  have hconjS : (g : G) * x * (g : G)⁻¹ ∈ (S : Subgroup G) := by
    change g * xM * g⁻¹ ∈ (SM : Subgroup M) at hconj
    rw [Sylow.coe_subtype] at hconj
    exact hconj
  exact ⟨(g : G)⁻¹, M.inv_mem g.property, by
    simpa only [rightConjugateElem, inv_inv] using hSY hconjS⟩

theorem strong_embedding_proper_overgroup {Y M : Subgroup G}
    (hY : IsStronglyEmbedded Y) (hYM : Y ≤ M) (hM : M ≠ ⊤) :
    IsStronglyEmbedded M := by
  refine ⟨hM, ?_, ?_⟩
  · obtain ⟨x, hxY, hx⟩ := hY.exists_involution
    exact ⟨x, hYM hxY, hx⟩
  · intro g hg x hxM hxright hx
    obtain ⟨v, hvM, hvx⟩ := Subgroup.mem_map.mp hxright
    change g⁻¹ * v * (g⁻¹)⁻¹ = x at hvx
    rw [inv_inv] at hvx
    change rightConjugateElem v g = x at hvx
    have hv : IsInvolution v := by
      have hv' : IsInvolution (rightConjugateElem x g⁻¹) :=
        isInvolution_rightConjugateElem hx
      have heq : rightConjugateElem x g⁻¹ = v := by
        rw [← hvx]
        simp only [rightConjugateElem, inv_inv]
        group
      exact heq ▸ hv'
    obtain ⟨a, haM, hxaY⟩ :=
      strong_embedding_involution_conjugate_in_overgroup hY hYM hxM hx
    obtain ⟨b, hbM, hvbY⟩ :=
      strong_embedding_involution_conjugate_in_overgroup hY hYM hvM hv
    have hmember : rightConjugateElem x a ∈ rightConjugate Y (b⁻¹ * g * a) := by
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨rightConjugateElem v b, hvbY, ?_⟩
      change (b⁻¹ * g * a)⁻¹ * rightConjugateElem v b *
        ((b⁻¹ * g * a)⁻¹)⁻¹ = rightConjugateElem x a
      rw [inv_inv]
      rw [← hvx]
      simp only [rightConjugateElem]
      group
    have hcY := hY.mem_of_involution_mem_rightConjugate hxaY hmember
      (isInvolution_rightConjugateElem hx)
    have hcM := hYM hcY
    have hgM := M.mul_mem (M.mul_mem hbM hcM) (M.inv_mem haM)
    apply hg
    convert hgM using 1
    group

omit [Finite G] [Finite Q] in
theorem odd_quotient_rightConjugate_map (f : G →* Q) (Y : Subgroup G) (g : G) :
    (rightConjugate Y g).map f = rightConjugate (Y.map f) (f g) := by
  rw [rightConjugate, Subgroup.conjBy, rightConjugate, Subgroup.conjBy,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  change f (g⁻¹ * x * (g⁻¹)⁻¹) = (f g)⁻¹ * f x * ((f g)⁻¹)⁻¹
  simp only [map_mul, map_inv]

theorem strong_embedding_image_of_contained_odd_kernel (f : G →* Q)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {Y : Subgroup G} (hY : IsStronglyEmbedded Y) (hker : f.ker ≤ Y) :
    IsStronglyEmbedded (Y.map f) := by
  have hpreimage : (Y.map f).comap f = Y := Subgroup.comap_map_eq_self hker
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hY.ne_top
    rw [← hpreimage, htop, Subgroup.comap_top]
  · obtain ⟨z, hzY, hz⟩ := hY.exists_involution
    exact ⟨f z, Subgroup.mem_map_of_mem f hzY, involution_image_of_odd_kernel f hodd hz⟩
  · intro qg hqg y hyY hyright hy
    obtain ⟨g, hg⟩ := hf qg
    obtain ⟨x, hxY, hx, hfx⟩ := involution_lift_in_subgroup_of_odd_kernel f hodd Y hy hyY
    have hkernelRight : f.ker ≤ rightConjugate Y g := by
      intro n hn
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨g * n * g⁻¹, hker ((inferInstance : f.ker.Normal).conj_mem n hn g), ?_⟩
      change g⁻¹ * (g * n * g⁻¹) * (g⁻¹)⁻¹ = n
      group
    have hxright : x ∈ rightConjugate Y g := by
      have hmapmem : f x ∈ (rightConjugate Y g).map f := by
        rw [odd_quotient_rightConjugate_map, hg, hfx]
        exact hyright
      change x ∈ ((rightConjugate Y g).map f).comap f at hmapmem
      rw [Subgroup.comap_map_eq_self hkernelRight] at hmapmem
      exact hmapmem
    exact hqg (hg ▸ Subgroup.mem_map_of_mem f
      (hY.mem_of_involution_mem_rightConjugate hxY hxright hx))

theorem strong_embedding_image_of_odd_kernel (f : G →* Q)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {Y : Subgroup G} (hY : IsStronglyEmbedded Y) (hproper : Y.map f ≠ ⊤) :
    IsStronglyEmbedded (Y.map f) := by
  let M : Subgroup G := Y ⊔ f.ker
  have hMproper : M ≠ ⊤ := by
    intro hM
    apply hproper
    have himage : M.map f = Y.map f := by
      rw [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq]
    rw [← himage, hM, Subgroup.map_top, MonoidHom.range_eq_top.mpr hf]
  have hM := strong_embedding_proper_overgroup hY (le_sup_left : Y ≤ M) hMproper
  have hquot := strong_embedding_image_of_contained_odd_kernel f hf hodd hM
    (le_sup_right : f.ker ≤ M)
  have himage : M.map f = Y.map f := by
    rw [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq]
  exact himage ▸ hquot

theorem strongly_embedded_proper_overgroup {Y M : Subgroup G}
    (hY : fusionStronglyEmbedded Y) (hYM : Y ≤ M) (hM : M ≠ ⊤) :
    fusionStronglyEmbedded M :=
  order_strong_embedding_of_native
    (strong_embedding_proper_overgroup (native_strong_embedding_of_order_conditions hY) hYM hM)

theorem strongly_embedded_odd_quotient_and_proper_overgroups
    (Y N : Subgroup G) [N.Normal] (hY : fusionStronglyEmbedded Y)
    (hNodd : Odd (Nat.card N)) (hproper : Y ⊔ N ≠ ⊤) :
    fusionStronglyEmbedded (Y.map (QuotientGroup.mk' N)) ∧
      ∀ M : Subgroup (G ⧸ N), Y.map (QuotientGroup.mk' N) ≤ M → M ≠ ⊤ →
        fusionStronglyEmbedded M := by
  let f := QuotientGroup.mk' N
  have hodd : Odd (Nat.card f.ker) := by
    simpa only [f, QuotientGroup.ker_mk'] using hNodd
  have himageproper : Y.map f ≠ ⊤ := by
    intro htop
    apply hproper
    have heq := Subgroup.comap_map_eq f Y
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at heq
    exact heq.symm
  have h := order_strong_embedding_of_native
    (strong_embedding_image_of_odd_kernel f (QuotientGroup.mk'_surjective N) hodd
      (native_strong_embedding_of_order_conditions hY) himageproper)
  exact ⟨h, fun M hle hM => strongly_embedded_proper_overgroup h hle hM⟩

end CFSG.ProperTwoGeneratedCore

module

public import CFSG.ClassicalInvolution.Asc77.AscSix69

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem conjSub_sup (h : G) (A B : Subgroup G) :
    conjSub h (A ⊔ B) = conjSub h A ⊔ conjSub h B :=
  Subgroup.map_sup _ _ _

theorem conjSub_normalizer (h : G) (C : Subgroup G) :
    conjSub h (Subgroup.normalizer (C : Set G)) = Subgroup.normalizer (conjSub h C : Set G) := by
  ext x
  rw [mem_conjSub_iff, mem_normalizer_conjSub_iff]

theorem conjSub_closure_pair (h : G) (x y : G) :
    conjSub h (Subgroup.closure ({x, y} : Set G)) =
      Subgroup.closure ({h * x * h⁻¹, h * y * h⁻¹} : Set G) := by
  unfold conjSub
  rw [MonoidHom.map_closure, Set.image_pair]
  simp [MulAut.conj_apply]

theorem conjSub_pairNormalizers (h : G) (K J : Subgroup G) (zK zJ : G) :
    conjSub h (pairNormalizers K J zK zJ) =
      pairNormalizers (conjSub h K) (conjSub h J) (h * zK * h⁻¹) (h * zJ * h⁻¹) := by
  unfold pairNormalizers
  rw [conjSub_sup, conjSub_inf, conjSub_inf, conjSub_normalizer, conjSub_closure_pair]

theorem aEmpty_conj (hΩ : ConjInvariant Ω) {K : Subgroup G} (hA : AEmpty Ω K) (h : G) :
    AEmpty Ω (conjSub h K) := by
  intro J' hJ' hJ'n zK' zJ' hzK' hzJ'
  have hK : conjSub h⁻¹ (conjSub h K) = K := conjSub_inv_conjSub h K
  have hJ : conjSub h⁻¹ J' ∈ omegaStarNbr Ω K := by
    have := omegaStarNbr_conj hΩ hJ' h⁻¹
    rwa [hK] at this
  have hJn : conjSub h⁻¹ J' ∉ omegaNbr Ω K := by
    intro hmem
    apply hJ'n
    have := omegaNbr_conj hΩ hmem h
    rwa [conjSub_conjSub_inv] at this
  have hzK : IsUniqueInvolution K (h⁻¹ * zK' * h⁻¹⁻¹) := by
    have := hzK'.conj h⁻¹
    rwa [hK] at this
  have hzJ : IsUniqueInvolution (conjSub h⁻¹ J') (h⁻¹ * zJ' * h⁻¹⁻¹) := hzJ'.conj h⁻¹
  obtain ⟨g, hg, hgK⟩ := hA _ hJ hJn _ _ hzK hzJ
  refine ⟨h * g * h⁻¹, ?_, ?_⟩
  · have h1 : h * g * h⁻¹ ∈ conjSub h (pairNormalizers K (conjSub h⁻¹ J') (h⁻¹ * zK' * h⁻¹⁻¹)
        (h⁻¹ * zJ' * h⁻¹⁻¹)) := conj_mem_conjSub hg
    rw [conjSub_pairNormalizers] at h1
    have e1 : h * (h⁻¹ * zK' * h⁻¹⁻¹) * h⁻¹ = zK' := by group
    have e2 : h * (h⁻¹ * zJ' * h⁻¹⁻¹) * h⁻¹ = zJ' := by group
    have e3 : conjSub h (conjSub h⁻¹ J') = J' := conjSub_conjSub_inv h J'
    rwa [e1, e2, e3] at h1
  · rw [show h * g * h⁻¹ = h * (g * h⁻¹) by group, conjSub_mul, conjSub_mul]
    have : conjSub h⁻¹ (conjSub h K) = K := hK
    rw [this, hgK, conjSub_conjSub_inv]

theorem aEmpty_forall_of_transitive (hΩ : ConjInvariant Ω) {K : Subgroup G}
    (hall : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hA : AEmpty Ω K) : ∀ J ∈ Ω, AEmpty Ω J := by
  intro J hJ
  obtain ⟨g, rfl⟩ := hall J hJ
  exact aEmpty_conj hΩ hA g

end CFSG.ClassicalInvolution.Asc77

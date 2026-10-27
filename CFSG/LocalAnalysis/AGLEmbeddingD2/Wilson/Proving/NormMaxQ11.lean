module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.HarithJ4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4TI
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Fusion
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.NormMax
public import CFSG.Sporadic.Bridge.J4Surj

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient
open Subgroup

theorem orderOf_nrm₂_pow_twenty :
    orderOf (nrm₂ ^ 20 : J) = 2 := by
  have hjN : (nrm₂ ^ 20 : J) ∈ Subgroup.normalizer (Q11 : Set J) :=
    (Subgroup.normalizer (Q11 : Set J)).pow_mem nrm₂_mem_normalizer 20
  have hjact : heisData.actMat ⟨nrm₂ ^ 20, hjN⟩ = -1 := by
    have h1 : (⟨nrm₂ ^ 20, hjN⟩ : Subgroup.normalizer (Q11 : Set J)) =
        (⟨nrm₂, nrm₂_mem_normalizer⟩ : Subgroup.normalizer (Q11 : Set J)) ^ 20 := rfl
    rw [h1, heisData.actMat_pow, actMat_nrm₂, J4Matrix_pow_twenty]
  have hj1 : (nrm₂ ^ 20 : J) ≠ 1 := by
    intro h
    have h1 : heisData.actMat ⟨nrm₂ ^ 20, hjN⟩ = 1 := by
      have : (⟨nrm₂ ^ 20, hjN⟩ : Subgroup.normalizer (Q11 : Set J)) = 1 := Subtype.ext h
      rw [this, heisData.actMat_one]
    rw [hjact] at h1
    have := congrFun (congrFun h1 0) 0
    revert this
    decide
  have hj2 : (nrm₂ ^ 20) ^ 2 = 1 := by
    rw [sq]
    exact (js_central_facts).1
  exact orderOf_eq_prime hj2 hj1

theorem normMax_Q11_of_hover
    (hover : ∀ T : Subgroup J,
      Subgroup.normalizer ((Q11Sylow : Subgroup J) : Set J) ⊓ Subgroup.centralizer {nrm₂ ^ 20} < T →
        T ≤ Subgroup.centralizer {nrm₂ ^ 20} →
        Subgroup.normalizer ((Q11Sylow : Subgroup J) : Set J) ⊔ T = ⊤) :
    NormMax (Q11Sylow : Subgroup J) := by
  have hN : Nat.card (normalizer ((Q11Sylow : Subgroup J) : Set J) : Subgroup J) = 319440 := by
    rw [Q11Sylow_coe, card_normalizer_Q11]
    norm_num
  have hR : Nat.card (Q11Sylow : Subgroup J) = 1331 := by
    rw [Q11Sylow_coe, card_Q11]
    norm_num
  have hTI : ∀ g : J, g ∉ Subgroup.normalizer ((Q11Sylow : Subgroup J) : Set J) →
      (Q11Sylow : Subgroup J) ⊓ (Q11Sylow : Subgroup J).map (MulAut.conj g).toMonoidHom = ⊥ := by
    intro g hg
    rw [Q11Sylow_coe] at hg ⊢
    exact TI_Q11 g hg
  have htN : (nrm₂ ^ 20 : J) ∈ Subgroup.normalizer ((Q11Sylow : Subgroup J) : Set J) := by
    rw [Q11Sylow_coe]
    exact (Subgroup.normalizer (Q11 : Set J)).pow_mem nrm₂_mem_normalizer 20
  have hfuse : ∀ s ∈ Subgroup.normalizer ((Q11Sylow : Subgroup J) : Set J),
      IsConj (nrm₂ ^ 20 : J) s →
        ∃ m ∈ Subgroup.normalizer ((Q11Sylow : Subgroup J) : Set J), m * nrm₂ ^ 20 * m⁻¹ = s := by
    intro s hs hc
    rw [Q11Sylow_coe] at hs ⊢
    exact fusion_j hs hc
  intro Y hY
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact normMax_of_TI_involution_J4 Q11Sylow CFSG.Sporadic.Bridge.J4.card_J hN hR hTI (nrm₂ ^ 20) htN
    (orderOf_nrm₂_pow_twenty) hfuse hover Y hY

end CFSG.AGLEmbeddingD2.Wilson.Proving

end

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Norm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem kgConcl_of_conj_le {K : Type} [Group K] (p : ℕ) (E : Subgroup (MulAut K))
    (hconj : ∀ S : Subgroup (MulAut K), IsPGroup 2 ↥S →
      ∃ β : MulAut K, S.map (MulAut.conj β⁻¹).toMonoidHom ≤ E)
    (hcore : ∀ S B : Subgroup (MulAut K), S ≤ E → IsPGroup 2 ↥S → ¬ IsCyclic ↥S →
      S ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ → B ≤ normalizer (S : Set (MulAut K)) →
      ∃ σ₁ σ₂ : MulAut K, σ₁ ∈ S ∧ σ₂ ∈ S ∧ σ₁ ≠ 1 ∧ σ₂ ≠ 1 ∧
        (∀ τ ∈ S, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ S, τ * σ₂ = σ₂ * τ) ∧
        (∀ τ ∈ B, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ B, τ * σ₂ = σ₂ * τ) ∧
        Subgroup.closure ({k : K | σ₁ k = k} ∪ {k : K | σ₂ k = k}) = ⊤) :
    KGConcl K p := by
  intro S B hS hSnc hSI _ hBN
  obtain ⟨β, hβ⟩ := hconj S hS
  set φ : MulAut (MulAut K) := MulAut.conj β⁻¹ with hφ
  have hsymm : ∀ σ : MulAut K, φ.symm σ = β * σ * β⁻¹ := fun σ => by
    rw [hφ, MulAut.conj_symm_apply, inv_inv]
  have hS' : IsPGroup 2 ↥(S.map φ.toMonoidHom) := hS.map φ.toMonoidHom
  have hSnc' : ¬ IsCyclic ↥(S.map φ.toMonoidHom) := by
    intro hc
    apply hSnc
    let ι := Subgroup.equivMapOfInjective S φ.toMonoidHom φ.injective
    exact isCyclic_of_surjective ι.symm ι.symm.surjective
  have hSI' : S.map φ.toMonoidHom ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨s, hs, rfl⟩, y, hy⟩
    have hs' : s = MulAut.conj (β y) := by
      apply φ.injective
      refine Eq.trans hy.symm ?_
      ext k
      rw [hφ, MulAut.conj_apply β⁻¹ (MulAut.conj (β y)), inv_inv, MulAut.mul_apply,
        MulAut.mul_apply, MulAut.conj_apply (β y), MulAut.conj_apply y, MulAut.inv_apply,
        map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    have hmem : s ∈ S ⊓ (MulAut.conj : K →* MulAut K).range := ⟨hs, β y, hs'.symm⟩
    rw [hSI, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot, hmem, map_one]
  have hBN' : B.map φ.toMonoidHom ≤
      normalizer ((S.map φ.toMonoidHom : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact FongOut.kg_normalizer_map φ S (hBN hb)
  obtain ⟨σ₁', σ₂', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    hcore (S.map φ.toMonoidHom) (B.map φ.toMonoidHom) hβ hS' hSnc' hSI' hBN'
  refine ⟨φ.symm σ₁', φ.symm σ₂', Subgroup.mem_map_equiv.mp h1, Subgroup.mem_map_equiv.mp h2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    apply h3
    have := congrArg φ hc
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · intro hc
    apply h4
    have := congrArg φ hc
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · intro τ hτ
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h5 _ (Subgroup.mem_map_of_mem φ.toMonoidHom hτ)
  · intro τ hτ
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h6 _ (Subgroup.mem_map_of_mem φ.toMonoidHom hτ)
  · intro τ hτ
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h7 _ (Subgroup.mem_map_of_mem φ.toMonoidHom hτ)
  · intro τ hτ
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h8 _ (Subgroup.mem_map_of_mem φ.toMonoidHom hτ)
  · rw [hsymm, hsymm, closure_fixedPoints_conj, h9]
    exact Subgroup.map_top_of_surjective _ β.surjective

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

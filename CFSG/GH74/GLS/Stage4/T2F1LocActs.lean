module

public import CFSG.GH74.GLS.Stage4.T2LeafOA
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundAut
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_matrix)
open CFSG.GH74.GLS.Stage4.Hex (SL2)
open CFSG.GH74.GLS.Stage4.Rest.T2 (slConj coe_slConj)

section Aux

variable {G : Type} [Group G]

theorem normalizerMonoidHom_mul_eq_conj {K : Subgroup G} {k₁ k₂ : G} (hk₁ : k₁ ∈ K)
    (hk₂ : ∀ x ∈ K, x * k₂ = k₂ * x) (hn : k₁ * k₂ ∈ normalizer (K : Set G)) :
    Subgroup.normalizerMonoidHom K ⟨k₁ * k₂, hn⟩ = MulAut.conj (⟨k₁, hk₁⟩ : ↥K) := by
  ext x
  show k₁ * k₂ * (x : G) * (k₁ * k₂)⁻¹ = k₁ * (x : G) * k₁⁻¹
  have h : k₂ * (x : G) * k₂⁻¹ = x := by rw [← hk₂ x x.2]; group
  calc k₁ * k₂ * (x : G) * (k₁ * k₂)⁻¹ = k₁ * (k₂ * (x : G) * k₂⁻¹) * k₁⁻¹ := by group
    _ = k₁ * (x : G) * k₁⁻¹ := by rw [h]

theorem inn_of_mul {K : Subgroup G} {t k₁ k₂ : G} (hk₁ : k₁ ∈ K) (hk₂ : ∀ x ∈ K, x * k₂ = k₂ * x)
    (ht : t ∈ normalizer (K : Set G)) (hk : k₁ * k₂ ∈ normalizer (K : Set G))
    (hc : t * (k₁ * k₂) ∈ normalizer (K : Set G))
    (h : Subgroup.normalizerMonoidHom K ⟨t * (k₁ * k₂), hc⟩ ∈ (MulAut.conj : ↥K →* MulAut ↥K).range) :
    Subgroup.normalizerMonoidHom K ⟨t, ht⟩ ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := by
  have e1 : (⟨t * (k₁ * k₂), hc⟩ : ↥(normalizer (K : Set G))) = ⟨t, ht⟩ * ⟨k₁ * k₂, hk⟩ := rfl
  rw [e1, map_mul, normalizerMonoidHom_mul_eq_conj hk₁ hk₂ hk] at h
  have e2 : Subgroup.normalizerMonoidHom K ⟨t, ht⟩ =
      Subgroup.normalizerMonoidHom K ⟨t, ht⟩ * MulAut.conj (⟨k₁, hk₁⟩ : ↥K) *
        (MulAut.conj (⟨k₁, hk₁⟩ : ↥K))⁻¹ := by
    group
  rw [e2]
  exact mul_mem h (inv_mem ⟨_, rfl⟩)

end Aux

section Main

variable {G : Type} [Group G] [Finite G] {K K' : Subgroup G} {t c : G}
  {F : Type} [Field F] [Finite F]

theorem actsAsConj_in_coord (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (φ : SL2 F →* G) (hφ : Function.Injective φ) (hrange : φ.range = K)
    (hKK' : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x)
    (hnK : ∀ c ∈ K ⊔ K' ⊔ Subgroup.zpowers t, ∀ x ∈ K, c * x * c⁻¹ ∈ K)
    (hts : ∃ (e₀ : ↥K ≃* SL2 F) (g : GL (Fin 2) F),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∧ ActsAsConj t K e₀ g)
    (hc : ∃ k ∈ K ⊔ K', c = t * k) :
    ∃ g' : GL (Fin 2) F, ¬ IsSquare ((Matrix.GeneralLinearGroup.det g' : Fˣ) : F) ∧
      ∀ M : SL2 F, c * φ M * c⁻¹ = φ (slConj g' M) := by
  subst hrange
  obtain ⟨k, hk, rfl⟩ := hc
  have hmt : t ∈ φ.range ⊔ K' ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hmk : k ∈ φ.range ⊔ K' ⊔ Subgroup.zpowers t := Subgroup.mem_sup_left hk
  have htn : t ∈ normalizer (φ.range : Set G) := Subgroup.mem_normalizer_fintype (hnK t hmt)
  have hkn : k ∈ normalizer (φ.range : Set G) := Subgroup.mem_normalizer_fintype (hnK k hmk)
  let e : ↥φ.range ≃* SL2 F := (MonoidHom.ofInjective hφ).symm
  obtain ⟨hcn, hc1⟩ := t2L_lin_gen hodd h3 e hKK' hnK
    (let ⟨e₀, g, _, h⟩ := hts; ⟨e₀, g, h⟩) (t * k) (mul_mem hmt hmk)
  obtain ⟨g', hg'⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hc1
  refine ⟨g', ?_, ?_⟩
  · intro hsq
    have hinn : slConjugation F g' ∈ (MulAut.conj : SL2 F →* MulAut (SL2 F)).range :=
      (slConjugation_mem_inn_iff hodd h3 g').2 (by simpa using hsq)
    have hρc : Subgroup.normalizerMonoidHom φ.range ⟨t * k, hcn⟩ ∈
        (MulAut.conj : ↥φ.range →* MulAut ↥φ.range).range :=
      inn_of_congr_inn e _ (hg' ▸ hinn)
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hKK' hk
    obtain ⟨e₀, g, hns, hact⟩ := hts
    obtain ⟨u, hu⟩ := inn_of_mul hk₁ (fun x hx => hKK' x hx k₂ hk₂) htn hkn hcn hρc
    have h1 := t2L_congr_actsAsConj e₀ g hact htn
    rw [← hu, congr_conj] at h1
    exact hns (by simpa using (slConjugation_mem_inn_iff hodd h3 g).1 ⟨e₀ u, h1⟩)
  · intro M
    have h1 : e (Subgroup.normalizerMonoidHom φ.range ⟨t * k, hcn⟩ (e.symm M)) =
        slConjugation F g' M := by
      have := congrArg (fun α : MulAut (SL2 F) => α M) hg'
      simpa [MulAut.congr_apply] using this
    have h2 : Subgroup.normalizerMonoidHom φ.range ⟨t * k, hcn⟩ (e.symm M) =
        e.symm (slConjugation F g' M) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    have h4 : slConj g' M = slConjugation F g' M := by
      apply Subtype.ext
      rw [coe_slConj, slConjugation_matrix]
    rw [h4]
    calc t * k * φ M * (t * k)⁻¹
        = ((Subgroup.normalizerMonoidHom φ.range ⟨t * k, hcn⟩ (e.symm M) : ↥φ.range) : G) := rfl
      _ = (e.symm (slConjugation F g' M) : G) := congrArg Subtype.val h2
      _ = φ (slConjugation F g' M) := rfl

end Main

end CFSG.GH74.GLS.Stage4.Rest.F1Loc

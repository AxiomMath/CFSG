module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GH74.GLS.Stage4.T2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.GorensteinWalter
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_toGL slConjugation_matrix)

section Gamma

variable {F : Type} [Field F] [Finite F]

theorem t2L_gamma_slConj (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (g : GL (Fin 2) F) :
    (gammaOf hodd h3 (slConjugation F g)).right = 1 := by
  have h : gammaOf hodd h3 (slConjugation F g) =
      SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk g) := by
    apply (thetaEquiv hodd h3).injective
    rw [thetaEquiv_gammaOf, psl2MulAutOf_slConjugation hodd h3 g]
  rw [h]
  rfl

@[expose] noncomputable def t2LFieldHom (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    MulAut (Hex.SL2 F) →* (F ≃+* F) :=
  (SemidirectProduct.rightHom).comp (gammaOf hodd h3)

end Gamma

section Conj

variable {G : Type} [Group G]

theorem t2L_congr_actsAsConj {K : Subgroup G} {t : G} {F : Type} [Field F]
    (e₀ : ↥K ≃* Hex.SL2 F) (g : GL (Fin 2) F) (hact : ActsAsConj t K e₀ g)
    (ht : t ∈ normalizer (K : Set G)) :
    MulAut.congr e₀ (Subgroup.normalizerMonoidHom K ⟨t, ht⟩) = slConjugation F g := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, hy1, hy2⟩ := hact (e₀.symm x)
  have h1 : (Subgroup.normalizerMonoidHom K ⟨t, ht⟩) (e₀.symm x) = y :=
    Subtype.ext (by rw [hy1]; rfl)
  show e₀ ((Subgroup.normalizerMonoidHom K ⟨t, ht⟩) (e₀.symm x)) = (slConjugation F g) x
  rw [h1]
  apply Subtype.ext
  rw [slConjugation_matrix, hy2, MulEquiv.apply_symm_apply]

end Conj

section Lin

variable {G : Type} [Group G] [Finite G]

theorem t2L_lin_gen {K K' : Subgroup G} {t : G} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (e : ↥K ≃* Hex.SL2 F)
    (hKK' : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x)
    (hnK : ∀ c ∈ K ⊔ K' ⊔ Subgroup.zpowers t, ∀ x ∈ K, c * x * c⁻¹ ∈ K)
    (hts : ∃ (e₀ : ↥K ≃* Hex.SL2 F) (g : GL (Fin 2) F), ActsAsConj t K e₀ g) :
    ∀ c ∈ K ⊔ K' ⊔ Subgroup.zpowers t, ∃ hc : c ∈ normalizer (K : Set G),
      (gammaOf hodd h3 (MulAut.congr e (Subgroup.normalizerMonoidHom K ⟨c, hc⟩))).right = 1 := by
  let Φ : ↥(normalizer (K : Set G)) →* (F ≃+* F) :=
    ((t2LFieldHom hodd h3).comp (MulAut.congr e).toMonoidHom).comp (Subgroup.normalizerMonoidHom K)
  have hΦ : ∀ (c : G) (hc : c ∈ normalizer (K : Set G)), Φ ⟨c, hc⟩ =
      (gammaOf hodd h3 (MulAut.congr e (Subgroup.normalizerMonoidHom K ⟨c, hc⟩))).right :=
    fun c hc => rfl
  have key : K ⊔ K' ⊔ Subgroup.zpowers t ≤ Φ.ker.map (normalizer (K : Set G)).subtype := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      have hyn : y ∈ normalizer (K : Set G) := Subgroup.le_normalizer hy
      refine ⟨⟨y, hyn⟩, ?_, rfl⟩
      show Φ ⟨y, hyn⟩ = 1
      rw [hΦ]
      have : Subgroup.normalizerMonoidHom K ⟨y, hyn⟩ = MulAut.conj (⟨y, hy⟩ : ↥K) := by
        ext x; rfl
      rw [this, congr_conj]
      exact gammaOf_conj_right hodd h3 _
    · intro y hy
      have hyc : ∀ x ∈ K, y * x * y⁻¹ = x := fun x hx => by
        rw [← hKK' x hx y hy]; group
      have hyn : y ∈ normalizer (K : Set G) :=
        Subgroup.mem_normalizer_fintype (fun x hx => by rw [hyc x hx]; exact hx)
      refine ⟨⟨y, hyn⟩, ?_, rfl⟩
      show Φ ⟨y, hyn⟩ = 1
      rw [hΦ]
      have : Subgroup.normalizerMonoidHom K ⟨y, hyn⟩ = 1 := by
        ext x
        exact hyc x x.2
      rw [this, map_one, map_one]
      rfl
    · rw [Subgroup.zpowers_le]
      have htn : t ∈ normalizer (K : Set G) :=
        Subgroup.mem_normalizer_fintype
          (hnK t (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
      refine ⟨⟨t, htn⟩, ?_, rfl⟩
      show Φ ⟨t, htn⟩ = 1
      rw [hΦ]
      obtain ⟨e₀, g, hact⟩ := hts
      have h1 := t2L_congr_actsAsConj e₀ g hact htn
      set ρ : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨t, htn⟩ with hρ
      let θ : MulAut (Hex.SL2 F) := e₀.symm.trans e
      have h2 : MulAut.congr e ρ = θ * MulAut.congr e₀ ρ * θ⁻¹ := by
        apply MulEquiv.ext
        intro x
        simp [θ, MulAut.congr_apply]
      rw [h2, h1]
      have h4 : t2LFieldHom hodd h3 (θ * slConjugation F g * θ⁻¹) =
          t2LFieldHom hodd h3 θ * t2LFieldHom hodd h3 (slConjugation F g) *
            (t2LFieldHom hodd h3 θ)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      have h5 : t2LFieldHom hodd h3 (slConjugation F g) = 1 := t2L_gamma_slConj hodd h3 g
      have h6 : t2LFieldHom hodd h3 (θ * slConjugation F g * θ⁻¹) = 1 := by
        rw [h4, h5, mul_one, mul_inv_cancel]
      exact h6
  intro c hc
  obtain ⟨⟨y, hyn⟩, hy1, hy2⟩ := key hc
  have hc' : c ∈ normalizer (K : Set G) := hy2 ▸ hyn
  refine ⟨hc', ?_⟩
  have h : Φ ⟨y, hyn⟩ = 1 := hy1
  subst hy2
  exact h

end Lin

end CFSG.GH74.GLS.Stage4.Rest

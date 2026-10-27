module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.GroupTheory.OppositeRadicals

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup

@[expose] def GomiExcAutFixed (K : Type) [Group K] : Prop :=
  ∀ (β : MulAut K) (U : Subgroup K), β * β = 1 → (∀ k : K, β ≠ MulAut.conj k) →
    IsSylowOf 2 U ⊤ → U.map β.toMonoidHom = U →
    (∀ A : Subgroup K, IsGomiAtom ⊤ U A → A ⊔ A.map β.toMonoidHom ≠ ⊤) →
    pCoreOf 2 (β.toMonoidHom.eqLocus (MonoidHom.id K)) ≠ ⊥

private theorem gomiExcAutFixed_congr_comp {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (β' : MulAut K') :
    (MulAut.congr e.symm β').toMonoidHom.comp e.symm.toMonoidHom =
      e.symm.toMonoidHom.comp β'.toMonoidHom := by
  ext x'
  simp [MulAut.congr_apply]

private theorem gomiExcAutFixed_comp_congr {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (β' : MulAut K') :
    e.toMonoidHom.comp (MulAut.congr e.symm β').toMonoidHom =
      β'.toMonoidHom.comp e.toMonoidHom := by
  ext x
  simp [MulAut.congr_apply]

private theorem gomiExcAutFixed_eqLocus {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (β' : MulAut K') :
    ((MulAut.congr e.symm β').toMonoidHom.eqLocus (MonoidHom.id K)).map e.toMonoidHom =
      β'.toMonoidHom.eqLocus (MonoidHom.id K') := by
  ext x'
  rw [Subgroup.mem_map_equiv]
  change (MulAut.congr e.symm β') (e.symm x') = e.symm x' ↔ β' x' = x'
  rw [show (MulAut.congr e.symm β') (e.symm x') = e.symm (β' x') by
    simp [MulAut.congr_apply]]
  exact e.symm.injective.eq_iff

private theorem gomiExcAutFixed_atom {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (β' : MulAut K') (U' : Subgroup K')
    (hA' : ∀ A : Subgroup K', IsGomiAtom ⊤ U' A → A ⊔ A.map β'.toMonoidHom ≠ ⊤) :
    ∀ A : Subgroup K, IsGomiAtom ⊤ (U'.map e.symm.toMonoidHom) A →
      A ⊔ A.map (MulAut.congr e.symm β').toMonoidHom ≠ ⊤ := by
  intro A hA
  have hUe : (U'.map e.symm.toMonoidHom).map e.toMonoidHom = U' := by
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K' := by
      ext x
      simp
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hA'atom : IsGomiAtom ⊤ U' (A.map e.toMonoidHom) := by
    have h := (isGomiAtom_top_map_mulEquiv_iff e (U'.map e.symm.toMonoidHom) A).2 hA
    rwa [hUe] at h
  intro htop
  apply hA' (A.map e.toMonoidHom) hA'atom
  have hmap : (A ⊔ A.map (MulAut.congr e.symm β').toMonoidHom).map e.toMonoidHom =
      A.map e.toMonoidHom ⊔ (A.map e.toMonoidHom).map β'.toMonoidHom := by
    rw [Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map, gomiExcAutFixed_comp_congr]
  rw [← hmap, htop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

theorem GomiExcAutFixed.of_mulEquiv {K K' : Type} [Group K] [Group K'] [Finite K]
    (e : K ≃* K') (h : GomiExcAutFixed K) : GomiExcAutFixed K' := by
  intro β' U' hβ2 hβout hU' hβU' hA'
  let β : MulAut K := MulAut.congr e.symm β'
  have hβ : β = MulAut.congr e.symm β' := rfl
  let U : Subgroup K := U'.map e.symm.toMonoidHom
  have hU : U = U'.map e.symm.toMonoidHom := rfl
  have hfin' : Finite K' := Finite.of_equiv K e.toEquiv
  have hβ2K : β * β = 1 := by rw [hβ, ← map_mul, hβ2, map_one]
  have hβoutK : ∀ k : K, β ≠ MulAut.conj k := by
    intro k hk
    apply hβout (e k)
    ext x'
    have h1 : β (e.symm x') = e.symm (β' x') := by rw [hβ]; simp [MulAut.congr_apply]
    have h2 : e.symm (β' x') = k * e.symm x' * k⁻¹ := by rw [← h1, hk]; rfl
    simpa [MulAut.conj_apply] using congrArg e h2
  have hUK : IsSylowOf 2 U ⊤ := by
    rw [hU]
    exact isSylowOf_top_map_of_surjective e.symm.surjective hU'
  have hβUK : U.map β.toMonoidHom = U := by
    rw [hU, Subgroup.map_map, hβ, gomiExcAutFixed_congr_comp, ← Subgroup.map_map, hβU']
  have hAK : ∀ A : Subgroup K, IsGomiAtom ⊤ U A → A ⊔ A.map β.toMonoidHom ≠ ⊤ := by
    rw [hU, hβ]
    exact gomiExcAutFixed_atom e β' U' hA'
  have hp := h β U hβ2K hβoutK hUK hβUK hAK
  have hC : (β.toMonoidHom.eqLocus (MonoidHom.id K)).map e.toMonoidHom =
      β'.toMonoidHom.eqLocus (MonoidHom.id K') := by
    rw [hβ]
    exact gomiExcAutFixed_eqLocus e β'
  intro hbot
  have hmapC : (pCoreOf 2 (β.toMonoidHom.eqLocus (MonoidHom.id K))).map
      e.toMonoidHom = ⊥ := by
    rw [← pCoreOf_map_of_injective 2 e.toMonoidHom e.injective, hC, hbot]
  exact hp ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmapC)

end CFSG.GroupTheory

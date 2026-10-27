module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.QTransport

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

variable {A B : Type} [Group A] [Group B]

@[expose] def mapFam (e : A ≃* B) (Ω : Set (Subgroup A)) : Set (Subgroup B) :=
  (Subgroup.map e.toMonoidHom) '' Ω

theorem map_map_symm (e : A ≃* B) (L : Subgroup A) :
    (L.map e.toMonoidHom).map e.symm.toMonoidHom = L := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A :=
    MonoidHom.ext fun x => e.symm_apply_apply x
  rw [this, Subgroup.map_id]

theorem map_symm_map (e : A ≃* B) (L : Subgroup B) :
    (L.map e.symm.toMonoidHom).map e.toMonoidHom = L := by
  rw [Subgroup.map_map]
  have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B :=
    MonoidHom.ext fun x => e.apply_symm_apply x
  rw [this, Subgroup.map_id]

theorem injOn_map (e : A ≃* B) (F : Subgroup A) : ∀ x ∈ F, e.toMonoidHom x = 1 → x = 1 :=
  fun _ _ h => e.injective (h.trans e.map_one.symm)

theorem map_pairNormalizers (e : A ≃* B) (K J : Subgroup A) (zK zJ : A) :
    (pairNormalizers K J zK zJ).map e.toMonoidHom =
      pairNormalizers (K.map e.toMonoidHom) (J.map e.toMonoidHom) (e zK) (e zJ) := by
  have hcl : (Subgroup.closure ({zK, zJ} : Set A)).map e.toMonoidHom =
      Subgroup.closure ({e zK, e zJ} : Set B) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_pair]
  have hN : (Subgroup.normalizer ((Subgroup.closure ({zK, zJ} : Set A) : Subgroup A) : Set A)).map
      e.toMonoidHom = Subgroup.normalizer
        ((Subgroup.closure ({e zK, e zJ} : Set B) : Subgroup B) : Set B) := by
    rw [← hcl]
    exact Subgroup.map_equiv_normalizer_eq _ e
  unfold pairNormalizers
  rw [Subgroup.map_sup, Subgroup.map_inf_eq _ _ _ e.injective,
    Subgroup.map_inf_eq _ _ _ e.injective, hN]

variable [Finite B]

theorem aEmpty_of_mapFam_sub (e : A ≃* B) {Ω : Set (Subgroup A)} {Δ : Set (Subgroup B)}
    (hΔ : HypOmegaGen Δ) (hsub : mapFam e Ω ⊆ Δ) {K : Subgroup A}
    (hA : AEmpty Δ (K.map e.toMonoidHom)) : AEmpty Ω K := by
  intro J hJ hJn zK zJ hzK hzJ
  obtain ⟨hJΩ, hJK, U, hU, hUJ, hUN⟩ := hJ
  have hJ'Δ : J.map e.toMonoidHom ∈ Δ := hsub ⟨J, hJΩ, rfl⟩
  have hstar : J.map e.toMonoidHom ∈ omegaStarNbr Δ (K.map e.toMonoidHom) := by
    refine ⟨hJ'Δ, fun h => hJK (Subgroup.map_injective e.injective h), U.map e.toMonoidHom, ?_,
      Subgroup.map_mono hUJ, (Subgroup.map_mono hUN).trans (Subgroup.le_normalizer_map _)⟩
    obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
    obtain ⟨J₀, hJ₀, hRs⟩ := exists_isSylow2In_of_mem_RSet hR
    refine USet_mono hsub ⟨R.map e.toMonoidHom, mem_RSet_of_isSylow2In ⟨J₀, hJ₀, rfl⟩
      (isSylow2In_map_of_injOn e.toMonoidHom (injOn_map e J₀) hRs), Subgroup.map_mono hUR, ?_, ?_⟩
    · exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective U e.toMonoidHom e.injective)).mp hcyc
    · rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]
      exact hidx
  have hnbr : J.map e.toMonoidHom ∉ omegaNbr Δ (K.map e.toMonoidHom) := by
    rintro ⟨-, -, R', hR', hR'J, hR'N⟩
    have hS : IsSylow2In R' (J.map e.toMonoidHom) :=
      Sec6Gen.isSylow2In_of_mem_RSet_of_le hΔ hJ'Δ hR' hR'J
    have hS' : IsSylow2In (R'.map e.symm.toMonoidHom) J := by
      have := isSylow2In_map_of_injOn e.symm.toMonoidHom (injOn_map e.symm _) hS
      rwa [map_map_symm] at this
    apply hJn
    refine ⟨hJΩ, hJK, R'.map e.symm.toMonoidHom, mem_RSet_of_isSylow2In hJΩ hS', hS'.1, ?_⟩
    have h1 := (Subgroup.map_mono hR'N).trans (Subgroup.le_normalizer_map e.symm.toMonoidHom)
    rwa [map_map_symm] at h1
  obtain ⟨g', hg', hconj⟩ := hA _ hstar hnbr (e zK) (e zJ)
    (isUniqueInvolution_map_of_injOn e.toMonoidHom (injOn_map e K) hzK)
    (isUniqueInvolution_map_of_injOn e.toMonoidHom (injOn_map e J) hzJ)
  refine ⟨e.symm g', ?_, ?_⟩
  · rw [← map_pairNormalizers] at hg'
    obtain ⟨x, hx, hxg⟩ := hg'
    have : x = e.symm g' := by rw [← hxg]; exact (e.symm_apply_apply x).symm
    rwa [this] at hx
  · have h1 : (conjSub (e.symm g') K).map e.toMonoidHom = J.map e.toMonoidHom := by
      rw [AscQuot.map_conjSub]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hconj
    exact Subgroup.map_injective e.injective h1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.QTransport

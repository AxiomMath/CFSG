module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP3Loc

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P10

open CFSG Subgroup GS82PumpInputs.FixedLoc
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X] [Finite X]

theorem fixedTwoComponentLocation' (β : MulAut X) (hβ : ∀ x, β (β x) = x) {T : Subgroup X}
    (hTC : T ≤ fixedSubgroup β) (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup β))) :
    ∃ X₁ : Subgroup X, IsPComponent 2 X₁ ∧
      ((X₁.map β.toMonoidHom = X₁ ∧ T ≤ X₁) ∨
        (X₁.map β.toMonoidHom ≠ X₁ ∧ T ≤ X₁ ⊔ X₁.map β.toMonoidHom ∧
          ∃ φ : ↥X₁ ⧸ pPrimeCore 2 ↥X₁ →* ↥T ⧸ pPrimeCore 2 ↥T, Function.Surjective φ)) := by
  by_cases hβ1 : β = 1
  · subst hβ1
    refine ⟨T, ?_, Or.inl ⟨?_, le_rfl⟩⟩
    · have htop : fixedSubgroup (1 : MulAut X) = ⊤ := by
        ext x
        exact ⟨fun _ => mem_top x, fun _ => rfl⟩
      rw [htop, CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T ⊤ le_top] at hT
      exact (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 T).2
        ⟨Subgroup.IsSubnormal.trans le_top hT.1 Subgroup.IsSubnormal.top, hT.2⟩
    · have h1 : (1 : MulAut X).toMonoidHom = MonoidHom.id X := MonoidHom.ext fun _ => rfl
      rw [h1, Subgroup.map_id]
  have ht := orderOf_gen β hβ hβ1
  have hJ := isTwoComponentIn_map_inl β hTC hT
  have h219 := HarrisLit.harris82Lemma219Input_holds (Ext β) (gen β) ht
  obtain ⟨K, hK, hcases, -⟩ := h219.2 _ hJ
  have hKX : K ≤ (SemidirectProduct.inl : X →* Ext β).range :=
    le_range_inl β (Subgroup.isPerfect_iff.mp hK.2.1)
  have hX₁K : (K.comap (SemidirectProduct.inl : X →* Ext β)).map
      (SemidirectProduct.inl : X →* Ext β) = K := map_comap_eq_self hKX
  have hinv : (K.comap (SemidirectProduct.inl : X →* Ext β)).map β.toMonoidHom =
      K.comap (SemidirectProduct.inl : X →* Ext β) ↔
      K.map (MulAut.conj (gen β)).toMonoidHom = K := by
    rw [← (Subgroup.map_injective
      (SemidirectProduct.inl_injective (φ := (zpowers β).subtype))).eq_iff,
      map_map_inl, hX₁K]
  refine ⟨K.comap SemidirectProduct.inl, isPComponent_comap_inl β hK hKX, ?_⟩
  rcases hcases with ⟨hKt, hJK⟩ | ⟨hKt, hJeq⟩
  · exact Or.inl ⟨hinv.mpr hKt, map_le_iff_le_comap.mp (hJK.1.trans inf_le_left)⟩
  · refine Or.inr ⟨fun h => hKt (hinv.mp h), ?_, ?_⟩
    ·
      have h1 : T.map (SemidirectProduct.inl : X →* Ext β) ≤
          K ⊔ K.map (MulAut.conj (gen β)).toMonoidHom := by
        rw [hJeq]
        exact HarrisLit.centralizerResidual_le_left
      have h2 : (K.comap (SemidirectProduct.inl : X →* Ext β) ⊔
          (K.comap (SemidirectProduct.inl : X →* Ext β)).map β.toMonoidHom).map
            (SemidirectProduct.inl : X →* Ext β) =
          K ⊔ K.map (MulAut.conj (gen β)).toMonoidHom := by
        rw [Subgroup.map_sup, map_map_inl, hX₁K]
      rw [← h2] at h1
      exact (Subgroup.map_le_map_iff_of_injective SemidirectProduct.inl_injective).mp h1
    ·
      have hφ : ∃ φ : ↥K ⧸ pPrimeCore 2 ↥K →*
          ↥(T.map (SemidirectProduct.inl : X →* Ext β)) ⧸
            pPrimeCore 2 ↥(T.map (SemidirectProduct.inl : X →* Ext β)),
          Function.Surjective φ := by
        obtain ⟨-, -, hφ⟩ := (h219.1 K hK).2 hKt
        rw [hJeq]
        exact hφ
      obtain ⟨φ, hφ⟩ := hφ
      let eT := T.equivMapOfInjective (SemidirectProduct.inl : X →* Ext β)
        SemidirectProduct.inl_injective
      let eK : ↥(K.comap (SemidirectProduct.inl : X →* Ext β)) ≃* ↥K :=
        ((K.comap (SemidirectProduct.inl : X →* Ext β)).equivMapOfInjective _
          SemidirectProduct.inl_injective).trans (MulEquiv.subgroupCongr hX₁K)
      let qK := QuotientGroup.congr _ _ eK (pPrimeCore_map_iso 2 eK)
      let qT := QuotientGroup.congr _ _ eT (pPrimeCore_map_iso 2 eT)
      refine ⟨qT.symm.toMonoidHom.comp (φ.comp qK.toMonoidHom), ?_⟩
      exact qT.symm.surjective.comp (hφ.comp qK.surjective)

end CFSG.ComponentClassification.GS82PumpInputs.P10

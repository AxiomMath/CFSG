module

public import CFSG.GroupTheory.QuasiDihedralFusion.WreathedSupport
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.BenderSuzuki.External
open CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {H : Type u} [Group H] {n : ℕ}

section Involutions

theorem orderOf_wreathModelHom (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (w : Wreath (2 ^ n)) : orderOf (wreathModelHom S e w) = orderOf w :=
  orderOf_injective _ (wreathModelHom_injective S e) w

theorem orderOf_wreath_x (hn : 2 ≤ n) (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2 := by
  rw [orderOf_wreathModelHom]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

theorem orderOf_wreath_x2 (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    orderOf (wreathModelHom S e (Original.x2 (2 ^ n))) = 2 := by
  rw [orderOf_wreathModelHom]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.2.1

theorem orderOf_wreath_z (hn : 2 ≤ n) (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    orderOf (wreathModelHom S e (Original.z (2 ^ n))) = 2 := by
  rw [orderOf_wreathModelHom]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.2.2.1

theorem wreath_x_mem_modelCenter (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x (2 ^ n)) ∈ modelCenter S e :=
  ⟨_, (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _, rfl⟩

theorem modelCenter_le_sylow (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    modelCenter S e ≤ (S : Subgroup H) := by
  rintro _ ⟨w, -, rfl⟩
  exact wreathModelHom_mem S e w

variable [Finite H]

theorem not_isConj_x_of_base_order_two (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hα : Nat.card (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H))) = 2)
    (y : H) (hyS : y ∈ (S : Subgroup H)) (hy : y ≠ wreathModelHom S e (Original.x (2 ^ n))) :
    ¬ IsConj (wreathModelHom S e (Original.x (2 ^ n))) y := by
  intro hxy
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have h := modelCenter_isolated_of_base_order_two hn S e hα (wreath_x_mem_modelCenter S e) c⁻¹
    (by rw [inv_inv, hc]; exact hyS)
  rw [inv_inv, hc] at h
  exact hy h

end Involutions

section Alternatives

variable [Finite H]

theorem wreathedFusionQD_of (hn : 2 ≤ n) (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hα : Nonempty (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H)) ≃* Equiv.Perm (Fin 3)))
    (hβ : Nonempty (Subgroup.normalizer (modelV S e : Set H) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    WreathedFusionQD S e where
  noIndexTwo K hK := typeI_of_base_sym3 n hn S e hα hβ
    ⟨K, Subgroup.normal_of_index_eq_two hK, hK⟩
  involutionClasses := conjClassCountOfOrder_eq_one _ _ (orderOf_wreath_x hn S e)
    (orderOf_wreath_x hn S e)
    (fun y hy => Or.inl (all_involutions_conjugate_of_base_sym3 hn S e hα hβ _ _
      (orderOf_wreath_x hn S e) hy)) (IsConj.refl _)
  baseIndex := by
    obtain ⟨eα⟩ := hα
    rw [automizerIndex_modelBase, Nat.card_congr eα.toEquiv, card_perm_fin_three]
  quaternionIndex := by
    obtain ⟨eβ⟩ := hβ
    rw [outerAutomizerIndex_modelV, Nat.card_congr eβ.toEquiv, card_perm_fin_three]

theorem wreathedFusionQ_of (hn : 2 ≤ n) (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hα : Nat.card (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H))) = 2)
    (hβ : Nonempty (Subgroup.normalizer (modelV S e : Set H) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    WreathedFusionQ S e := by
  obtain ⟨G₀, hG₀, hidx, hQ⟩ := typeII_of_base_order_two n hn S e hα hβ
  have : G₀.Normal := hG₀
  have hKS : G₀ ⊓ (S : Subgroup H) = modelY S e := by
    rw [inf_comm]
    exact (typeII_subgroup_spec n hn S e G₀ hidx hQ).1
  have hpow : ∃ k : ℕ, G₀.index = 2 ^ k := ⟨n, hidx⟩
  refine ⟨⟨G₀, hG₀, hidx, ?_, ?_⟩, ?_, ?_, hα, ?_⟩
  · intro M hM
    have hYK : modelY S e ≤ G₀ := by
      rw [← hKS]
      exact inf_le_left
    have hY := modelY_le_commutator hn S e hβ G₀ hpow hYK
    apply inf_sylow_not_le_map_of_index_two S G₀ hM
    rw [hKS]
    exact hY.trans (Subgroup.map_mono (commutator_le_of_index_two hM))
  · intro P
    obtain ⟨eP⟩ := nonempty_sylow_equiv_inf S G₀ P
    obtain ⟨eQ⟩ := hQ
    exact ⟨n - 1, by omega, ⟨eP.trans ((MulEquiv.subgroupCongr (inf_comm _ _)).trans eQ)⟩⟩
  · intro Z₀ hZ₀
    rw [centerOf_eq_modelCenter hn S e] at hZ₀
    have hfix : ∀ c ∈ Z₀, ∀ g : H, g⁻¹ * c * g ∈ (S : Subgroup H) → g⁻¹ * c * g = c :=
      fun c hc g hg => modelCenter_isolated_of_base_order_two hn S e hα (hZ₀ hc) g hg
    refine ⟨hZ₀.trans (modelCenter_le_sylow S e), fun g hg => ?_⟩
    have hmem : ∀ c ∈ Z₀, g⁻¹ * c * g ∈ (S : Subgroup H) := by
      intro c hc
      apply hg
      exact ⟨c, hc, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hfix c hc g (hmem c hc)]
      exact hc
    · intro c hc
      refine ⟨c, hc, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hfix c hc g (hmem c hc)
  · refine conjClassCountOfOrder_eq_two _ _ (orderOf_wreath_x hn S e)
      (orderOf_wreath_x2 hn S e) (fun y hy => ?_) ?_
    · rcases involution_isConj_cases hn S e y hy with h | h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
      · exact Or.inr (h.trans (isConj_swap_x2 hn S e hβ)).symm
    · exact not_isConj_x_of_base_order_two hn S e hα _ (wreathModelHom_mem S e _)
        (modelHom_x_ne_x2 S e (by omega)).symm
  · obtain ⟨eβ⟩ := hβ
    rw [outerAutomizerIndex_modelV, Nat.card_congr eβ.toEquiv, card_perm_fin_three]

theorem wreathedFusionD_of (hn : 2 ≤ n) (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hα : Nonempty (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H)) ≃* Equiv.Perm (Fin 3)))
    (hβ : Nat.card (Subgroup.normalizer (modelV S e : Set H) ⧸ modelVInnerCentralizer S e) = 2) :
    WreathedFusionD S e := by
  obtain ⟨K, hK, -, hKpow, hKS⟩ := exists_focal_kernel S
  have : K.Normal := hK
  have hF : K ⊓ (S : Subgroup H) = modelBase S e := by
    rw [hKS, Subgroup.subgroupOf_map_subtype, Subgroup.commutator_inf_eq_focalSubgroup S]
    apply le_antisymm (model_base_contains_focal_of_v_order_two n hn S e hβ)
    rw [← Subgroup.commutator_inf_eq_focalSubgroup S]
    exact le_inf (modelBase_le_derived hn S e hα) (modelBase_le_sylow S e)
  refine ⟨⟨K, hK, ?_, hF⟩, ?_, ?_, ?_⟩
  · intro M hM
    have hUK : modelBase S e ≤ K := by
      rw [← hF]
      exact inf_le_left
    have hU := modelBase_le_commutator hn S e hα K hKpow hUK
    apply inf_sylow_not_le_map_of_index_two S K hM
    rw [hF]
    exact hU.trans (Subgroup.map_mono (commutator_le_of_index_two hM))
  · refine conjClassCountOfOrder_eq_two _ _ (orderOf_wreath_x hn S e)
      (orderOf_wreath_z hn S e) (fun y hy => ?_) ?_
    · rcases involution_isConj_cases hn S e y hy with h | h | h
      · exact Or.inl h.symm
      · exact Or.inl ((isConj_x_x2_of_base_sym3 hn S e hα).trans h.symm)
      · exact Or.inr h.symm
    · exact not_isConj_swap_of_v_order_two hn S e hβ _ (BrauerWong.modelHom_x_mem_modelBase S e)
  · obtain ⟨eα⟩ := hα
    rw [automizerIndex_modelBase, Nat.card_congr eα.toEquiv, card_perm_fin_three]
  · rw [outerAutomizerIndex_modelV]
    exact hβ

theorem wreathedFusionComplement_of (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hα : Nat.card (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H))) = 2)
    (hβ : Nat.card (Subgroup.normalizer (modelV S e : Set H) ⧸ modelVInnerCentralizer S e) = 2) :
    WreathedFusionComplement S e := by
  obtain ⟨K, hK, -, hKpow, hKS⟩ := exists_focal_kernel S
  have : K.Normal := hK
  have hle : K ⊓ (S : Subgroup H) ≤ Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) := by
    rw [hKS, Subgroup.subgroupOf_map_subtype, Subgroup.commutator_inf_eq_focalSubgroup S,
      ← modelBase_inf_modelY hn S e]
    exact le_inf (model_base_contains_focal_of_v_order_two n hn S e hβ)
      (modelY_contains_focal_of_base_order_two n hn S e hα)
  have hcyc : IsCyclic (K ⊓ (S : Subgroup H) : Subgroup H) := Subgroup.isCyclic_of_le hle
  refine ⟨hasNormalPComplement_of_cyclic_kernel S K hKpow hcyc, ?_, hα, ?_⟩
  · refine conjClassCountOfOrder_eq_three _ _ _ (orderOf_wreath_x hn S e)
      (orderOf_wreath_x2 hn S e) (orderOf_wreath_z hn S e) (fun y hy => ?_) ?_ ?_ ?_
    · rcases involution_isConj_cases hn S e y hy with h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h.symm)
    · exact not_isConj_x_of_base_order_two hn S e hα _ (wreathModelHom_mem S e _)
        (modelHom_x_ne_x2 S e (by omega)).symm
    · exact not_isConj_swap_of_v_order_two hn S e hβ _ (BrauerWong.modelHom_x_mem_modelBase S e)
    · exact not_isConj_swap_of_v_order_two hn S e hβ _
        (BrauerWong.modelHom_x2_mem_modelBase S e)
  · rw [outerAutomizerIndex_modelV]
    exact hβ

theorem wreathed_two_fusion_classification {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    WreathedFusionQD S e ∨ WreathedFusionQ S e ∨ WreathedFusionD S e ∨
      WreathedFusionComplement S e := by
  rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with hα | hα <;>
    rcases modelVNormalizerQuotient_alternatives n hn S e with hβ | hβ
  · exact Or.inr (Or.inr (Or.inr (wreathedFusionComplement_of hn S e hα hβ)))
  · exact Or.inr (Or.inl (wreathedFusionQ_of hn S e hα hβ))
  · exact Or.inr (Or.inr (Or.inl (wreathedFusionD_of hn S e hα hβ)))
  · exact Or.inl (wreathedFusionQD_of hn S e hα hβ)

end Alternatives

end CFSG.QuasiDihedralFusion

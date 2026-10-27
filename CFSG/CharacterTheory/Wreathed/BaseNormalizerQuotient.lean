module

public import CFSG.CharacterTheory.Wreathed.BaseActionAlternatives
public import CFSG.Dihedral.DihedralFusionStepReplacement

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

variable {G : Type u} [Group G]

theorem modelBaseAction_ker {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelBaseAction S e).ker =
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) := by
  unfold modelBaseAction
  rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr (modelBaseEquiv S e).symm).injective,
    Subgroup.normalizerMonoidHom_ker]

@[expose] def modelBaseNormalizerQuotientEquiv {m : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* (modelBaseAction S e).range :=
  (QuotientGroup.quotientMulEquivOfEq (modelBaseAction_ker S e).symm).trans
    (QuotientGroup.quotientKerEquivRange (modelBaseAction S e))

theorem modelBaseNormalizerQuotient_alternatives [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2 ∨
    Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)) := by
  rcases modelBaseImage_alternatives n hn S e with htwo | hsix
  · exact Or.inl ((Nat.card_congr (modelBaseNormalizerQuotientEquiv S e).toEquiv).trans htwo)
  · obtain ⟨esix⟩ := hsix
    exact Or.inr ⟨(modelBaseNormalizerQuotientEquiv S e).trans esix⟩

theorem modelBaseAction_symm_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (g : Subgroup.normalizer (modelBase S e : Set G)) (b : baseSubgroup m) :
    wreathModelHom S e ((modelBaseAction S e g).symm b).val =
      g.val⁻¹ * wreathModelHom S e b.val * g.val := by
  have h := modelBaseAction_coe S e g ((modelBaseAction S e g).symm b)
  rw [MulEquiv.apply_symm_apply] at h
  calc
    wreathModelHom S e ((modelBaseAction S e g).symm b).val =
      g.val⁻¹ * (g.val * wreathModelHom S e
        ((modelBaseAction S e g).symm b).val * g.val⁻¹) * g.val := by group
    _ = g.val⁻¹ * wreathModelHom S e b.val * g.val := by rw [← h]

theorem modelBaseNormalizer_order_two_step_replacement [Finite G]
    {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (g : G) (hg : g ∈ Subgroup.normalizer (modelBase S e : Set G)) :
    ∃ s : G, s ∈ (S : Subgroup G) ∧
      s ∈ Subgroup.normalizer (modelBase S e : Set G) ∧
        ∀ b ∈ modelBase S e, s⁻¹ * b * s = g⁻¹ * b * g := by
  let f := modelBaseAction S e
  have htwo : IsPGroup 2 f.range := by
    apply IsPGroup.of_card (n := 1)
    rw [← Nat.card_congr (modelBaseNormalizerQuotientEquiv S e).toEquiv, hcard]
    rfl
  obtain ⟨s, hs, hsg⟩ := CFSG.GorensteinWalter.hom_to_pGroup_image_on_sylow
    htwo f.rangeRestrict (modelBaseNormalizerSylow S e) ⟨g, hg⟩
  have hsS : s.val ∈ (S : Subgroup G) := by
    rw [modelBaseNormalizerSylow_coe] at hs
    exact hs
  have heq : f s = f ⟨g, hg⟩ := congrArg Subtype.val hsg
  refine ⟨s.val, hsS, s.property, ?_⟩
  intro b hb
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hb
  have hpoint := DFunLike.congr_fun (congrArg MulEquiv.symm heq) (⟨w, hw⟩ : baseSubgroup m)
  have hambient := congrArg (fun b : baseSubgroup m => wreathModelHom S e b.val) hpoint
  rw [modelBaseAction_symm_coe, modelBaseAction_symm_coe] at hambient
  exact hambient

end CFSG.Wreathed

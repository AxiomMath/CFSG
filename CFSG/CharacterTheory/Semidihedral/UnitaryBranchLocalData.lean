module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchLocal
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierLinear

public section

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem exists_unitaryLocalData {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq1 : p ^ f % 4 = 1)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hNcent : N t ≤ Subgroup.center (C t)) (hNcyc : IsCyclic (N t))
    (hNcop : Nat.Coprime (Nat.card (N t)) (p * (p ^ f - 1))) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (κ : C t →* Equiv.Perm (Omega F)),
      UnitaryLocalData t p f F κ := by
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  have hz : (fS (z n) : G) = t := by
    rw [ht, z, map_pow, SubmonoidClass.coe_pow]
    rfl
  have ht2 : orderOf t = 2 := supplied_orderOf hn fS hz
  obtain ⟨F, hFfield, hFfin, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  have hA1 : Nat.card A = 1 :=
    SimpleLayerFrontier.field_group_card_eq_one_of_index_two n hn S fS hG t ht2 hnonab p f F A rho
      data hY
  have hAbot : A = ⊥ := Subgroup.eq_bot_of_card_eq A hA1
  refine ⟨F, hFfield, hFfin, localAction F rho, ?_⟩
  have hpne : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  refine ⟨hp, hpne, hf, data.field_card, hq1, ht2, ?_, ?_, hNcent, hNcyc, hNcop⟩
  ·
    have hker := permutationCover_kernel F A rho data.faithful data.full_image
    ext c
    rw [MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker, ← permutationCover_value F A rho
      data.full_image c]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  ·
    have hk : (kappa t).range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    have hlift : SemilinearOddExtensions.liftedField F A = ⊥ := by
      rw [SemilinearOddExtensions.liftedField, hAbot, Subgroup.map_bot]
    change ((coordinateE F).subtype.comp (rho.comp (kappa t))).range = coordinateD F
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hk, ← MonoidHom.range_eq_map,
      data.full_image, OddFieldLift.Gamma, hlift, sup_bot_eq,
      SemilinearOddExtensions.linearLayer, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (coordinateD_le_E F)]

end CFSG.Semidihedral.UnitaryBranch

module

public import CFSG.Foundations.MaxOrderThompson
public import CFSG.Adapters.GlaubermanZJ
public import CFSG.GroupTheory.Gorenstein.MaxCardThompson

public section

namespace CFSG

section Bounded

variable {G : Type*} [Group G]

theorem Open.thompsonSubgroup_eq_map_maxCardThompson (S : Subgroup G) :
    Open.thompsonSubgroup S = (maxCardThompson S).map S.subtype :=
  (Adapters.leanEval_thompsonSubgroup_eq S).trans (CFSG.thompsonSubgroup_eq_map_maxCardThompson S)

theorem Open.thompsonSubgroup_le_self (S : Subgroup G) : Open.thompsonSubgroup S ≤ S :=
  Open.thompsonSubgroup_eq_map_maxCardThompson S ▸ Subgroup.map_subtype_le _

theorem Open.normalizer_le_normalizer_thompsonSubgroup (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (Open.thompsonSubgroup S : Set G) :=
  Open.thompsonSubgroup_eq_map_maxCardThompson S ▸
    normalizer_le_normalizer_image_of_characteristic S (maxCardThompson S)

end Bounded

section FiniteSubgroup

variable {G : Type*} [Group G]

theorem centerIn_le_thompsonSubgroup_of_finite (S : Subgroup G) [Finite S] :
    centerIn S ≤ thompsonSubgroup S := by
  rw [thompsonSubgroup_eq_map_maxCardThompson, maxCardThompson_eq_orderThompson,
    centerIn_eq_map_center]
  exact Subgroup.map_mono center_le_orderThompson

theorem thompsonSubgroup_ne_bot_of_finite {S : Subgroup G} [Finite S] (hS : S ≠ ⊥) :
    thompsonSubgroup S ≠ ⊥ := by
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS
  obtain ⟨A, hA⟩ := maxOrderAbelianFamily_nonempty (G := S)
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  have hcard : Nat.card (Subgroup.zpowers s) ≤ Nat.card A :=
    hA.2 ▸ card_le_maxAbelianOrder_of_isMulCommutative inferInstance
  intro hJ
  rw [thompsonSubgroup_eq_map_maxCardThompson, maxCardThompson_eq_orderThompson,
    Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective] at hJ
  have hAbot : A = ⊥ := le_bot_iff.mp (hJ ▸ le_orderThompson hA)
  rw [hAbot, Subgroup.card_bot] at hcard
  exact hs (Subgroup.zpowers_eq_bot.mp ((Subgroup.card_le_one_iff_eq_bot _).mp hcard))

theorem thompsonCenter_ne_bot_of_isPGroup {S : Subgroup G} [Finite S] {p : ℕ} (hp : p.Prime)
    (hSp : IsPGroup p S) (hS : S ≠ ⊥) : thompsonCenter S ≠ ⊥ := by
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS
  rw [thompsonCenter_eq_map_maxCardZJ, maxCardZJ_eq_orderZJ, Ne,
    Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective]
  exact orderZJ_ne_bot_of_isPGroup hp hSp

theorem Open.thompsonSubgroup_ne_bot_of_finite {S : Subgroup G} [Finite S] (hS : S ≠ ⊥) :
    Open.thompsonSubgroup S ≠ ⊥ := by
  rw [Adapters.leanEval_thompsonSubgroup_eq]
  exact CFSG.thompsonSubgroup_ne_bot_of_finite hS

end FiniteSubgroup

variable {G : Type*} [Group G] [Finite G]

theorem thompsonAbelianSubgroups_top_eq :
    thompsonAbelianSubgroups (⊤ : Subgroup G) = maxOrderAbelianFamily G := by
  rw [thompsonAbelianSubgroups_top_eq_setOf_isMaxCardAbelian, setOf_isMaxCardAbelian_eq]

theorem image_maxOrderAbelianFamily_eq_thompsonAbelianSubgroups (S : Subgroup G) :
    (fun A : Subgroup S => A.map S.subtype) '' maxOrderAbelianFamily S =
      thompsonAbelianSubgroups S := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨hAc, hmax⟩ := mem_maxOrderAbelianFamily_iff_forall_card_le.mp hA
    refine ⟨Subgroup.map_subtype_le A, inferInstance, fun C hCS hC => ?_⟩
    rw [Subgroup.card_map_of_injective S.subtype_injective,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCS).toEquiv]
    exact hmax _ inferInstance
  · rintro ⟨hBS, hB, hmax⟩
    refine ⟨B.subgroupOf S, mem_maxOrderAbelianFamily_iff_forall_card_le.mpr
      ⟨inferInstance, fun A hA => ?_⟩, Subgroup.map_subgroupOf_eq_of_le hBS⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv,
      ← Subgroup.card_map_of_injective S.subtype_injective]
    exact hmax _ (Subgroup.map_subtype_le A) inferInstance

theorem thompsonSubgroup_top_eq : thompsonSubgroup (⊤ : Subgroup G) = orderThompson G := by
  rw [thompsonSubgroup_top_eq_maxCardThompson, maxCardThompson_eq_orderThompson]

theorem thompsonSubgroup_eq_ambientOrderThompson (S : Subgroup G) :
    thompsonSubgroup S = ambientOrderThompson S := by
  rw [thompsonSubgroup_eq_map_maxCardThompson, maxCardThompson_eq_orderThompson]
  rfl

theorem thompsonCenter_eq_ambientOrderZJ (S : Subgroup G) :
    thompsonCenter S = ambientOrderZJ S := by
  rw [thompsonCenter_eq_map_maxCardZJ, maxCardZJ_eq_orderZJ]
  rfl

theorem Open.thompsonSubgroup_eq_ambientOrderThompson (S : Subgroup G) :
    Open.thompsonSubgroup S = ambientOrderThompson S :=
  (Adapters.leanEval_thompsonSubgroup_eq S).trans (CFSG.thompsonSubgroup_eq_ambientOrderThompson S)

theorem Open.map_center_thompsonSubgroup_eq_ambientOrderZJ (S : Subgroup G) :
    (Subgroup.center (Open.thompsonSubgroup S)).map (Open.thompsonSubgroup S).subtype =
      ambientOrderZJ S := by
  rw [Adapters.leanEval_thompsonSubgroup_eq, ← centerIn_eq_map_center]
  exact CFSG.thompsonCenter_eq_ambientOrderZJ S

end CFSG

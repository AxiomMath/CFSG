module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockCharTwo
public import CFSG.LieType.Chevalley.RootLocalComponentFree

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.LieType.Chevalley

@[expose] noncomputable def centralizerSingletonEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : A) :
    centralizer ({a} : Set A) ≃* centralizer (zpowers (e a) : Set B) :=
  ((centralizer ({a} : Set A)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      ext y
      rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_iff]
      constructor
      · intro h z hz
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hz
        have h1 : Commute (e a) y := by
          have h2 := congrArg e h
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
          exact h2.symm
        exact (h1.zpow_left n).eq
      · intro h
        have h1 := h (e a) (mem_zpowers _)
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact h1.symm))

variable {G : Type*} [Group G] [Finite G]

theorem commuting_block_even_root_model_overgroup_exclusion {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) :
    ¬ ∃ L : Subgroup G, CFSG.Assembly.IsQuasisimple L ∧ blockGroup J ≤ L ∧
      ¬ L ≤ normalizer (blockGroup J : Set G) ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (D : RootWeightDatum k),
        Nonempty (L ⧸ center L ≃* D.group) := by
  rintro ⟨L, hL, hML, hLH, k, _, _, _, D, ⟨e⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht2, hnot⟩ := escaping_block_quotient_non_characteristic_two_centralizer hq heven hJ hΔ
    hL hML hLH
  set u : D.group := e t with hu
  have hu2 : orderOf u = 2 := by rw [hu, MulEquiv.orderOf_eq, ht2]
  have hQp : IsPGroup 2 (zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hu2, pow_one]
  have hQ1 : zpowers u ≠ ⊥ := by
    intro h
    have h1 : u = 1 := by
      rw [← mem_bot, ← h]
      exact mem_zpowers u
    rw [h1, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  obtain ⟨hchar, -⟩ := D.defining_characteristic_root_local_groups_component_free 2 (zpowers u)
    hQp hQ1 _ (Or.inr rfl)
  exact hnot (isCharacteristicP_of_mulEquiv (centralizerSingletonEquiv e t).symm hchar)

end CFSG.LocalAnalysis.ComponentInitial

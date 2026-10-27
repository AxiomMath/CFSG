module

public import CFSG.CharacterTheory.Semidihedral.Local.LayerCoveringCentralizerSupport
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem centralized_or_inverted_local_sylow_prime_has_layer_covering_centralizer {G : Type}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ Nat.card (N t)) (P : Sylow ℓ (N t))
    (hsP : s ∈ Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t))) : Set (C t)))
    (hact : (∀ x : N t, x ∈ P → s * (x : C t) * s⁻¹ = x) ∨
      (∀ x : N t, x ∈ P → s * (x : C t) * s⁻¹ = (x : C t)⁻¹)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let D := Subgroup.centralizer
      (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) : Set (C t))
    (D ⊓ Y).map (nu t) = T₀ := by
  intro T₀ Y D
  have _hunused : ℓ ∣ Nat.card (N t) ∧ s ∈ Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t))) : Set (C t)) := ⟨hℓ, hsP⟩
  have hpackage := actual_simple_layer_matrix_data n hn S0 f0 hG t ht hnonab hcentral hnc p f hp
    hpodd hf hmodel
  obtain ⟨F, hF, hFfin, A, rho, data⟩ := hpackage
  obtain ⟨eta, -, -, -⟩ := data.compatible_layer
  have hT₀perf : Group.IsPerfect T₀ := by
    have : Fintype F := Fintype.ofFinite F
    have h4 : ∃ s : Finset F, s.card = 4 := by
      obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, data.field_card]; omega)
      exact ⟨u, hu⟩
    have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    exact Group.IsPerfect.ofSurjective (f := eta.symm.toMonoidHom) eta.symm.surjective
  have hsJ : s ∈ idOrInv (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t))) := by
    rcases hact with h | h
    · exact Or.inl fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact h x hx
    · exact Or.inr fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact h x hx
  have htJ : tInC t ∈ idOrInv (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t))) :=
    centralizer_le_idOrInv _ (Z_le_centralizer t _ (Subgroup.mem_zpowers _))
  have hUn : ((idOrInv (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)))).map
      (kappa t)).Normal := by
    constructor
    rintro _ ⟨j, hj, rfl⟩ γ
    obtain ⟨b, hb, rfl⟩ := exists_normalizer_kappa_eq t P γ
    exact ⟨b * j * b⁻¹, conj_mem_idOrInv hb hj, by simp only [map_mul, map_inv]⟩
  have hU1 : kappa t s ∈ (idOrInv (((P : Subgroup (N t)).map (N t).subtype :
      Subgroup (C t)))).map (kappa t) := Subgroup.mem_map_of_mem _ hsJ
  have hks := kappa_ne_one_of_involution t ht hs hst
  have hLn : (CFSG.generalizedFitting (Gamma t)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := Gamma t)).2
  have hLU : CFSG.generalizedFitting (Gamma t) ≤ (idOrInv (((P : Subgroup (N t)).map
      (N t).subtype : Subgroup (C t)))).map (kappa t) := by
    have hnorm : (((idOrInv (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)))).map
        (kappa t) ⊓ CFSG.generalizedFitting (Gamma t)).subgroupOf
          (CFSG.generalizedFitting (Gamma t))).Normal :=
      (Subgroup.normal_inf_normal _ _).subgroupOf _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((idOrInv (((P : Subgroup (N t)).map
        (N t).subtype : Subgroup (C t)))).map (kappa t) ⊓
          CFSG.generalizedFitting (Gamma t)).subgroupOf (CFSG.generalizedFitting (Gamma t)))
      with h | h
    · exfalso
      have hbot := (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right
      have hcomm := le_bot_iff.mp (hbot ▸ Subgroup.commutator_le_inf _ _)
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      rw [hcentral] at hle
      exact hks (Subgroup.mem_bot.mp (hle hU1))
    · exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left
  have hT₀J : T₀ ≤ (idOrInv (((P : Subgroup (N t)).map (N t).subtype :
      Subgroup (C t)))).map (nu t) := by
    intro x hx
    obtain ⟨j, hj, hjx⟩ := hLU (Subgroup.mem_comap.mp hx)
    have hker : (nu t j)⁻¹ * x ∈ (barKappa t).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, barKappa_nu]
      change (kappa t j)⁻¹ * barKappa t x = 1
      rw [hjx, inv_mul_cancel]
    rw [barKappa_kernel] at hker
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hker
    refine ⟨j * tInC t ^ k, Subgroup.mul_mem _ hj (Subgroup.zpow_mem _ htJ k), ?_⟩
    rw [map_mul, map_zpow, hk]
    group
  have hT₀D : T₀ ≤ D.map (nu t) := by
    rw [← Subgroup.isPerfect_iff.mp hT₀perf]
    calc ⁅T₀, T₀⁆ ≤ ⁅(idOrInv (((P : Subgroup (N t)).map (N t).subtype :
          Subgroup (C t)))).map (nu t), (idOrInv (((P : Subgroup (N t)).map (N t).subtype :
          Subgroup (C t)))).map (nu t)⁆ := Subgroup.commutator_mono hT₀J hT₀J
      _ = ⁅idOrInv (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t))),
          idOrInv (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)))⁆.map (nu t) :=
        (Subgroup.map_commutator _ _ _).symm
      _ ≤ D.map (nu t) := Subgroup.map_mono (commutator_idOrInv_le _)
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact inf_le_right
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := hT₀D hx
    exact ⟨d, ⟨hd, hx⟩, rfl⟩

end CFSG.Semidihedral.Local

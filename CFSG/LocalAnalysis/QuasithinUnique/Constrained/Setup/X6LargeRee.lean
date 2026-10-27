module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LieType.Ree.LargeReeModelSchreier

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section LargeRee

theorem largeRee_hasUnequalCovers
    (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ U : Subgroup (F4.reeGamma K a), CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧
      HasUnequalCovers (F4.reeGamma K a) U (Nat.card K + 1) (Nat.card K ^ 2 + 1) := by
  classical
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent K a)
      (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hBnorm : F4.reeGamma K a ⊓
      Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) =
        F4.reeFixedBorel K a :=
    reeGamma_inf_normalizer_reeFixedPosUnipotent
  obtain ⟨hmin, hne, -⟩ := large_Ree_minimal_Borel_intersections a K w₀ hw₀
  have hP₀Γ : F4.reeLocalParabolic K a ⟨0, by decide⟩ ≤ F4.reeGamma K a := inf_le_left
  have hP₁Γ : F4.reeLocalParabolic K a ⟨1, by decide⟩ ≤ F4.reeGamma K a := inf_le_left
  have hcov : ∀ A : Subgroup (ModGL F4.tag K), A ≤ F4.reeGamma K a →
      (F4.reeFixedBorel K a ⋖ A ↔ A = F4.reeLocalParabolic K a ⟨0, by decide⟩ ∨
        A = F4.reeLocalParabolic K a ⟨1, by decide⟩) := by
    intro A hA
    rw [covBy_iff_minimal_of_le hA]
    exact hmin A
  have hcov₀ : F4.reeFixedBorel K a ⋖ F4.reeLocalParabolic K a ⟨0, by decide⟩ :=
    (hcov _ hP₀Γ).2 (Or.inl rfl)
  have hcov₁ : F4.reeFixedBorel K a ⋖ F4.reeLocalParabolic K a ⟨1, by decide⟩ :=
    (hcov _ hP₁Γ).2 (Or.inr rfl)
  have hP₀ne : F4.reeLocalParabolic K a ⟨0, by decide⟩ ≠ F4.reeGamma K a := fun h =>
    hcov₀.2 hcov₁.lt (lt_of_le_of_ne (hP₁Γ.trans_eq h.symm) hne.symm)
  have hP₁ne : F4.reeLocalParabolic K a ⟨1, by decide⟩ ≠ F4.reeGamma K a := fun h =>
    hcov₁.2 hcov₀.lt (lt_of_le_of_ne (hP₀Γ.trans_eq h.symm) hne)
  have hgen : F4.reeLocalParabolic K a ⟨0, by decide⟩ ⊔ F4.reeLocalParabolic K a ⟨1, by decide⟩ =
      F4.reeGamma K a := by
    refine le_antisymm (sup_le hP₀Γ hP₁Γ) ?_
    have h := (large_Ree_simple_pair_generation a K hK).le
    exact h.trans (sup_le_sup (large_Ree_local_block_Sylow_action F4 a K ⟨0, by decide⟩).1
      (large_Ree_local_block_Sylow_action F4 a K ⟨1, by decide⟩).1)
  have hrel : ∀ j : Fin F4.fixedOrbitCount, (F4.reeFixedBorel K a).relIndex
      (F4.reeLocalParabolic K a j) = Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1 := by
    intro j
    rw [← ncard_image_coset_eq_relIndex]
    exact (large_Ree_local_block_Sylow_action F4 a K j).2.2.2.2.1
  have hi₀ : (F4.reeFixedBorel K a).relIndex (F4.reeLocalParabolic K a ⟨0, by decide⟩) =
      Nat.card K + 1 := by
    rw [hrel, card_reeFixedOrbitUnipotent_zero hK]
  have hi₁ : (F4.reeFixedBorel K a).relIndex (F4.reeLocalParabolic K a ⟨1, by decide⟩) =
      Nat.card K ^ 2 + 1 := by
    rw [hrel, card_reeFixedOrbitUnipotent_one hK]
  exact ⟨(F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a),
    isSylowTwoOf_subgroupOf_top hUsyl,
    hasUnequalCovers_of_ambient hUsyl hBnorm hcov hP₀Γ hP₁Γ hP₀ne hP₁ne hgen hi₀ hi₁⟩

theorem exists_mulEquiv_largeRee_model
    {X : Type} [Group X] {f : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime),
      1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧ Nonempty (X ≃* F4.reeGamma K a) := by
  obtain ⟨-, -, -, -, ⟨a, ha, hfa⟩, hiso⟩ := large_Ree_model_Schreier X 2 f hX
  obtain ⟨-, a', hfa', K, hKF, hKFin, hK, ⟨e₀⟩⟩ := hX
  have ha' : a' = a := by omega
  subst ha'
  have : Fintype K := Fintype.ofFinite K
  have hcp2 : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hcp : CharP K F4.prime := hcp2
  obtain ⟨E⟩ := hiso a' K hfa hK ⟨e₀⟩
  exact ⟨a', K, hKF, hKFin, hcp, ha, hfa, hK, ⟨E⟩⟩

theorem large_Ree_model_two_extensions
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 f) :
    Subgroup.center X = ⊥ ∧
    TwoGeneratingSylowOvergroups X ∧
    (∀ D : Subgroup (MulAut X), inner X ≤ D →
      IsPGroup 2 (D ⧸ (inner X).subgroupOf D) → ∀ R : Subgroup (MulAut X),
        CFSG.QuasithinUnique.IsSylowTwoOf R D →
          ∃ M₁ M₂ : Subgroup (MulAut X), M₁ ≠ M₂ ∧ M₁ ⋖ D ∧ M₂ ⋖ D ∧ R ≤ M₁ ∧ R ≤ M₂) ∧
    ∀ U : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ →
      HasUnequalCovers X U (2 ^ f + 1) (2 ^ (2 * f) + 1) := by
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨U₀, hU₀, hcov⟩ := largeRee_hasUnequalCovers a K hK'
  have hZC : Subgroup.center (F4.reeGamma K a) = ⊥ := large_Ree_fixed_group_center_trivial a K hK'
  have hne : Nat.card K + 1 ≠ Nat.card K ^ 2 + 1 := by
    intro h
    have h1 : Nat.card K = Nat.card K ^ 2 := Nat.add_right_cancel h
    have h2 : 2 ≤ Nat.card K := by
      rw [hK]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have hgen : TwoGeneratingSylowOvergroups (F4.reeGamma K a) := hcov.twoGenerating hZC hU₀ hne
  have hgenX : TwoGeneratingSylowOvergroups X := hgen.of_mulEquiv e.symm
  refine ⟨?_, hgenX, fun D hD _ R hR => (hgenX D hD R hR).exists_two_maximal, fun U hU => ?_⟩
  · have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
    rw [hZC] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h
  · have h := hcov.of_isSylow e hU₀ hU
    have e2 : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
    rwa [hK, e2] at h

end LargeRee

end CFSG.QuasithinUnique.Setup.X6

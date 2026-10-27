module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal
  Matrix CFSG.Open
open TauCeti.QuadraticMap (orthogonalGroup)
open scoped commutatorElement

section Parity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem commSpace_eichler_le (u w : V) :
    commSpace (eichler Q u w) ≤ Submodule.span K {u, w} := by
  intro y hy
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · rw [eichler_apply h.1 h.2]
    have e : x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u - x =
        polar Q x u • w + (-(polar Q x w + Q w * polar Q x u)) • u := by module
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [eichler_of_not h, LinearEquiv.coe_one, id, sub_self]
    exact Submodule.zero_mem _

theorem span_le_commSpace_eichler [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (hli : LinearIndependent K ![u, w]) :
    Submodule.span K {u, w} ≤ commSpace (eichler Q u w) := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ hli
  have h00 : polar Q u (g 0) = 1 := by simpa using hg 0 0
  have h01 : polar Q u (g 1) = 0 := by simpa using hg 0 1
  have h10 : polar Q w (g 0) = 0 := by simpa using hg 1 0
  have h11 : polar Q w (g 1) = 1 := by simpa using hg 1 1
  have hu1 : u ∈ commSpace (eichler Q u w) := by
    have hmem := sub_mem_commSpace (eichler Q u w) (g 1)
    rw [eichler_apply hu hw, polar_comm Q (g 1) u, polar_comm Q (g 1) w, h01, h11] at hmem
    have e : g 1 + (0 : K) • w - (1 + Q w * 0) • u - g 1 = -u := by module
    rw [e] at hmem
    simpa using Submodule.neg_mem _ hmem
  have hw1 : w ∈ commSpace (eichler Q u w) := by
    have hmem := sub_mem_commSpace (eichler Q u w) (g 0)
    rw [eichler_apply hu hw, polar_comm Q (g 0) u, polar_comm Q (g 0) w, h00, h10] at hmem
    have e : g 0 + (1 : K) • w - (0 + Q w * 1) • u - g 0 = w - Q w • u := by module
    rw [e] at hmem
    have := Submodule.add_mem _ hmem (Submodule.smul_mem _ (Q w) hu1)
    simpa using this
  refine Submodule.span_le.mpr ?_
  rintro z (rfl | rfl)
  · exact hu1
  · exact hw1

theorem commSpace_one_eq_bot : commSpace (1 : V ≃ₗ[K] V) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  rw [Submodule.mem_bot, LinearEquiv.coe_one, id, sub_self]

theorem even_finrank_commSpace_eichler [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (u w : V) :
    Even (finrank K (commSpace (eichler Q u w))) := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · by_cases hli : LinearIndependent K ![u, w]
    · have heq : commSpace (eichler Q u w) = Submodule.span K {u, w} :=
        le_antisymm (commSpace_eichler_le u w) (span_le_commSpace_eichler hQ h.1 h.2 hli)
      rw [heq]
      have := finrank_span_eq_card hli
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Fintype.card_fin] at this
      rw [this]
      exact even_two
    · have h1 : eichler Q u w = 1 := by
        rw [LinearIndependent.pair_iff] at hli
        push_neg at hli
        obtain ⟨s, t, hst, hne⟩ := hli
        by_cases ht : t = 0
        · subst ht
          have hs : s ≠ 0 := fun hs => hne hs rfl
          rw [zero_smul, add_zero] at hst
          have hu0 : u = 0 := (smul_eq_zero.mp hst).resolve_left hs
          rw [hu0]
          exact eichler_zero_left Q w
        · have hw : w = (-(t⁻¹ * s)) • u := by
            have : t • w = -(s • u) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
            calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
              _ = (-(t⁻¹ * s)) • u := by rw [this, smul_neg, smul_smul, neg_smul]
          have := eichler_add_smul_self (Q := Q) h.1 0 (-(t⁻¹ * s))
          rw [zero_add, ← hw, eichler_zero_right] at this
          exact this
      rw [h1, commSpace_one_eq_bot, finrank_bot]
      exact ⟨0, rfl⟩
  · rw [eichler_of_not h, commSpace_one_eq_bot, finrank_bot]
    exact ⟨0, rfl⟩

end Parity

section Omega

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem eichler_mem_omegaGroup_general (hQ : (polarBilin Q).Nondegenerate) (u w : V) :
    eichler Q u w ∈ omegaGroup Q hQ :=
  ⟨eichler_mem_orthogonalGroup Q u w, even_finrank_commSpace_eichler hQ u w⟩

theorem commutator_le_omegaGroup (hQ : (polarBilin Q).Nondegenerate) :
    ⁅orthogonalGroup Q, orthogonalGroup Q⁆ ≤ omegaGroup Q hQ := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  let a : orthogonalGroup Q := ⟨g, hg⟩
  let b : orthogonalGroup Q := ⟨h, hh⟩
  have h1 : dicksonHom Q hQ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have h2 : ⁅a, b⁆ ∈ (dicksonHom Q hQ).ker := h1
  rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem omegaGroup_eq_commutator [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate)
    (h2 : (⁅orthogonalGroup Q, orthogonalGroup Q⁆).relIndex (orthogonalGroup Q) = 2) :
    omegaGroup Q hQ = ⁅orthogonalGroup Q, orthogonalGroup Q⁆ := by
  have hle := commutator_le_omegaGroup hQ
  have hΩO : omegaGroup Q hQ ≤ orthogonalGroup Q := omegaGroup_le Q hQ
  have h3 := Subgroup.relIndex_mul_relIndex ⁅orthogonalGroup Q, orthogonalGroup Q⁆
    (omegaGroup Q hQ) (orthogonalGroup Q) hle hΩO
  rw [h2, relIndex_omegaGroup Q hQ] at h3
  have h4 : (⁅orthogonalGroup Q, orthogonalGroup Q⁆).relIndex (omegaGroup Q hQ) = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h4) hle

end Omega

section Minus

open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  coe_quadMinus)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
  (finrank_minusSpace_small exists_quadMinus_ne_zero_small)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem quadMinus_three_derived (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (⁅orthogonalGroup (quadMinus 3 F b c), orthogonalGroup (quadMinus 3 F b c)⁆).relIndex
        (orthogonalGroup (quadMinus 3 F b c)) = 2 ∧
      ∀ g ∈ orthogonalGroup (quadMinus 3 F b c), Odd (orderOf g) →
        g ∈ ⁅orthogonalGroup (quadMinus 3 F b c), orthogonalGroup (quadMinus 3 F b c)⁆ := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, hidx, -, hodd⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction (quadMinus 3 F b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr)
      (finrank_minusSpace_small (n := 3) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_small hirr (by norm_num) U hU)
  rw [hcomm]
  exact ⟨hidx, hodd⟩

theorem eichler_mem_commutator (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (u w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :
    eichler (quadMinus 3 F b c) u w ∈
      ⁅orthogonalGroup (quadMinus 3 F b c), orthogonalGroup (quadMinus 3 F b c)⁆ := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  rw [← omegaGroup_eq_commutator hQ (quadMinus_three_derived hirr).1]
  exact eichler_mem_omegaGroup_general hQ u w

theorem mem_statedOmega_iff (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
    g ∈ StatedOmega (StatedQuadMinus 3 F b c) ↔
      toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g ∈
        ⁅orthogonalGroup (quadMinus 3 F b c), orthogonalGroup (quadMinus 3 F b c)⁆ := by
  rw [statedOmega_eq_comap (coe_quadMinus 3 F b c)]
  rfl

theorem eichler_mem_statedOmega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (u w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :
    ∃ A ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x =
        eichler (quadMinus 3 F b c) u w x := by
  refine ⟨(toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm
    (eichler (quadMinus 3 F b c) u w), ?_, fun x => ?_⟩
  · rw [mem_statedOmega_iff, MulEquiv.apply_symm_apply]
    exact eichler_mem_commutator hirr u w
  · rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]

theorem odd_isometry_mem_omega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hg : ∀ v, StatedQuadMinus 3 F b c
      ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v)
        = StatedQuadMinus 3 F b c v)
    (hodd : Odd (orderOf g)) : g ∈ StatedOmega (StatedQuadMinus 3 F b c) := by
  rw [mem_statedOmega_iff]
  refine (quadMinus_three_derived hirr).2 _ ?_ ?_
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [toLinEquiv_apply, coe_quadMinus 3 F b c]
    exact hg x
  · rwa [MulEquiv.orderOf_eq]

end Minus

end CFSG.LocalAnalysis.RankThreeUC

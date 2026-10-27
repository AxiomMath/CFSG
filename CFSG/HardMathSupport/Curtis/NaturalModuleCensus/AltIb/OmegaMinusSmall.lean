module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Sp
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixExtract

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Module QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Open CFSG.AGLEmbedding.LieOut
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)
open scoped MatrixGroups commutatorElement

theorem isQuasisimple_of_simple_nonabelian {G : Type} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : CFSG.Open.IsQuasisimple G := by
  obtain ⟨a, b, hab⟩ := h
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      have h' : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← _root_.commutator_def, h, Subgroup.mem_bot, commutatorElement_def] at h'
      exact hab (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h'))
    · exact h
  · have e : G ⧸ Subgroup.center G ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

section Small

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

omit [Finite F] [CharP F 2] in
theorem finrank_minusSpace_small {n : ℕ} (hn : 1 ≤ n) :
    finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

theorem exists_quadMinus_ne_zero_small (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hn : 1 ≤ n) (U : Submodule F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F))
    (hU : finrank F U = n) : ∃ u ∈ U, quadMinus n F b c u ≠ 0 := by
  by_contra h
  push Not at h
  refine CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hn hirr ⟨U, ?_, h⟩
  rw [hU, finrank_minusSpace_small hn]

theorem nonempty_range_equiv_statedOmega {n : ℕ} {S : Type} [Group S]
    (ρ : S →* ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)))
    (hr : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)⁆ = ρ.range) :
    Nonempty (ρ.range ≃* StatedOmega (StatedQuadMinus n F b c)) := by
  have h1 : StatedOmega (StatedQuadMinus n F b c) =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c),
          TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)⁆.map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          F).symm.toMonoidHom := by
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (coe_quadMinus n F b c),
      Subgroup.comap_equiv_eq_map_symm']
  exact ⟨((MulEquiv.subgroupCongr hr.symm).trans
    ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      F).symm.subgroupMap _)).trans (MulEquiv.subgroupCongr h1.symm)⟩

theorem isQuasisimple_of_range_equiv {G H : Type} [Group G] [Group H] [IsSimpleGroup G]
    (hna : ¬ ∀ x y : G, x * y = y * x) (e : G ≃* H) : CFSG.Open.IsQuasisimple H := by
  have : IsSimpleGroup H := e.symm.isSimpleGroup
  refine isQuasisimple_of_simple_nonabelian ?_
  by_contra hH
  push Not at hH
  apply hna
  intro x y
  apply e.injective
  rw [map_mul, map_mul]
  exact hH _ _

theorem isQuasisimple_statedOmega_quadMinus_two (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Open.IsQuasisimple ↥(StatedOmega (StatedQuadMinus 2 F b c)) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hs, -, hna, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction (quadMinus 2 F b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 2 F hirr)
      (finrank_minusSpace_small (n := 2) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_small hirr (by norm_num) U hU)
  obtain ⟨e⟩ := nonempty_range_equiv_statedOmega ρ hcomm
  exact isQuasisimple_of_range_equiv hna e

theorem isQuasisimple_statedOmega_quadMinus_three (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Open.IsQuasisimple ↥(StatedOmega (StatedQuadMinus 3 F b c)) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hs, -, hna, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction (quadMinus 3 F b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr)
      (finrank_minusSpace_small (n := 3) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_small hirr (by norm_num) U hU)
  obtain ⟨e⟩ := nonempty_range_equiv_statedOmega ρ hcomm
  exact isQuasisimple_of_range_equiv hna e

theorem omegaMinusSmallQS : OmegaMinusSmallQS := by
  intro m F _ _ _ b c hirr h2 h3
  interval_cases m
  · exact isQuasisimple_statedOmega_quadMinus_two hirr
  · exact isQuasisimple_statedOmega_quadMinus_three hirr

theorem omegaMinus_four_noAp (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hpq : p ∣ Nat.card F - 1) :
    NoAp p (↥(Ωm 1 F b c) ⧸ Subgroup.center ↥(Ωm 1 F b c)) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, hinj, -, hcomm, -, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction (quadMinus 2 F b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 2 F hirr)
      (finrank_minusSpace_small (n := 2) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_small hirr (by norm_num) U hU)
  obtain ⟨e⟩ := nonempty_range_equiv_statedOmega ρ hcomm
  have := D.finite_E
  have : CharP E 2 := CFSG.RankThree.PartOne.KCOrthogonal.charP_two_of_algebra (K := F)
  have hq : p ∣ Nat.card E - 1 := by
    rw [D.card_E]
    have := Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 2
    simpa using hpq.trans this
  let e' : SL(2, E) ≃* StatedOmega (StatedQuadMinus 2 F b c) :=
    (MonoidHom.ofInjective hinj).trans e
  exact CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.noAp_center_quotient_of_surjective
    e'.symm.toMonoidHom (MulEquiv.surjective _)
    (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell.noAp_sl2 hp57 hq)

end Small

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

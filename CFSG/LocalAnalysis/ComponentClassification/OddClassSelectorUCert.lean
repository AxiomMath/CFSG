module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalFourGroupCommutant
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module CFSG.ComponentClassification.RestrictedStd CFSG.Assembly.LowTwoRank

theorem orth_component_false {k : Type} [Field k] [Finite k] {W : Type} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {ℓ j : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 1 ≤ j)
    (hk : Nat.card k = ℓ ^ j) (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate)
    (h5 : 5 ≤ finrank k W) {H : Type*} [Group H]
    (F : H ≃* TauCeti.QuadraticMap.orthogonalGroup Q) {Y : Subgroup H} (hY : CFSG.IsComponent Y)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) : False := by
  classical
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hL' := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent F hY
  have hq := OddSelector.commutator_orthogonalGroup_quasisimple hodd Q hQ h5
  have hrange := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hL' hq
  obtain ⟨τ, hτ⟩ := OddSelector.exists_sp_four_hom hodd Q hQ h5
  have : Group.IsPerfect (StatedSp 2 k) := OddSelector.isPerfect_statedSp le_rfl hodd
  have hτr : ∀ x, τ x ∈ Y.map F.toMonoidHom := fun x => by
    rw [hrange]
    exact OddSelector.map_mem_commutator_of_isPerfect τ x
  exact false_of_smallSource hs (OddSelector.not_small_source_of_sp_cover le_rfl hℓ hℓ2 hj hk _
    (ker_comp_codRestrict_le_center τ hτ hτr
      (Y.equivMapOfInjective F.toMonoidHom F.injective).symm σ hσk))

theorem false_of_sl_two {k : Type} [Field k] [Finite k] {ℓ j : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hj : 1 ≤ j) (hk : Nat.card k = ℓ ^ j) (h3 : ℓ ^ j ≠ 3) {X' : Type} [Group X']
    {X : Subgroup X'} (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) k) (hs : SmallSource X) :
    False := by
  classical
  have : CharP k ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hj hk
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq k ℓ]; exact hℓ2)
  have hq2 : ℓ ^ j ≠ 2 := fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
    (h ▸ dvd_pow_self ℓ (by omega)))
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) k) ∈
      center (Matrix.SpecialLinearGroup (Fin 2) k) := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    simp
  have hne : (-1 : Matrix.SpecialLinearGroup (Fin 2) k) ≠ 1 := by
    intro h1
    have h01 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) k =>
      (g : Matrix (Fin 2) (Fin 2) k) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h01
    apply h2
    linear_combination -h01
  have hmem : e.symm (-1) ∈ center X := by
    rw [← Subgroup.map_center_eq e.symm]
    exact ⟨-1, hneg, rfl⟩
  have hz : orderOf (⟨e.symm (-1), hmem⟩ : center X) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      change e.symm (-1) ^ 2 = 1
      rw [← map_pow, show (-1 : Matrix.SpecialLinearGroup (Fin 2) k) ^ 2 = 1 by
        rw [sq, neg_one_mul, neg_neg], map_one]
    · intro h1
      apply hne
      have h3 := congrArg (fun z : center X => e (z : X)) h1
      simpa using h3
  have hZeven : Even (Nat.card (center X)) := even_iff_two_dvd.mpr (hz ▸ orderOf_dvd_natCard _)
  let eQ : X ⧸ center X ≃* StatedProj (StatedSL 2 k) :=
    (QuotientGroup.congr (center X) (center (Matrix.SpecialLinearGroup (Fin 2) k)) e
      (Subgroup.map_center_eq e)).trans (projectiveSpecialLinearGroupEquivStatedProj 2 k)
  have hX : StatedClassicalModel (X ⧸ center X) .PSL 2 ℓ j :=
    SectionRank.statedClassicalModel_of_mulEquiv eQ
      (OddSelector.statedClassicalModel_psl_two hℓ hj hk hq2 h3)
  obtain ⟨-, -, h34⟩ :=
    UnbalancingLocal.small_standard_source_projective_linear_two_field_parameters_stated hX
  rcases hs with ⟨-, -, -, -, -, -, -, hodd⟩ | ⟨-, hodd⟩ | h
  · exact (Nat.not_even_iff_odd.mpr hodd) hZeven
  · exact (Nat.not_even_iff_odd.mpr hodd) hZeven
  · exact h34 (statedClassicalModel_of_lieModel_psl h)

end CFSG.ComponentClassification.OddClassSelector

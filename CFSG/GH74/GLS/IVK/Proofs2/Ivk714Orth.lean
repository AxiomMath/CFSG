module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714A7
public import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalFourGroupCommutant
public import CFSG.LocalAnalysis.ComponentInitial.SimpleOrder33792

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Module QuadraticMap Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open TauCeti.QuadraticMap (orthogonalGroup)
open scoped MatrixGroups

theorem exists_surjective_of_range_eq {G H : Type*} [Group G] [Group H] (f : G →* H)
    {Y : Subgroup H} (h : f.range = Y) : ∃ σ : G →* ↥Y, Function.Surjective σ := by
  refine ⟨f.codRestrict Y (fun g => h ▸ (⟨g, rfl⟩ : f g ∈ f.range)), fun y => ?_⟩
  have hy : (y : H) ∈ f.range := h ▸ y.2
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, Subtype.ext hg⟩

theorem five_le_card_of_odd {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : Nat.card F ≠ 3) : 5 ≤ Nat.card F := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨j, hj⟩ := hodd
  omega

variable {k : Type} [Field k] [Finite k] {W : Type} [AddCommGroup W] [Module k W]
  [FiniteDimensional k W]

theorem orth_dim34_component_exists_sl2 (hodd : Odd (Nat.card k)) (Q : QuadraticForm k W)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank k W = 3 ∨ finrank k W = 4)
    {B : Subgroup (orthogonalGroup Q)} (hB : CFSG.IsComponent B) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Odd (Nat.card F') ∧ 5 ≤ Nat.card F' ∧
      ∃ σ : Matrix.SpecialLinearGroup (Fin 2) F' →* ↥B, Function.Surjective σ := by
  classical
  have hsolv : Group.IsSolvable (orthogonalGroup Q) → False := fun hs => by
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective B)
    have : Nontrivial B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
    have : Group.IsPerfect B := hB.1.1
    exact Group.IsPerfect.not_isSolvable B inferInstance
  rcases hd with hd3 | hd4
  ·
    by_cases hq3 : Nat.card k = 3
    · exfalso
      have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
        (Or.inl ⟨hodd, Or.inl hd3⟩)
      obtain ⟨hexc, -⟩ := hcov
      obtain ⟨hprime, -⟩ := hexc (Or.inl ⟨hd3, hq3⟩)
      exact hsolv (isSolvable_of_prime_dvd_card_eq_or_eq hprime)
    · obtain ⟨d, ψ, e, hψ, he, hcomm, hq, -⟩ := orthogonal_three_derived hodd hq3 Q hQ hd3
      have hBeq : B = commutator (orthogonalGroup Q) := eq_commutator_of_isComponent hB hq
      obtain ⟨σ, hσ⟩ := exists_surjective_of_range_eq
        (e.symm.toMonoidHom.comp
          (CatalogueBOrthogonal.traceZeroOrthogonalAction.comp
            (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) k →*
              GL (Fin 2) k))) (Y := B) (by
        rw [hBeq, hcomm, MonoidHom.range_comp]
        rfl)
      exact ⟨k, inferInstance, inferInstance, hodd, five_le_card_of_odd hodd hq3, σ, hσ⟩
  ·
    by_cases hS : ∃ S : Submodule k W, finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0
    ·
      by_cases hq3 : Nat.card k = 3
      · exfalso
        have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
          (Or.inr (Or.inr ⟨hd4, hS⟩))
        obtain ⟨hexc, -⟩ := hcov
        obtain ⟨hprime, -⟩ := hexc (Or.inr ⟨⟨hd4, hS⟩, Or.inr hq3⟩)
        exact hsolv (isSolvable_of_prime_dvd_card_eq_or_eq hprime)
      · have hq2 : Nat.card k ≠ 2 := by
          intro h2
          rw [h2] at hodd
          exact (Nat.not_odd_iff_even.mpr even_two) hodd
        obtain ⟨-, e, -, -, hsup, hq₁, hq₂, hn₁, hn₂, -⟩ :=
          orthogonal_split_four_derived hq2 hq3 Q hQ hd4 hS
        rcases eq_or_eq_of_isComponent_of_commutator_eq_sup hB hsup hq₁ hq₂ hn₁ hn₂ with h | h
        · obtain ⟨σ, hσ⟩ := exists_surjective_of_range_eq
            (e.symm.toMonoidHom.comp ((CatalogueBOrthogonalFourSplit.specialRho (K := k)).comp (MonoidHom.inl _ _))) (Y := B)
            (by rw [h, determinantLeftFactor, MonoidHom.range_comp])
          exact ⟨k, inferInstance, inferInstance, hodd, five_le_card_of_odd hodd hq3, σ, hσ⟩
        · obtain ⟨σ, hσ⟩ := exists_surjective_of_range_eq
            (e.symm.toMonoidHom.comp ((CatalogueBOrthogonalFourSplit.specialRho (K := k)).comp (MonoidHom.inr _ _))) (Y := B)
            (by rw [h, determinantRightFactor, MonoidHom.range_comp])
          exact ⟨k, inferInstance, inferInstance, hodd, five_le_card_of_odd hodd hq3, σ, hσ⟩
    ·
      obtain ⟨δ, hδ, d, ψ, e, hψ, he, hcomm, hq, -⟩ :=
        orthogonal_nonsplit_four_derived hodd Q hQ hd4 hS
      have : Fact (¬ IsSquare (δ : k)) := ⟨hδ⟩
      have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
      have hBeq : B = commutator (orthogonalGroup Q) := eq_commutator_of_isComponent hB hq
      obtain ⟨σ, hσ⟩ := exists_surjective_of_range_eq
        (e.symm.toMonoidHom.comp
          (CatalogueBOrthogonalFourNonsplit.specialRho (δ : k) h2)) (Y := B) (by
        rw [hBeq, hcomm, MonoidHom.range_comp]
        rfl)
      have hcard : Nat.card (CatalogueBOrthogonalFourNonsplit.extension (δ : k)) =
          Nat.card k ^ 2 := CatalogueBOrthogonalFourNonsplit.extension_card (δ : k)
      have hk3 : 3 ≤ Nat.card k := by
        have h1 : 1 < Nat.card k := Finite.one_lt_card
        obtain ⟨j, hj⟩ := hodd
        omega
      refine ⟨CatalogueBOrthogonalFourNonsplit.extension (δ : k), inferInstance, inferInstance,
        ?_, ?_, σ, hσ⟩
      · rw [hcard]
        exact hodd.pow
      · rw [hcard]
        nlinarith

theorem false_of_orth_dim34_component (hodd : Odd (Nat.card k)) (Q : QuadraticForm k W)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank k W = 3 ∨ finrank k W = 4) {H : Type*}
    [Group H] (F : H ≃* orthogonalGroup Q) {Y : Subgroup H} (hY : CFSG.IsComponent Y)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hX : Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 7))) : False := by
  obtain ⟨F', _, _, hodd', h5, σ₀, hσ₀⟩ :=
    orth_dim34_component_exists_sl2 hodd Q hQ hd (isComponent_map_of_isComponent F hY)
  obtain ⟨e₀⟩ := hX
  let ψ : ↥Y ≃* ↥(Y.map F.toMonoidHom) := Y.equivMapOfInjective F.toMonoidHom F.injective
  exact not_surjective_sl2_alt7 hodd' h5
    ((e₀.toMonoidHom.comp (QuotientGroup.mk' (center X))).comp
      (σ.comp (ψ.symm.toMonoidHom.comp σ₀)))
    ((e₀.surjective.comp (QuotientGroup.mk'_surjective _)).comp
      (hσs.comp (ψ.symm.surjective.comp hσ₀)))

end CFSG.GH74.GLS.IVK.Proofs2

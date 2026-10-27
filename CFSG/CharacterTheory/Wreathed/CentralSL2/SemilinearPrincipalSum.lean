module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalEquality

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Family

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def principalFamilyH :
    Set (SemilinearExtension F b m hm heven Sigma hSigma → ℂ) :=
  {χ | ∃ (P : PrincipalSeriesParameter F b m) (ρ : parameterStabilizer hSigma P →* ℂˣ),
    P.1.1 ≠ 1 ∧ χ = principalInduced hSigma P ρ}

theorem principalFamilyH_subset (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma)) :
    principalFamilyH (hm := hm) (heven := heven) hSigma ⊆
      BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) := by
  rintro χ ⟨P, ρ, hP, rfl⟩
  exact ((principal_clifford hSigma hb hd hP).1 ρ).1

theorem principalFamilyH_finite (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma)) :
    (principalFamilyH (hm := hm) (heven := heven) hSigma).Finite :=
  (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite _).subset
    (principalFamilyH_subset hSigma hb hd)

theorem mem_principalFamilyH_iff (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {χ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ}
    (hχ : χ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma)) :
    (∃ P : PrincipalSeriesParameter F b m, P.1.1 ≠ 1 ∧
      0 < BlocksInnerProduct (fun g => χ (SemidirectProduct.inl g))
        (principalSeries F b m hm heven (torusCharacter F b m hm heven P))) ↔
      χ ∈ principalFamilyH hSigma := by
  constructor
  · rintro ⟨P, hP, hpos⟩
    obtain ⟨ρ, rfl⟩ := ((principal_clifford hSigma hb hd hP).2.2.1 χ hχ).mp hpos
    exact ⟨P, ρ, hP, rfl⟩
  · rintro ⟨P, ρ, hP, rfl⟩
    exact ⟨P, hP, ((principal_clifford hSigma hb hd hP).2.2.1 _ hχ).mpr ⟨ρ, rfl⟩⟩

end Family

section Sum

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def principalBase :
    Set (CentralExtension F b m hm heven → ℂ) :=
  (fun P => principalSeries F b m hm heven (torusCharacter F b m hm heven P)) ''
    {P : PrincipalSeriesParameter F b m | P.1.1 ≠ 1}

theorem principalBase_finite :
    (principalBase (F := F) (b := b) (hm := hm) (heven := heven)).Finite := by
  have := finite_splitTorus_characters (F := F) (b := b) (hm := hm) (heven := heven)
  have hfin : Finite (PrincipalSeriesParameter F b m) :=
    Finite.of_injective _ (torusCharacter_injective F b m hm heven)
  exact Set.Finite.image _ (Set.toFinite _)

@[expose] def liesAbove (χ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ)
    (ψ : CentralExtension F b m hm heven → ℂ) : Prop :=
  0 < BlocksInnerProduct (fun g => χ (SemidirectProduct.inl g)) ψ

theorem degree_eq_card_above (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1)
    (ρ : parameterStabilizer hSigma P →* ℂˣ) :
    principalInduced (hm := hm) (heven := heven) hSigma P ρ 1 =
      ((Nat.card F : ℂ) + 1) * ((principalBase_finite (F := F) (b := b) (hm := hm)
        (heven := heven)).toFinset.filter
          fun ψ => liesAbove hSigma (principalInduced hSigma P ρ) ψ).card := by
  obtain ⟨hirr, -, -, hrest, -⟩ := principal_clifford (hm := hm) (heven := heven) hSigma hb hd hP
  obtain ⟨C, hC⟩ := CFSG.Wreathed.exists_leftCoset_reps (parameterStabilizer hSigma P)
  obtain ⟨hsum, hdist, hmult⟩ := hrest C hC
  have hσP : ∀ σ : Sigma, (fieldParameter hSigma σ P).1.1 ≠ 1 := by
    intro σ h1
    apply hP
    have h2 : P = fieldParameter hSigma σ⁻¹ (fieldParameter hSigma σ P) := by
      rw [← fieldParameter_mul, inv_mul_cancel, fieldParameter_one]
    rw [h2, fieldParameter_fst, h1]
    rfl
  have hfilter : (principalBase_finite (F := F) (b := b) (hm := hm)
      (heven := heven)).toFinset.filter
        (fun ψ => liesAbove hSigma (principalInduced (hm := hm) (heven := heven) hSigma P ρ) ψ) =
      C.image fun σ => principalSeries F b m hm heven
        (torusCharacter F b m hm heven (fieldParameter hSigma σ P)) := by
    ext ψ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image]
    constructor
    · rintro ⟨⟨P', hP', rfl⟩, habove⟩
      unfold liesAbove at habove
      rw [hsum ρ, CFSG.Wreathed.blocksInnerProduct_finset_sum_left] at habove
      by_contra hnot
      rw [Finset.sum_eq_zero fun σ hσ => by
        have hirrσ := principalSeries_mem_blocksIrr F b m hm heven hb _ (hσP σ)
        have hirrP' := principalSeries_mem_blocksIrr F b m hm heven hb _ hP'
        have h3 := blocksInnerProduct_irreducible ⟨_, hirrσ⟩ ⟨_, hirrP'⟩
        change BlocksInnerProduct (principalSeries F b m hm heven
          (torusCharacter F b m hm heven (fieldParameter hSigma σ P)))
            (principalSeries F b m hm heven (torusCharacter F b m hm heven P')) = _ at h3
        rw [h3, ite_eq_right]
        intro heq
        exact hnot ⟨σ, hσ, congrArg Subtype.val heq⟩] at habove
      exact lt_irrefl 0 habove
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨⟨fieldParameter hSigma σ P, hσP σ, rfl⟩, ?_⟩
      unfold liesAbove
      rw [hmult ρ σ hσ]
      exact one_pos
  rw [hfilter, Finset.card_image_of_injOn fun σ hσ σ' hσ' h => by
    by_contra hne
    exact hdist σ hσ σ' hσ' hne h, card_coset_reps _ C hC, (hirr ρ).2]
  ring

theorem sum_degree_above (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1) :
    ∑ χ ∈ (principalFamilyH_finite (hm := hm) (heven := heven) hSigma hb hd).toFinset.filter
        (fun χ => liesAbove hSigma χ
          (principalSeries F b m hm heven (torusCharacter F b m hm heven P))), χ 1 =
      (Nat.card Sigma : ℂ) * ((Nat.card F : ℂ) + 1) := by
  obtain ⟨hirr, hinj, hiff, -, -⟩ := principal_clifford (hm := hm) (heven := heven) hSigma hb hd hP
  have hcyc : IsCyclic (parameterStabilizer hSigma P) := by
    have : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
    infer_instance
  let _ : CommGroup (parameterStabilizer hSigma P) := IsCyclic.commGroup
  have := finite_hom_units_of_isCyclic (parameterStabilizer hSigma P)
  have : Fintype (parameterStabilizer hSigma P →* ℂˣ) := Fintype.ofFinite _
  have hfilter : (principalFamilyH_finite (hm := hm) (heven := heven) hSigma hb hd).toFinset.filter
      (fun χ => liesAbove hSigma χ
        (principalSeries F b m hm heven (torusCharacter F b m hm heven P))) =
      Finset.univ.image (principalInduced (hm := hm) (heven := heven) hSigma P) := by
    ext χ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hχ, habove⟩
      obtain ⟨ρ, rfl⟩ := (hiff χ (principalFamilyH_subset hSigma hb hd hχ)).mp habove
      exact ⟨ρ, rfl⟩
    · rintro ⟨ρ, rfl⟩
      exact ⟨⟨P, ρ, hP, rfl⟩, (hiff _ (hirr ρ).1).mpr ⟨ρ, rfl⟩⟩
  rw [hfilter, Finset.sum_image fun ρ _ ρ' _ h => hinj h]
  simp_rw [fun ρ => (hirr ρ).2]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    card_hom_units_of_isCyclic, ← mul_assoc, ← Nat.cast_mul,
    Subgroup.card_mul_index (parameterStabilizer hSigma P)]

theorem sum_sq_principalFamilyH (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma)) :
    ∑ χ ∈ (principalFamilyH_finite (hm := hm) (heven := heven) hSigma hb hd).toFinset, χ 1 ^ 2 =
      ((Nat.card Sigma * m * (Nat.card F - 2) * (Nat.card F + 1) ^ 2 / 2 : ℕ) : ℂ) := by
  set famFin := (principalFamilyH_finite (hm := hm) (heven := heven) hSigma hb hd).toFinset
    with hfamFin
  set baseFin := (principalBase_finite (F := F) (b := b) (hm := hm) (heven := heven)).toFinset
    with hbaseFin
  have hdeg : ∀ χ ∈ famFin, χ 1 = ((Nat.card F : ℂ) + 1) *
      (baseFin.filter fun ψ => liesAbove hSigma χ ψ).card := by
    intro χ hχ
    rw [hfamFin, Set.Finite.mem_toFinset] at hχ
    obtain ⟨P, ρ, hP, rfl⟩ := hχ
    exact degree_eq_card_above hSigma hb hd hP ρ
  have hstep : ∀ χ ∈ famFin, χ 1 ^ 2 = ((Nat.card F : ℂ) + 1) *
      ∑ ψ ∈ baseFin, if liesAbove hSigma χ ψ then χ 1 else 0 := by
    intro χ hχ
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    calc χ 1 ^ 2 = ((Nat.card F : ℂ) + 1) *
          ((baseFin.filter fun ψ => liesAbove hSigma χ ψ).card) * χ 1 := by
          rw [sq, ← hdeg χ hχ]
      _ = _ := by ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ ψ ∈ baseFin, (∑ χ ∈ famFin, if liesAbove hSigma χ ψ then χ 1 else 0) =
      (Nat.card Sigma : ℂ) * ((Nat.card F : ℂ) + 1) := by
    intro ψ hψ
    rw [hbaseFin, Set.Finite.mem_toFinset] at hψ
    obtain ⟨P, hP, rfl⟩ := hψ
    rw [← Finset.sum_filter]
    exact sum_degree_above hSigma hb hd hP
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  have hcardBase : baseFin.card = m * (Nat.card F - 2) / 2 := by
    rw [hbaseFin, ← Set.ncard_eq_toFinset_card _ principalBase_finite]
    exact principalSeries_ncard F b m hm heven hb
  rw [hcardBase]
  obtain ⟨k, hk⟩ := heven
  have hq : 2 ≤ Nat.card F := two_le_card F
  have e1 : m * (Nat.card F - 2) / 2 = k * (Nat.card F - 2) := by
    rw [hk, show (k + k) * (Nat.card F - 2) = 2 * (k * (Nat.card F - 2)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  have e2 : Nat.card Sigma * m * (Nat.card F - 2) * (Nat.card F + 1) ^ 2 / 2 =
      Nat.card Sigma * k * (Nat.card F - 2) * (Nat.card F + 1) ^ 2 := by
    rw [hk, show Nat.card Sigma * (k + k) * (Nat.card F - 2) * (Nat.card F + 1) ^ 2 =
      2 * (Nat.card Sigma * k * (Nat.card F - 2) * (Nat.card F + 1) ^ 2) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [e1, e2]
  push_cast [Nat.cast_sub hq]
  ring

end Sum

end CFSG.Wreathed.CentralSL2

module

public import CFSG.CharacterTheory.Wreathed.FourPointCompleteModelCharacters
public import CFSG.CharacterTheory.Wreathed.SelfcentralizingUniqueBlock
public import CFSG.CharacterTheory.Wreathed.NormalComplementQuotientBlock
public import CFSG.CharacterTheory.BlockBasics.Bridge

public noncomputable section

namespace CFSG.Wreathed.FourPointCompleteModel

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.FourPointLifts
open CFSG.Wreathed.CyclicCentralSL2Extension

open scoped Classical

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_actual_centralizer_complete_model_and_principal_block
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisH : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (basisN : FiniteIrreducibleCharacterBasis (involutionCentralizer n S e))
    (principalN : basisN.index)
    (hprincipalN : (basisN.representation principalN).character = 1) :
    let H := centralizerOddCoreQuotient n S e
    let π := centralizerOddCoreMap n S e
    let A := centralizerFullCenterImage n hn S e
    let Q : Subgroup H := fourKlein.comap (alpha.toMonoidHom.comp
      (centralizerFullQuotientMap n hn S e))
    let st : involutionCentralizer n S e := wreathModelHom (centralizerSylow n hn S e)
      (centralizerCoordinates n hn S e) (Original.a (2 ^ n))
    let x := centralInvolution n S e
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let u := cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let iF := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let B₀ := coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN
    let deg : basisN.index → ℂ := fun χ => (basisN.representation χ).character 1
    n = 2 ∧ A = Subgroup.center H ∧ IsCyclic A ∧ Nat.card A = 4 ∧ Nat.card H = 96 ∧
      Q.Normal ∧ Nat.card Q = 16 ∧ Subgroup.centralizer (Q : Set H) ≤ Q ∧
      (∃ Φ : W ≃* H, Φ (u ^ 2) = π st ∧
        Φ (iF (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3))) = π x) ∧
      coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH = Finset.univ ∧
      (∀ χ, χ ∈ B₀ ↔
        centralizerOddCore n S e ≤ MonoidHom.ker (basisN.representation χ).representation) ∧
      (∀ χ, χ ∈ B₀ ↔ ∃ θ : basisH.index,
        (basisN.representation χ).character = (basisH.representation θ).character ∘ π) ∧
      (∀ θ : basisH.index, ∃ χ ∈ B₀,
        (basisN.representation χ).character = (basisH.representation θ).character ∘ π) ∧
      (∀ (Φ : W ≃* H) (basisW : FiniteIrreducibleCharacterBasis W),
        (∀ χ, χ ∈ B₀ ↔ ∃ η : basisW.index, (basisN.representation χ).character =
          (basisW.representation η).character ∘ Φ.symm ∘ π) ∧
        ∀ η : basisW.index, ∃ χ ∈ B₀, (basisN.representation χ).character =
          (basisW.representation η).character ∘ Φ.symm ∘ π) ∧
      B₀.card = 16 ∧ (B₀.filter fun χ => deg χ = 1).card = 4 ∧
      (B₀.filter fun χ => deg χ = 2).card = 6 ∧ (B₀.filter fun χ => deg χ = 3).card = 4 ∧
      (B₀.filter fun χ => deg χ = 4).card = 2 := by
  intro H π A Q st x W u iF B₀ deg
  have hres := FourPointResidual.four_point_full_center_quotient_actual_sl2_three_residual
    hnonab n hn S e alpha
  have hQnormal : Q.Normal := fourPointQ_normal n hn S e alpha
  have hQcard : Nat.card Q = 16 := fourPointQ_card n hn S e alpha hres.centralizer_card
  have hQcent : Subgroup.centralizer (Q : Set H) ≤ Q := fourPointQ_centralizer_le n hn S e alpha
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 4) hQcard
  have hone : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH =
      Finset.univ :=
    (selfcentralizing_unique_block 2 Q hQp hQcent ideal basisH).1 principalH hprincipalH
  have hR : ¬ 2 ∣ Nat.card (centralizerOddCore n S e) :=
    (CFSG.ComponentClassification.OddCore.odd_card (involutionCentralizer n S e)).not_two_dvd_nat
  obtain ⟨hker, hiff, hsurj, -⟩ :=
    @normal_prime_complement_unique_quotient_principal_block _ _ _ basisN ideal _ 2 _ _
      principalN hprincipalN (centralizerOddCore n S e) _ _ hR
      (inferInstanceAs (Fintype (centralizerOddCoreQuotient n S e))) basisH principalH hone
  have hiff' : ∀ χ, χ ∈ B₀ ↔ ∃ θ : basisH.index,
      (basisN.representation χ).character = (basisH.representation θ).character ∘ π := hiff
  have hsurj' : ∀ θ : basisH.index, ∃ χ ∈ B₀,
      (basisN.representation χ).character = (basisH.representation θ).character ∘ π := hsurj
  have htrans : ∀ (Φ : W ≃* H) (basisW : FiniteIrreducibleCharacterBasis W),
      (∀ χ, χ ∈ B₀ ↔ ∃ η : basisW.index, (basisN.representation χ).character =
        (basisW.representation η).character ∘ Φ.symm ∘ π) ∧
      ∀ η : basisW.index, ∃ χ ∈ B₀, (basisN.representation χ).character =
        (basisW.representation η).character ∘ Φ.symm ∘ π := by
    intro Φ basisW
    have hWH := exists_label_comp_surjective basisW basisH Φ.symm.toMonoidHom Φ.symm.surjective
    have hHW := exists_label_comp_surjective basisH basisW Φ.toMonoidHom Φ.surjective
    refine ⟨fun χ => ⟨fun hχ => ?_, fun ⟨η, hη⟩ => ?_⟩, fun η => ?_⟩
    · obtain ⟨θ, hθ⟩ := (hiff' χ).mp hχ
      obtain ⟨η, hη⟩ := hHW θ
      refine ⟨η, ?_⟩
      rw [hθ, hη]
      funext g
      simp
    · obtain ⟨θ, hθ⟩ := hWH η
      refine (hiff' χ).mpr ⟨θ, ?_⟩
      rw [hη, hθ]
      rfl
    · obtain ⟨θ, hθ⟩ := hWH η
      obtain ⟨χ, hχ, hχθ⟩ := hsurj' θ
      refine ⟨χ, hχ, ?_⟩
      rw [hχθ, hθ]
      rfl
  obtain ⟨Φ, hΦu, hΦx⟩ := exists_four_point_model_equiv hnonab n hn S e alpha
  obtain ⟨basisW⟩ := finiteIrreducibleCharacterBasis_exists (G := W)
  obtain ⟨hto, hfrom⟩ := htrans Φ basisW
  have hL : Function.Injective fun η : W → ℂ => η ∘ Φ.symm ∘ π :=
    (Φ.symm.surjective.comp (centralizerOddCoreMap_surjective n S e)).injective_comp_right
  have hBI : (fun χ => (basisN.representation χ).character) '' (B₀ : Set basisN.index) =
      (fun η : W → ℂ => η ∘ Φ.symm ∘ π) '' CFSG.BlocksIrr W := by
    ext ψ
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      obtain ⟨η, hη⟩ := (hto χ).mp hχ
      exact ⟨_, CFSG.BlockBasics.basis_character_mem_irr basisW η, hη.symm⟩
    · rintro ⟨η', hη', rfl⟩
      obtain ⟨η, rfl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basisW hη'
      obtain ⟨χ, hχ, hχη⟩ := hfrom η
      exact ⟨χ, hχ, hχη⟩
  have hval : ∀ η : W → ℂ, (fun η : W → ℂ => η ∘ Φ.symm ∘ π) η 1 = η 1 := by
    intro η
    simp only [Function.comp_apply, map_one]
  have hdeg := card_filter_eq_ncard_sep B₀ (fun χ => (basisN.representation χ).character)
    basisN.distinct _ hL _ hBI 1 1 hval
  obtain ⟨h16, h1, h2, h3, h4⟩ := fourPointModel_irr_ncard
  refine ⟨hres.parameter, hres.full_center, hres.center_cyclic, hres.center_card,
    hres.centralizer_card, hQnormal, hQcard, hQcent, ⟨Φ, hΦu, hΦx⟩, hone, hker, hiff', hsurj',
    htrans, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_eq_ncard_of_image B₀ (fun χ => (basisN.representation χ).character)
      basisN.distinct _ hL _ hBI, h16]
  · exact (hdeg 1).trans h1
  · exact (hdeg 2).trans h2
  · exact (hdeg 3).trans h3
  · exact (hdeg 4).trans h4

end CFSG.Wreathed.FourPointCompleteModel

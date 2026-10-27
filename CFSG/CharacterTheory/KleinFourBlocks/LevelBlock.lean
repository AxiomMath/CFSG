module

public import CFSG.CharacterTheory.KleinFourBlocks.OrbitTrace
public import CFSG.CharacterTheory.Semidihedral.Principal.KleinFourSylowBrauerFiber
public import CFSG.CharacterTheory.Wreathed.FullDefectCanonicalBridge

public section

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers
  CFSG.Wreathed CFSG.Wreathed.BlockOrbits CFSG.BlockBasics
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.KleinFourFiber
  CFSG.Semidihedral.Principal.ControlledDefect

open scoped Classical

namespace CFSG.KleinFourBlocks

variable {H : Type} [Group H] [Fintype H]

omit [Fintype H] in
theorem subgroupOf_map_normalCentralizerConj (P : Subgroup H) [P.Normal] (h : H) :
    (P.subgroupOf (Subgroup.centralizer (P : Set H))).map
        (normalCentralizerConj P h).toMonoidHom =
      P.subgroupOf (Subgroup.centralizer (P : Set H)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : H) ∈ P := hy
    show ((normalCentralizerConj P h y : Subgroup.centralizer (P : Set H)) : H) ∈ P
    rw [normalCentralizerConj_apply]
    exact Subgroup.Normal.conj_mem inferInstance _ hy' h
  · intro hx
    have hx' : (x : H) ∈ P := hx
    refine ⟨normalCentralizerConj P h⁻¹ x, ?_, ?_⟩
    · show ((normalCentralizerConj P h⁻¹ x : Subgroup.centralizer (P : Set H)) : H) ∈ P
      rw [normalCentralizerConj_inv_apply]
      have := Subgroup.Normal.conj_mem (inferInstance : P.Normal) _ hx' h⁻¹
      simpa using this
    · exact normalCentralizerConj_apply_inv h x

theorem defect_of_conj_block (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (P : Subgroup H) [P.Normal]
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    {β₀ c : localBasis.index}
    (hdef : coefficientBlockDefect localBasis ideal 2 β₀
      (P.subgroupOf (Subgroup.centralizer (P : Set H))))
    (h : H) (θ' : localBasis.index)
    (hθ' : LabelTransport localBasis localBasis (normalCentralizerConj P h) β₀ θ')
    (hc : sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ' c) :
    coefficientBlockDefect localBasis ideal 2 c
      (P.subgroupOf (Subgroup.centralizer (P : Set H))) := by
  have hres : ∀ z, centralCharacterResidueHom localBasis ideal θ'
      (centralCoefficientTransport _ (normalCentralizerConj P h) z) =
        centralCharacterResidueHom localBasis ideal β₀ z := fun z =>
    centralCharacterResidueHom_labelTransport localBasis localBasis ideal
      (normalCentralizerConj P h) hθ' z
  have h1 := coefficientBlockDefect_map_equiv localBasis localBasis ideal 2
    (normalCentralizerConj P h) hres hdef
  rw [subgroupOf_map_normalCentralizerConj] at h1
  exact (coefficientBlockDefect_iff_of_same_block localBasis ideal 2 hc _).mp h1

theorem stabilizer_shared_of_basis (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (P : Subgroup H) [P.Normal]
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (β₀ : localBasis.index)
    (hstab : ∀ (h : H) (θ' : localBasis.index),
      LabelTransport localBasis localBasis (normalCentralizerConj P h) β₀ θ' →
      sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β₀ θ' →
      h ∈ Subgroup.centralizer (P : Set H)) :
    ∀ q : H, ∀ ψ ∈ BlocksBlockOf ideal (Subgroup.centralizer (P : Set H))
        (localBasis.representation β₀).character,
      (fun d => ψ (normalCentralizerConj P q d)) ∈ BlocksBlockOf ideal
        (Subgroup.centralizer (P : Set H)) (localBasis.representation β₀).character →
      q ∈ Subgroup.centralizer (P : Set H) := by
  intro q ψ hψ hψq
  obtain ⟨ℓ, hℓ⟩ := exists_label_of_mem_irr localBasis hψ.1
  obtain ⟨ℓ', hℓ'⟩ := exists_label_of_mem_irr localBasis hψq.1
  have hsame_ℓ : sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β₀ ℓ :=
    (sameCoefficientBlock_iff localBasis ideal β₀ ℓ).mpr (by rw [hℓ]; exact hψ)
  have hsame_ℓ' : sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β₀ ℓ' :=
    (sameCoefficientBlock_iff localBasis ideal β₀ ℓ').mpr (by rw [hℓ']; exact hψq)
  obtain ⟨θ', hθ'⟩ := labelTransport_exists localBasis localBasis (normalCentralizerConj P q) β₀
  have hℓ'ℓ : LabelTransport localBasis localBasis (normalCentralizerConj P q) ℓ' ℓ := by
    intro x
    rw [hℓ, hℓ']
  have h1 := (sameCoefficientBlock_labelTransport_iff localBasis localBasis ideal
    (normalCentralizerConj P q) hθ' hℓ'ℓ).mp hsame_ℓ'
  have h2 : sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β₀ θ' := by
    rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq] at hsame_ℓ h1 ⊢
    exact hsame_ℓ.trans h1.symm
  exact hstab q θ' hθ' h2

omit [Fintype H] in
theorem labelTransport_symm' {X Y : Type*} [Group X] [Fintype X] [Group Y] [Fintype Y]
    {bX : FiniteIrreducibleCharacterBasis X} {bY : FiniteIrreducibleCharacterBasis Y}
    {f : X ≃* Y} {n : bX.index} {n' : bY.index} (h : LabelTransport bX bY f n n') :
    LabelTransport bY bX f.symm n' n := by
  intro y
  rw [← h (f.symm y), MulEquiv.apply_symm_apply]

theorem no_defect_group_outside_centralizer
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (P : Subgroup H) [P.Normal]
    (hP : IsPGroup 2 P) (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (β₀ : localBasis.index)
    (hstab : ∀ (h : H) (θ' : localBasis.index),
      LabelTransport localBasis localBasis (normalCentralizerConj P h) β₀ θ' →
      sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β₀ θ' →
      h ∈ Subgroup.centralizer (P : Set H))
    (A : basis.index)
    (hA : brauerNormalizerCharacterResidueHom ideal 2 P hP (Subgroup.centralizer (P : Set H))
      le_rfl (Subgroup.centralizer_le_normalizer _) localBasis β₀ =
        centralCharacterResidueHom basis ideal A)
    {X : Subgroup H} (hX : coefficientBlockDefect basis ideal 2 A X)
    (hXD : ¬ X ≤ Subgroup.centralizer (P : Set H)) : False := by
  have hXp : IsPGroup 2 X := coefficientBlockDefect_isPGroup basis ideal hX
  obtain ⟨lb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ↥(Subgroup.centralizer (X : Set H)))
  obtain ⟨γ, hγ⟩ := brauerNormalizer_local_block_exists_of_subconjugate basis ideal 2 X hXp
    (Subgroup.centralizer (X : Set H)) le_rfl (Subgroup.centralizer_le_normalizer _) lb hX
    (CFSG.TwoRankLowerBound.Helpers.subgroupSubconjugate_refl X)
  have hcorrX := FullDefectCanonical.brauerCorr_of_residue_eq basis ideal 2 X hXp
    (Subgroup.centralizer (X : Set H)) le_rfl (Subgroup.centralizer_le_normalizer _) lb γ A hγ
  have hcorrP := FullDefectCanonical.brauerCorr_of_residue_eq basis ideal 2 P hP
    (Subgroup.centralizer (P : Set H)) le_rfl (Subgroup.centralizer_le_normalizer _) localBasis
    β₀ A hA
  exact no_brauer_preimage_of_not_le_centralizer ideal
    ⟨_, basis_character_mem_irr localBasis β₀, rfl⟩ ⟨_, basis_character_mem_irr basis A, rfl⟩
    hcorrP (stabilizer_shared_of_basis ideal P localBasis β₀ hstab) hXp hXD
    ⟨_, basis_character_mem_irr lb γ, rfl⟩ hcorrX

theorem defect_group_eq_of_le_centralizer
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (P : Subgroup H) [P.Normal]
    (hP : IsPGroup 2 P) (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (β₀ : localBasis.index)
    (hdef : coefficientBlockDefect localBasis ideal 2 β₀
      (P.subgroupOf (Subgroup.centralizer (P : Set H))))
    (A : basis.index)
    (hA : brauerNormalizerCharacterResidueHom ideal 2 P hP (Subgroup.centralizer (P : Set H))
      le_rfl (Subgroup.centralizer_le_normalizer _) localBasis β₀ =
        centralCharacterResidueHom basis ideal A)
    {X : Subgroup H} (hX : coefficientBlockDefect basis ideal 2 A X)
    (hXD : X ≤ Subgroup.centralizer (P : Set H)) : X = P := by
  have hXp : IsPGroup 2 X := coefficientBlockDefect_isPGroup basis ideal hX
  have hPX : P ≤ X := normal_p_le_coefficientBlockDefect basis ideal 2 P hP hX
  have hCX : Subgroup.centralizer (X : Set H) ≤ Subgroup.centralizer (P : Set H) :=
    Subgroup.centralizer_le hPX
  have hPD : P ≤ Subgroup.centralizer (P : Set H) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hPab b hb a ha
  obtain ⟨lb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ↥(Subgroup.centralizer (X : Set H)))
  obtain ⟨γG, hγG⟩ := brauerNormalizer_local_block_exists_of_subconjugate basis ideal 2 X hXp
    (Subgroup.centralizer (X : Set H)) le_rfl (Subgroup.centralizer_le_normalizer _) lb hX
    (CFSG.TwoRankLowerBound.Helpers.subgroupSubconjugate_refl X)
  obtain ⟨wb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ↥(Subgroup.centralizer ((X.subgroupOf (Subgroup.centralizer (P : Set H)) :
      Subgroup (Subgroup.centralizer (P : Set H))) : Set (Subgroup.centralizer (P : Set H)))))
  obtain ⟨γ, hγ⟩ := labelTransport_exists lb wb (centralizerSubgroupOfEquiv hXD hCX).symm γG
  have hγ' := labelTransport_symm' hγ
  have hXDp : IsPGroup 2 (X.subgroupOf (Subgroup.centralizer (P : Set H))) := hXp.comap_subtype
  obtain ⟨c, hc⟩ := brauerNormalizer_block_image_exists localBasis ideal 2
    (X.subgroupOf (Subgroup.centralizer (P : Set H))) hXDp
    (Subgroup.centralizer ((X.subgroupOf (Subgroup.centralizer (P : Set H)) :
      Subgroup (Subgroup.centralizer (P : Set H))) : Set (Subgroup.centralizer (P : Set H))))
    le_rfl (Subgroup.centralizer_le_normalizer _) wb γ
  have hcomp := brauer_composite ideal 2 P X (Subgroup.centralizer (P : Set H)) hP hXp hPX le_rfl
    (Subgroup.centralizer_le_normalizer _) hXD hCX localBasis wb lb
    (by simpa using hγ') hc
  have hcA : brauerNormalizerCharacterResidueHom ideal 2 P hP (Subgroup.centralizer (P : Set H))
      le_rfl (Subgroup.centralizer_le_normalizer _) localBasis c =
        centralCharacterResidueHom basis ideal A := hcomp.trans hγG
  obtain ⟨-, -, hfib⟩ := normal_p_centralizer_brauer_fibers_are_block_orbits basis ideal 2 P hP
    localBasis
  obtain ⟨h, θ', hθ', hsame⟩ := (hfib β₀ c).mp (hA.trans hcA.symm)
  have hdefc := defect_of_conj_block ideal P localBasis hdef h θ' hθ' hsame
  have hsub := brauerNormalizer_subconjugate_of_local_block_exists localBasis ideal 2
    (X.subgroupOf (Subgroup.centralizer (P : Set H))) hXDp
    (Subgroup.centralizer ((X.subgroupOf (Subgroup.centralizer (P : Set H)) :
      Subgroup (Subgroup.centralizer (P : Set H))) : Set (Subgroup.centralizer (P : Set H))))
    le_rfl (Subgroup.centralizer_le_normalizer _) wb hdefc ⟨γ, hc⟩
  have hcard := CFSG.TwoRankLowerBound.Helpers.subgroupSubconjugate_card_le hsub
  have hcardX : Nat.card (X.subgroupOf (Subgroup.centralizer (P : Set H))) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXD).toEquiv
  have hcardP : Nat.card (P.subgroupOf (Subgroup.centralizer (P : Set H))) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPD).toEquiv
  rw [hcardX, hcardP] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hPX hcard).symm

theorem coefficientBlockDefect_of_trivial_stabilizer
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (P : Subgroup H) [P.Normal]
    (hP : IsPGroup 2 P) (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (β₀ : localBasis.index)
    (hdef : coefficientBlockDefect localBasis ideal 2 β₀
      (P.subgroupOf (Subgroup.centralizer (P : Set H))))
    (hstab : ∀ (h : H) (θ' : localBasis.index),
      LabelTransport localBasis localBasis (normalCentralizerConj P h) β₀ θ' →
      sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β₀ θ' →
      h ∈ Subgroup.centralizer (P : Set H))
    (A : basis.index)
    (hA : brauerNormalizerCharacterResidueHom ideal 2 P hP (Subgroup.centralizer (P : Set H))
      le_rfl (Subgroup.centralizer_le_normalizer _) localBasis β₀ =
        centralCharacterResidueHom basis ideal A) :
    coefficientBlockDefect basis ideal 2 A P := by
  obtain ⟨X, hX⟩ := coefficientBlockDefect_exists basis ideal 2 A
  by_cases hXD : X ≤ Subgroup.centralizer (P : Set H)
  · have hXP := defect_group_eq_of_le_centralizer basis ideal P hP hPab localBasis β₀ hdef A hA hX
      hXD
    rwa [hXP] at hX
  · exact (no_defect_group_outside_centralizer basis ideal P hP localBasis β₀ hstab A hA hX
      hXD).elim

theorem exists_level_block
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (P : Subgroup H) [P.Normal]
    (hP : IsPGroup 2 P) (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (β₀ : localBasis.index)
    (hdef : coefficientBlockDefect localBasis ideal 2 β₀
      (P.subgroupOf (Subgroup.centralizer (P : Set H))))
    (hstab : ∀ (h : H) (θ' : localBasis.index),
      LabelTransport localBasis localBasis (normalCentralizerConj P h) β₀ θ' →
      sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β₀ θ' →
      h ∈ Subgroup.centralizer (P : Set H)) :
    ∃ A : basis.index, coefficientBlockDefect basis ideal 2 A P ∧
      brauerNormalizerCharacterResidueHom ideal 2 P hP (Subgroup.centralizer (P : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis β₀ =
          centralCharacterResidueHom basis ideal A ∧
      ∀ n : localBasis.index,
        brauerNormalizerCharacterResidueHom ideal 2 P hP (Subgroup.centralizer (P : Set H))
            le_rfl (Subgroup.centralizer_le_normalizer _) localBasis n =
          centralCharacterResidueHom basis ideal A ↔
        ∃ (h : H) (θ' : localBasis.index),
          LabelTransport localBasis localBasis (normalCentralizerConj P h) β₀ θ' ∧
          sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ' n := by
  obtain ⟨himage, -, hfib⟩ := normal_p_centralizer_brauer_fibers_are_block_orbits basis ideal 2 P
    hP localBasis
  obtain ⟨A, hA⟩ := himage β₀
  refine ⟨A, coefficientBlockDefect_of_trivial_stabilizer basis ideal P hP hPab localBasis β₀ hdef
    hstab A hA, hA, fun n => ?_⟩
  rw [← hA, eq_comm]
  exact hfib β₀ n

end CFSG.KleinFourBlocks

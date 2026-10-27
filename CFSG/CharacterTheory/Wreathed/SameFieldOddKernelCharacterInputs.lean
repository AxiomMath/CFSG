module

public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelLocalModel
public import CFSG.CharacterTheory.Wreathed.ReciprocalDegreeExclusion
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityMultiplicities
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

open CFSG.TwoRankLowerBound.Helpers CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Fintype G]

theorem same_field_layer_character_inputs
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : (p ^ f % 4 = 1 ∧ StatedClassicalModel L .PSL 3 p f) ∨
      (p ^ f % 4 = 3 ∧ StatedClassicalModel L .PSU 3 p f)) :
    letI : Fintype L := Fintype.ofFinite L
    ∃ (Q : ℕ) (ideal : Ideal ComplexAlgebraicIntegers)
      (basisG : FiniteIrreducibleCharacterBasis G) (basisL : FiniteIrreducibleCharacterBasis L)
      (principalG : basisG.index) (principalL : basisL.index),
      (Q : ℤ) = (p ^ f : ℕ) ^ 2 + modFourSign (p ^ f) * (p ^ f) + 1 ∧
      1 < Q ∧ Q < (p ^ f) ^ 3 ∧ Q < (p ^ f) * Q ∧
      ideal.IsMaximal ∧ CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 ∧
      (basisG.representation principalG).character = 1 ∧
      (basisL.representation principalL).character = 1 ∧
      let P := layerSylow S K hSK O L hindex
      let eP := layerCoordinates S e K hSK O hO L hindex
      (¬ Nonempty (centralizerFullQuotient n hn P eP ≃* Equiv.Perm (Fin 4))) ∧
      StatedClassicalModel (centralizerSimpleLayer n hn P eP) .PSL 2 p f := by
  let : Fintype L := Fintype.ofFinite L
  let q := p ^ f
  have hqZ : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hpoly : 0 ≤ (q : ℤ) ^ 2 + modFourSign q * q + 1 := by
    rcases modFourSign_cases q with h | h <;> rw [h] <;> nlinarith
  let Q := ((q : ℤ) ^ 2 + modFourSign q * q + 1).toNat
  have hQ : (Q : ℤ) = (q : ℤ) ^ 2 + modFourSign q * q + 1 :=
    Int.toNat_of_nonneg hpoly
  obtain ⟨hQone, hQA, hQD⟩ :=
    SquareRootSmallCharacterRigidity.square_root_degree_bounds hq (modFourSign_cases q) hQ
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  obtain ⟨basisG⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨basisL⟩ := finiteIrreducibleCharacterBasis_exists (G := L)
  obtain ⟨principalG, hprincipalG⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisG
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  obtain ⟨principalL, hprincipalL⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisL
    (principalFiniteComplexRepresentation L) (principalFiniteComplexRepresentation_isIrreducible L)
  rw [principalFiniteComplexRepresentation_character] at hprincipalG hprincipalL
  have hlocal := same_field_layer_local_data n hn S e K hSK O hO L hindex
    p f hp hpodd hf hq hmodel
  exact ⟨Q, ideal, basisG, basisL, principalG, principalL, hQ, hQone, hQA, hQD,
    hmax, hchar, hprincipalG, hprincipalL, hlocal.1, hlocal.2.2.2.2.2.1⟩

end CFSG.Wreathed.SameFieldOddKernel

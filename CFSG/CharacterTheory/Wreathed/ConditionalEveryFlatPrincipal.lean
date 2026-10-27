module

public import CFSG.CharacterTheory.Wreathed.FlatWreathedBlock
public import CFSG.CharacterTheory.Wreathed.LinearLocalTwistMoment

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatEvery

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.FullDefectLabels
  CFSG.Wreathed.LinearLocalTwistMoment

theorem character_eq_one_of_finrank_one {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (ρ : FiniteComplexRepresentation G)
    (h1 : Module.finrank ℂ ρ.vector = 1) : ρ.character = 1 := by
  have hcomm : ∀ g h : G, ρ.representation g * ρ.representation h =
      ρ.representation h * ρ.representation g := by
    intro g h
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
      (ρ.representation g)
    obtain ⟨d, hd, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
      (ρ.representation h)
    rw [hc, hd]
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      mul_comm c d]
  have htop : ρ.representation.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.representation.ker with hbot | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      apply (MonoidHom.ker_eq_bot_iff _).mp hbot
      rw [map_mul, map_mul, hcomm]
    · exact htop
  have hone := MonoidHom.ker_eq_top_iff.mp htop
  funext g
  rw [FiniteComplexRepresentation.character, Representation.character, hone,
    MonoidHom.one_apply, LinearMap.trace_one, h1, Pi.one_apply, Nat.cast_one]

theorem principal_flat {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∃ (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θ : eb.index)
      (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
      (θhat : nb.index), (eb.representation θ).character = 1 ∧
      InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat ∧
      brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
          (Subgroup.normalizer ((S : Subgroup G) : Set G))
          (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat =
        centralCharacterResidueHom basis ideal (principalCharacterLabel basis) ∧
      FlatWreathedBlock basis ideal S e (principalCharacterLabel basis) := by
  obtain ⟨eb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))
  obtain ⟨nb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.normalizer ((S : Subgroup G) : Set G))
  have hlabels := full_defect_block_canonical_sylow_centralizer_labels basis ideal n hn S e nb eb
    (principalCharacterLabel basis) (principalCharacterLabel_character basis)
  obtain ⟨θhat, hθhat, -⟩ := hlabels.1 (principalCharacterLabel eb)
  have hchar := principalCharacterLabel_character eb
  have hB := hlabels.2.2.2.2.2.2.2.2 (principalCharacterLabel eb) θhat hchar hθhat
  refine ⟨eb, principalCharacterLabel eb, nb, θhat, hchar, hθhat, hB, ?_⟩
  refine FlatWreathedBlock.of_family basis ideal hn S e eb (principalCharacterLabel eb) nb θhat
    hθhat hB (fun _ => 1) (fun c z y _ _ => by rw [hchar]; rfl) (ψ := fun _ => 1) ?_
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl,
    fun _ => ?_⟩
  simp

end CFSG.Wreathed.FlatEvery

module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ProjectivePairCharacters

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem faithful_unit_exponent_card_le {actor : Type u} {field : Type v}
    [Group actor] [Field field] (character : actor →* fieldˣ)
    (hinjective : Function.Injective character) (exponent : ℕ) (hpositive : 0 < exponent)
    (hpower : ∀ member : actor, member ^ exponent = 1) : Nat.card actor ≤ exponent := by
  let polynomial : Polynomial field := Polynomial.X ^ exponent - Polynomial.C 1
  have hfinite : (polynomial.rootSet field).Finite := polynomial.rootSet_finite field
  let : Finite (polynomial.rootSet field) := hfinite.to_subtype
  have hroot : ∀ member : actor, (character member : field) ∈ polynomial.rootSet field := by
    intro member
    apply Polynomial.mem_rootSet.mpr
    constructor
    · exact Polynomial.X_pow_sub_C_ne_zero hpositive 1
    · have hunitPower : character member ^ exponent = 1 := by
        rw [← map_pow, hpower, map_one]
      have hfieldPower : (character member : field) ^ exponent = 1 :=
        congrArg (fun unit : fieldˣ => (unit : field)) hunitPower
      simp only [polynomial, map_sub, Polynomial.aeval_X_pow,
        map_one, hfieldPower, sub_self]
  let injection : actor → polynomial.rootSet field := fun member => ⟨character member, hroot member⟩
  have hinjection : Function.Injective injection := by
    intro first second heq
    apply hinjective
    apply Units.ext
    exact congrArg Subtype.val heq
  calc
    Nat.card actor ≤ Nat.card (polynomial.rootSet field) :=
      Nat.card_le_card_of_injective injection hinjection
    _ = (polynomial.rootSet field).ncard := Nat.card_coe_set_eq _
    _ ≤ polynomial.natDegree := polynomial.ncard_rootSet_le field
    _ = exponent := Polynomial.natDegree_X_pow_sub_C

theorem projective_pointwise_pair_exponent_card_le {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [FiniteDimensional field space]
    (hdimension : Module.finrank field space = 2)
    (subgroup : Subgroup (space ≃ₗ[field] space))
    (projectiveSubgroup : Subgroup ((linearProjectiveAction field space).comp subgroup.subtype).range)
    (first second : Projectivization field space) (hne : first ≠ second)
    (hfixed : ∀ member : projectiveSubgroup,
      (member : Equiv.Perm (Projectivization field space)) first = first ∧
        (member : Equiv.Perm (Projectivization field space)) second = second)
    (exponent : ℕ) (hpositive : 0 < exponent)
    (hpower : ∀ member : projectiveSubgroup, member ^ exponent = 1) :
    Nat.card projectiveSubgroup ≤ exponent := by
  obtain ⟨character, hinjective⟩ := projective_plane_pointwise_pair_embeds_units
    hdimension subgroup projectiveSubgroup first second hne hfixed
  exact faithful_unit_exponent_card_le character hinjective exponent hpositive hpower

end CFSG.RankThreeEvenClassification.Helpers

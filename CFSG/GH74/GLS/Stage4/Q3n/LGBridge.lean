module

public import CFSG.GH74.GLS.Stage4.Q3n.Leaves
public import CFSG.CharacterTheory.BlockBasics.Bridge
public import CFSG.CharacterTheory.Semidihedral.Principal.DefectDegreeDivisibility

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open CFSG CFSG.TwoRankLowerBound.Helpers

theorem lg33_1 : LG33_1 := by
  intro p hp m hm hpm G _ _ D χ hχ hD
  have : Fintype G := Fintype.ofFinite G
  have : Fact p.Prime := ⟨hp⟩
  have : m.IsMaximal := hm
  have : CharP (ComplexAlgebraicIntegers ⧸ m) p :=
    (CFSG.BlockBasics.residue_prime_existence p hp).2 m hm hpm
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨l, rfl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis hχ
  have hD' : coefficientBlockDefect basis m p l D :=
    (CFSG.BlockBasics.coefficientBlockDefect_iff basis m p l D).mpr hD
  obtain ⟨-, ⟨d, hd⟩, key⟩ :=
    CFSG.Semidihedral.Principal.block_class_defect_witness_character_degree_dvd basis m p l D hD'
  obtain ⟨-, hdvd⟩ := key d hd
  refine ⟨Module.finrank ℂ (basis.representation l).vector, Representation.char_one _, ?_⟩
  have hG : (Nat.card G).factorization p = padicValNat p (Nat.card G) :=
    Nat.factorization_def _ hp
  have hDd : (Nat.card D).factorization p = d := by
    rw [hd, Nat.Prime.factorization_pow hp]
    simp
  rw [hG, hDd]
  exact hdvd l (coefficientBlock_self_mem basis _ l)

end CFSG.GH74.GLS.Stage4.Q3n

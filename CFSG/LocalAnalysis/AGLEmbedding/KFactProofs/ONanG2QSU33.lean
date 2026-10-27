module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus
public import CFSG.Adapters.RankThreeOutcomesReverse

public section

namespace CFSG.AGLEmbedding.KFactProofs.G2Q

open CFSG.UnitaryThreeRecognition.Model CFSG.AGLEmbedding.UnitaryModel
  CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.RankThreeEven (projSU statedClassicalModel_of_projSU)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

theorem exists_unitaryCoord_pair {K : Type} [Field K] (J : HermitianForm 3 K)
    (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution J.conj) :
    ∃ z w : Coord J, z * w ≠ w * z := by
  obtain ⟨c, hc⟩ := hσ.exists_ne
  obtain ⟨b, hb⟩ := hσ.trace_surj (-1) (by rw [map_neg, map_one])
  obtain ⟨b', hb'⟩ := hσ.trace_surj (-(c * J.conj c)) (by
    rw [map_neg, map_mul, hσ.invol, mul_comm])
  refine ⟨⟨(1, b), ?_⟩, ⟨(c, b'), ?_⟩, ?_⟩
  · show b + J.conj b + 1 * J.conj 1 = 0
    rw [hb, map_one]; ring
  · show b' + J.conj b' + c * J.conj c = 0
    rw [hb']; ring
  · intro h
    have h2 : b + b' - 1 * J.conj c = b' + b - c * J.conj 1 :=
      congrArg (fun z : Coord J => ((z : K × K)).2) h
    rw [map_one] at h2
    apply hc
    linear_combination -h2

theorem unitaryCoord_pow_three {K : Type} [Field K] [CharP K 3] (J : HermitianForm 3 K)
    (z : Coord J) : z ^ 3 = 1 := by
  apply Subtype.ext
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  rw [pow_succ, pow_two, coord_mul_val, coord_mul_val, coord_one_val]
  refine Prod.ext ?_ ?_
  · show z.1.1 + z.1.1 + z.1.1 = 0
    linear_combination z.1.1 * h3
  · show z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 + z.1.2 -
      (z.1.1 + z.1.1) * J.conj z.1.1 = 0
    linear_combination (z.1.2 - z.1.1 * J.conj z.1.1) * h3

theorem exists_pair_projSU33 {X : Type} [Group X] (e : X ≃* projSU 3 3 1) :
    ∃ x y : X, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : StatedLieAdmissible .PSU 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨-, -, -, K, _, _, J, hJ, hK, hfix, ⟨e0⟩⟩ :=
    exists_equiv_psu (statedClassicalModel_of_projSU hadm e)
  have : CharP K 3 := charP_of_card Nat.prime_three hK
  obtain ⟨z, w, hzw⟩ := exists_unitaryCoord_pair J (isUnitaryInvolution_conj J hK hfix)
  refine ⟨e0.symm (root J hJ z), e0.symm (root J hJ w), ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ← map_pow, unitaryCoord_pow_three, map_one, map_one]
  · rw [← map_pow, ← map_pow, unitaryCoord_pow_three, map_one, map_one]
  · intro h
    apply hzw
    apply root_injective J hJ
    rw [map_mul, map_mul]
    exact e0.symm.injective (by rw [map_mul, map_mul]; exact h)
  · have hR : IsPGroup 3 ((rootGroup J hJ).map e0.symm.toMonoidHom) :=
      (isPGroup_rootGroup J hJ hK hfix).map _
    refine hR.to_le ((Subgroup.closure_le _).2 ?_)
    rintro _ (rfl | rfl)
    · exact ⟨_, root_mem_rootGroup J hJ z, rfl⟩
    · exact ⟨_, root_mem_rootGroup J hJ w, rfl⟩

end CFSG.AGLEmbedding.KFactProofs.G2Q

module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4Maximal
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldCaseB
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldCorner

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne

section Planes


@[expose] def D4SubfieldMaximalEight : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 8 → ∀ σ : K ≃+* K, orderOf σ = 3 →
    ∀ M : Subgroup ↥(adjointGroup Tag.D4 K), subfieldGroup Tag.D4 σ ≤ M →
      M = subfieldGroup Tag.D4 σ ∨ M = ⊤

theorem d4ThreeFieldPlanes_of_eight (h8 : D4SubfieldMaximalEight) : D4ThreeFieldPlanes := by
  unfold D4ThreeFieldPlanes
  intro K _ _ _hK3 E hE hEc hex
  obtain ⟨α, hαE, g, a, σ, ε, -, hσ3, ⟨hε0, hσ1⟩, hα⟩ := hex
  classical
  haveI := hE
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  subst hε0
  rw [d4Graph_zero, mul_one] at hα
  obtain ⟨e, T, he0, hef, hT, hT3, hσT⟩ :=
    exists_frobenius_of_cube hℓ n.pos K hK σ hσ3 hσ1
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, one_pow])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← hef]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ringChar K ^ (e * 3) := Nat.pow_le_pow_left hℓ.two_le _
  have hordT : orderOf T = 3 := orderOf_eq_prime hT3 hT1
  have hq0 : Nat.card (fixSubfield T) = ringChar K ^ e := card_fixSubfield_eq_pow hK hef T hT3 hT1
  have hK' : Nat.card K = (ringChar K ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
  have hmax : ∀ M : Subgroup ↥(adjointGroup Tag.D4 K), subfieldGroup Tag.D4 T ≤ M →
      M = subfieldGroup Tag.D4 T ∨ M = ⊤ := by
    by_cases h2 : Nat.card (fixSubfield T) = 2
    · have hK8 : Nat.card K = 8 := by rw [hK', ← hq0, h2]; norm_num
      exact h8 K hK8 T hordT
    · exact subfieldMaximal_D4_of_card_ne_two T Nat.prime_three (by norm_num) hordT h2
  by_cases hA : ∃ ι ∈ E, ι ≠ 1 ∧ ∃ (g' : adjointGroup Tag.D4 K)
      (b : Fin Tag.D4.rank → Kˣ), ι = MulAut.conj g' * rootDiagAut Tag.D4 K b
  · obtain ⟨ι, hιE, hι1, g', b, hι⟩ := hA
    by_cases h2 : Nat.card (fixSubfield T) = 2
    · have hK8 : Nat.card K = 8 := by rw [hK', ← hq0, h2]; norm_num
      exact d4_caseA_eight hK hK4 he0 hef T σ hT hT3 hT1 hσT hmax (by rw [hK8]; norm_num) hαE
        hιE g a hα g' b hι hι1
    · have hbig : 2 < Nat.card (fixSubfield T) := by
        have : 2 ≤ Nat.card (fixSubfield T) := Finite.one_lt_card
        omega
      exact d4_caseA_big hK hK4 he0 hef T σ hT hT3 hT1 hσT hmax hbig hαE hιE g a hα g' b hι hι1
  · push Not at hA
    exact d4_caseB hK hK4 he0 hef T σ hT hT3 hT1 hσT hmax hEc hαE g a hα
      (fun ι hι g' b h => by_contra fun h1 => hA ι hι h1 g' b h)

end Planes

end CFSG.LieType.SeitzGeneration.ExcWideThree

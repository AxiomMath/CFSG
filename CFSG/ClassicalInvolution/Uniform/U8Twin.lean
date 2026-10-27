module

public import CFSG.ClassicalInvolution.Uniform.U8Basic
public import CFSG.ClassicalInvolution.Asc77.AscR10E24
public import CFSG.ClassicalInvolution.Asc77.AscR10E20
public import CFSG.ClassicalInvolution.Uniform.U5Three2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.ModelFacts (Gen3 fundamentalSubgroups_subset_longest)
open scoped MatrixGroups commutatorElement


section Twin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}

theorem ih8_twin_stable3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {A B : Subgroup (modelUniv t k 3 e Fact.out).K} (hA : A ∈ M.cls) (hB : B ∈ M.cls)
    (hAB : A ≠ B) {z : G} (hzA : IsUniqueInvolution (A.map M.ψ) z)
    (hzB : IsUniqueInvolution (B.map M.ψ) z) {S : Subgroup (modelUniv t k 3 e Fact.out).K}
    (hS : S ∈ M.cls) (hSA : Commutes S A) : S = B ∨ Commutes S B := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hex := exactMembers_of_ih8Model M hΩ hG2 hD4
  have hnpsl : ¬ (t = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    exact M.admissible.2.2.2.2 (by norm_num)
  have hgA := ih8Model_gen3 M hG2 hD4 hA
  have hgB := ih8Model_gen3 M hG2 hD4 hB
  have hk3 := ih8Model_ker_pow_three M hD4
  have := M.finite_K hp2
  have hne' : A.map M.ψ ≠ B.map M.ψ := fun h =>
    hAB (eq_of_map_eq_of_gen3 M.ψ M.ker_le_center hk3 hgA hgB h)
  obtain ⟨-, x, hx, x', hx', hψx, hψx', hx'1, hcen⟩ := ih8_twin_data3 hΩ hex M.ker_le_center hk3
    hgA (M.map_mem hA) (M.map_mem hB) hne' hzA hzB
  obtain ⟨eB⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hB
  obtain ⟨eS⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hS
  have hodd := M.natCard_galoisField_odd hp2
  have hinj := M.injOn_fund hnpsl (M.cls_sub hB)
  have hx'2 : x' * x' = 1 := by
    apply hinj (x' * x') (B.mul_mem hx' hx')
    rw [map_mul, hψx', hzB.sq]
  have hord : orderOf x' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx'2) hx'1
  have hcS : ∀ s ∈ S, x' * s = s * x' := by
    intro s hs
    have h1 : x * s = s * x := (hSA s hs x hx).symm
    have hcc : ∀ y, y * (x' * x⁻¹) = (x' * x⁻¹) * y := Subgroup.mem_center_iff.mp hcen
    have hx'c : x' = (x' * x⁻¹) * x := by group
    calc x' * s = (x' * x⁻¹) * x * s := by rw [← hx'c]
      _ = (x' * x⁻¹) * (x * s) := mul_assoc _ _ _
      _ = (x' * x⁻¹) * (s * x) := by rw [h1]
      _ = ((x' * x⁻¹) * s) * x := (mul_assoc _ _ _).symm
      _ = (s * (x' * x⁻¹)) * x := by rw [← hcc s]
      _ = s * ((x' * x⁻¹) * x) := mul_assoc _ _ _
      _ = s * x' := by rw [← hx'c]
  have hdich := CFSG.ClassicalInvolution.Asc77.T3CII.stdDich3_all
    CFSG.ClassicalInvolution.ModelFacts.stdDich3Orth CFSG.ClassicalInvolution.ModelFacts.stdDich3Exc
    t k M.isFundTag M.admissible hG2 hD4
  have hBl := fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hB)
  have hSl := fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hS)
  have ho2 : orderOf (sl2Inv eS) = 2 := orderOf_sl2Inv hodd eS
  have hcomm : x' * sl2Inv eS = sl2Inv eS * x' := hcS _ (sl2Inv_mem eS)
  have hF3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  rcases hdich B hBl S hSl x' (sl2Inv eS) hx' (sl2Inv_mem eS) hord ho2 hcomm with
    h | h | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact Or.inl h.symm
  · exact Or.inr fun s hs b hb => (h b hb s hs).symm
  · exact absurd (linearPair_eq_one_of_centralizes3 hF3 hW hx' hcS) hx'1
  · exact absurd (unitaryPair_eq_one_of_centralizes3
      (CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl) (by norm_num) hW hx' hcS) hx'1

theorem modelTwinClass_two3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hne : Ω.Nonempty) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {A B : Subgroup (modelUniv t k 3 e Fact.out).K} (hA : A ∈ M.cls) (hB : B ∈ M.cls)
    (hAB : A ≠ B) {z : G} (hzA : IsUniqueInvolution (A.map M.ψ) z)
    (hzB : IsUniqueInvolution (B.map M.ψ) z) : ModelTwinClass 3 t k e 2 := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hex := exactMembers_of_ih8Model M hΩ hG2 hD4
  have hgA := ih8Model_gen3 M hG2 hD4 hA
  have hgB := ih8Model_gen3 M hG2 hD4 hB
  have hk3 := ih8Model_ker_pow_three M hD4
  have := M.finite_K hp2
  have hne' : A.map M.ψ ≠ B.map M.ψ := fun h =>
    hAB (eq_of_map_eq_of_gen3 M.ψ M.ker_le_center hk3 hgA hgB h)
  obtain ⟨hcomm, -⟩ := ih8_twin_data3 hΩ hex M.ker_le_center hk3 hgA (M.map_mem hA)
    (M.map_mem hB) hne' hzA hzB
  refine ⟨![A, B], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact M.cls_sub hA
    · exact M.cls_sub hB
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hAB
    · exact absurd hij.symm hAB
    · rfl
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcomm
    · exact fun x hx y hy => (hcomm y hy x hx).symm
    · exact absurd rfl hij
  · intro i j S hS
    have hS' := M.fund_subset_cls hne hG2 hD4 hS
    fin_cases i <;> fin_cases j
    · exact Iff.rfl
    · constructor
      · rintro (rfl | h)
        · exact Or.inr hcomm
        · exact ih8_twin_stable3 M hΩ hG2 hD4 hA hB hAB hzA hzB hS' h
      · rintro (rfl | h)
        · exact Or.inr fun x hx y hy => (hcomm y hy x hx).symm
        · exact ih8_twin_stable3 M hΩ hG2 hD4 hB hA hAB.symm hzB hzA hS' h
    · constructor
      · rintro (rfl | h)
        · exact Or.inr fun x hx y hy => (hcomm y hy x hx).symm
        · exact ih8_twin_stable3 M hΩ hG2 hD4 hB hA hAB.symm hzB hzA hS' h
      · rintro (rfl | h)
        · exact Or.inr hcomm
        · exact ih8_twin_stable3 M hΩ hG2 hD4 hA hB hAB hzA hzB hS' h
    · exact Iff.rfl

end Twin

end CFSG.ClassicalInvolution.Uniform

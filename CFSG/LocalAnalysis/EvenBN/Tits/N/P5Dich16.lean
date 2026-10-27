module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Dich16Comp
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Dich16Tr
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5ExclR

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalAnalysis.EvenBN.Tits.N

section


theorem layer_dichotomy16 (hTop : TopStatement) {X : Type} [Group X] [Finite X] (S : Sylow 2 X)
    {A : Subgroup X} (hAS : A ≤ S) (hab : IsElemAbelian 2 A) (hA : Nat.card A = 16)
    (hcl : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    {x : X} (hxN : x ∈ normalizer (A : Set X)) (hx5 : x ^ 5 = 1)
    (hfpf : ∀ a ∈ A, x * a * x⁻¹ = a → a = 1) :
    goldschmidtLayer (Mbar A) = ⊥ ∨
      ∃ B₀ : Subgroup (MulAut ↥A), B₀ ≤ imgIn A (normalizer (A : Set X)) ∧
        (∀ h ∈ imgIn A (normalizer (A : Set X)), ∀ b ∈ B₀, h * b * h⁻¹ ∈ B₀) ∧
        Odd (Nat.card B₀) ∧ ∀ a b : ↥A, a ≠ 1 → b ≠ 1 → ∃ g ∈ B₀, g a = b := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hU1, hU2, hU3⟩ := unpack hTop S hAS hab.1 hcl
  have hφ5 : rhoHom A x ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
  have hcardAbar : Nat.card (Abar A) = 16 := by rw [card_Abar hab]; exact hA
  have hfpfbar := rhoHom_fpf hab hxN hfpf
  have hRA : pCore 2 (Mbar A) ≤ Abar A := R_le_Abar hTop S hAS hab.1 hcl
  have hφA : ∀ a ∈ Abar A, rhoHom A x a ∈ Abar A := fun a ha => rhoHom_mem_Abar A hxN ha
  by_cases hR1 : pCore 2 (Mbar A) = ⊥
  · by_cases hlay : goldschmidtLayer (Mbar A) = ⊥
    · exact Or.inl hlay
    · right
      obtain ⟨Sb, hSb⟩ := exists_sylow_Mbar S A
      have hAb : Abar A = pCore 2 (Mbar A) ⊔ closure {t | t ∈ (Sb : Subgroup (Mbar A)) ⊓
          goldschmidtLayer (Mbar A) ∧ t ^ 2 = 1} := by
        rw [hSb]
        exact hU2
      obtain ⟨htrans, hodd⟩ := comp_odd_transitive16 (oddCore_Mbar A) hR1 hU1 hU3 Sb hAb
        (isElemAbelian_Abar hab) hcardAbar hφ5 hφA hfpfbar hlay
      exact exists_B₀ hab htrans hodd
  · left
    have hinv : ∀ r ∈ pCore 2 (Mbar A), rhoHom A x r ∈ pCore 2 (Mbar A) :=
      fun r hr => rhoHom_mem_pCore A x hr
    rcases eq_bot_or_eq_of_invariant16 hcardAbar hφ5 hfpfbar hRA hinv with h | h
    · exact absurd h hR1
    · exact layer_eq_bot_of_pCore_eq_Abar hab h

end

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

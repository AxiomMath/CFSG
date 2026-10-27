module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Final
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalKType
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Lemma35

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

@[expose] def Solomon75Lemma34K : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X), SolCEx X → HypA X →
    IsMaxAhatDeg X n → IsSec5Pair X n z Z → Lemma34K X n Z

theorem exists_sec5Data (hGold : CFSG.Goldschmidt.CoreStatement) (h34 : Solomon75Lemma34K)
    (X : Type) [Group X] [Finite X] (hX : SolCEx X) (hA : HypA X) :
    ∃ (n : ℕ) (z : X) (Z : Subgroup X) (S : Sylow 2 ↥(normalizer (Z : Set X))),
      Sec5Data X n z Z S := by
  obtain ⟨n, hn⟩ := hX.toSolMinCEx.exists_isMaxAhatDeg
  obtain ⟨t, L, ht, hL, hcov⟩ := hn.2.1
  obtain ⟨Z, hp⟩ := exists_isSec5Pair ht hL hcov
  have ha := lemma33b_of_isSec5Pair hA hn hp
  have hb := lemma33a_of_isSec5Pair hA hn hp
  have hc := h34 X n t Z hX hA hn hp
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥(normalizer (Z : Set X))))
  exact ⟨n, t, Z, S, hX, hA, hn, hp, hX.lemma52_of_n hGold hn.1 hp ha hb hc S⟩

theorem sol_caseA_false_of_data (hF : Solomon75Frac53) (h55 : Solomon75Lemma55)
    (h56 : Solomon75Cor56) (h57 : Solomon75Lemma57) (h58 : Solomon75Lemma58)
    (hAB : ∀ m : ℕ, 8 ≤ m → m ≤ 11 → AlternatingBalanceData m)
    (h44McL : Solomon44McL) (h44Ly : Solomon44Ly) (h44NT : Solomon44NineTen)
    (hdata : ∀ (X : Type) [Group X] [Finite X], SolCEx X → HypA X →
      ∃ (n : ℕ) (z : X) (Z : Subgroup X) (S : Sylow 2 ↥(normalizer (Z : Set X))),
        Sec5Data X n z Z S) :
    ∀ (X : Type) [Group X] [Finite X], SolCEx X → HypA X → False := by
  intro X _ _ hX hA
  obtain ⟨n, z, Z, S, h⟩ := hdata X hX hA
  obtain ⟨hcov, hn8, hn11⟩ := thm310 hF h55 h56 h57 h58 hAB h
  have := hX.simple
  have hz := h.orderOf_z
  have hnonab := hX.nonabelian
  have hn : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by omega
  rcases hn with rfl | rfl | rfl | rfl
  · exact hX.false_of_equiv hz (Or.inl (h44McL X hnonab z hz hcov))
  · exact h44NT X hnonab z hz 9 (Or.inl rfl) hcov
  · exact h44NT X hnonab z hz 10 (Or.inr rfl) hcov
  · exact hX.false_of_equiv hz (Or.inr (h44Ly X hnonab z hz hcov))

theorem sol_caseA_false (hGold : CFSG.Goldschmidt.CoreStatement) (h34 : Solomon75Lemma34K)
    (hF : Solomon75Frac53) (h55 : Solomon75Lemma55) (h56 : Solomon75Cor56)
    (h57 : Solomon75Lemma57) (h58 : Solomon75Lemma58)
    (hAB : ∀ m : ℕ, 8 ≤ m → m ≤ 11 → AlternatingBalanceData m)
    (h44McL : Solomon44McL) (h44Ly : Solomon44Ly) (h44NT : Solomon44NineTen) :
    ∀ (X : Type) [Group X] [Finite X], SolCEx X → HypA X → False :=
  sol_caseA_false_of_data hF h55 h56 h57 h58 hAB h44McL h44Ly h44NT
    (fun X _ _ hX hA => exists_sec5Data hGold h34 X hX hA)

end CFSG.OddStandard.Solomon75

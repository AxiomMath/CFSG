module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.KDSp6Lie
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.KDSp6Alt
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.KDSp6Spor
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.KDSp6Odd
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Id

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.ComponentClassification.Sol76T13 CFSG.ComponentClassification.CatLeaf

@[expose] def KDSp6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Catalog K → SolomonA12HypK K → LieModel K .PSp 3 2 1

variable {K : Type} [Group K] [Finite K]

theorem false_of_cyclic (hP : P12Facts) (hK : SolomonA12HypK K) {q : ℕ} (hq : q.Prime)
    (e : K ≃* Multiplicative (ZMod q)) : False := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
  have h1 : Nat.card (S : Subgroup K) = 2 ^ 9 := (elemFactsIn_sylow hP hK S).1
  have h2 : Nat.card K = q := by
    haveI := Fact.mk hq
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have h3 : 2 ^ 9 ∣ q := by
    rw [← h1, ← h2]
    exact Subgroup.card_subgroup_dvd_card _
  rcases (Nat.dvd_prime hq).1 h3 with h | h
  · omega
  · rw [← h] at hq
    norm_num at hq

theorem kdSp6_of_inputs (hO : LieOrderFormulasInput)
    (hcard : ∀ s, Nat.card (Carrier s) = CFSG.AGLEmbedding.sporOrd s) (hP : P12Facts)
    (hOdd : OddLieA12Sylow) (hSpor : SporadicNoE64) : KDSp6 := by
  intro K _ _ hcat hK
  rcases Hq4.catalog_cases_lieModel hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hL⟩ | hS
  · exact (false_of_cyclic hP hK hq e).elim
  · exact (false_of_alternating hP hK hn e).elim
  · by_cases h2 : p = 2
    · subst h2
      exact lieModel_psp_of_even hO hP hK hL
    · exact (false_of_odd_lie hOdd hK ⟨t, n, p, f, hL.admissible.1, h2, hL.admissible, hL⟩).elim
  · exact (false_of_sporadic hcard hSpor hP hK hS).elim

end CFSG.EvenSporadicStandard.M12Std.SolomonK

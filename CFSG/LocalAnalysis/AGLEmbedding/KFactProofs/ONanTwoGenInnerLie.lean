module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerSpor
import CFSG.RankThree.PartOne.TCB.Final
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OddExcAll
import CFSG.RankThree.PartOne.S11d.OutExceptional
import CFSG.RankThree.PartOne.S11d.OutEsix
import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
import CFSG.RankThree.PartOne.AUTSL.OddOutRee

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OutStructure CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms

section FamilyCerts


theorem pGoodOut_of_lieModel {T : Type} [Group T] [Finite T] {t : StatedLieTag}
    {n ℓ f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hadm : StatedLieAdmissible t n ℓ f)
    (hmodel : LieModel T t n ℓ f)
    (hL : StatedClassicalModel T .PSL n ℓ f → ¬ p ∣ Nat.gcd n (ℓ ^ f - 1))
    (hU : StatedClassicalModel T .PSU n ℓ f → ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (hD4 : D4PGood) : PGoodOut p T := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hp3' : 3 < p := by omega
  have nice : OutPNice p T → PGoodOut p T := pGoodOut_of_outPNice
  rcases hmodel with ⟨ht, hcl⟩ | ⟨-, ht, hch⟩ | ⟨-, ht, hree⟩ | ⟨-, -, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hn2 : n = 2
      · subst hn2
        by_cases hℓ : ℓ = 2
        · subst hℓ
          exact nice (outPNice_PSL_two hp hcl)
        · exact nice (outPNice_PSL_two_odd hp hp3' hℓ hcl)
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact nice (outPNice_PSL_ge_three_odd hp hp2 hn3 hcl (hL hcl))
    · exact nice (outPNice_PSU_odd hp hcl (hU hcl))
    · by_cases hn2 : n = 2
      · subst hn2
        by_cases hℓ : ℓ = 2
        · subst hℓ
          exact nice (outPNice_PSp_two hp hcl)
        · exact nice (AUTSL.SpTwo.outPNice_PSp_two_odd hp hp2 hℓ hcl)
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact nice (outPNice_PSp_ge_three_odd hp hp2 hn3 hcl)
    · exact nice (outPNice_POmegaOdd_gen hp hp5 hcl)
    · by_cases hn4 : n = 4
      · subst hn4
        exact hD4 T p ℓ f hp hp5 hcl
      · have hn5 : 5 ≤ n := by
          have := hcl.1.2.2
          omega
        exact nice (outPNice_POmegaPlus_gen_ge_five hp hp5 hn5 hcl)
    · exact nice (outPNice_POmegaMinus_gen hp hp5 hcl)
  · by_cases hℓ : ℓ = 2
    · subst hℓ
      simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact nice (outPNice_G2 hp hch)
      · exact nice (outPNice_F4 hp hch)
      · exact nice (outPNice_E6 hp hp3 hp2 hch)
      · exact nice (outPNice_E7 hp hch)
      · exact nice (outPNice_E8 hp hch)
      · exact nice (outPNice_twistedE6 hp hp3 hch)
      · exact nice (outPNice_trialityD4 hp hch)
    · exact nice (oddExceptionalOut_holds p T t ℓ f hp hp5 hadm.1 hℓ ht hch)
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have h3 : ℓ = 3 := hree.1.2.2.2.1
      subst h3
      exact nice (AUTSL.outPNice_twistedG2 hp hree)
    · have h2 : ℓ = 2 := hree.1.2.2.2.1
      subst h2
      exact nice (outPNice_twistedF4 hp hree)
    · exact pGoodOut_of_tits hp hp5 hree
  · have h2 : ℓ = 2 := hsz.1
    subst h2
    exact nice (outPNice_Suzuki hp hsz)

end FamilyCerts

section FullCerts


theorem pGoodOut_of_catalogGroup {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ {n ℓ f : ℕ}, StatedClassicalModel S .PSL n ℓ f → ¬ p ∣ Nat.gcd n (ℓ ^ f - 1))
    (hU : ∀ {n ℓ f : ℕ}, StatedClassicalModel S .PSU n ℓ f → ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (hD4 : D4PGood) : PGoodOut p S := by
  rcases TCB.tauCetiCatalogBridge S hnab hcat |> PlaneCases.catalog_cases with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (e.injective (by rw [map_mul, map_mul, mul_comm])) hab
  · exact pGoodOut_of_alternating hn hp hp5 e
  · exact pGoodOut_of_lieModel hp hp5 hadm hmodel hL hU hD4
  · exact pGoodOut_of_sporadic hnab ⟨e⟩ hp hp5

end FullCerts

end CFSG.AGLEmbedding.TwoGenInner

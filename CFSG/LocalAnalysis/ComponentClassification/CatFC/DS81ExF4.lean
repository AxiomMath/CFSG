module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Classes
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.RankThree.Chevalley CFSG.SeitzReduction
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
  CFSG.ComponentClassification.RankTwoExceptional.Exc

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem commute_rootDiagUnit_f4CollProd (L : List ℕ) (hL : ∀ p ∈ L, 24 ≤ p ∧ p ≤ 47)
    (c : Fin Tag.F4.rank → ℤ) (hc : ∀ p ∈ L, ∑ i, c i * orbitCertRoot .F4 p i = 0) (ε : Kˣ) :
    Commute (rootDiagUnit .F4 (fun i => ε ^ c i)) (f4CollProd K L) := by
  have := commute_rootDiagUnit_framePt (K := K) (τ := .F4) (L.map (orbitCertRoot .F4))
    (by simpa using fun p hp => (f4_isRoot_pos (hL p hp)).1) c (by simpa using hc) ε
  simpa [f4CollProd, f4x, List.map_map, Function.comp_def] using this

theorem f4_exists_order_eightynine_commute [Finite K] [CharP K 2] {ε : Kˣ} (hε : orderOf ε = 89) :
    ∀ y ∈ ([f4Rep K [47], f4Rep K [44], f4Rep K [47, 44], f4Rep K [41, 45]] :
      List (adjointGroup .F4 K)), ∃ z : adjointGroup .F4 K, orderOf z = 89 ∧ Commute z y := by
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have h2 : ringChar K = 2 := ringChar.eq K 2
  have key : ∀ (L : List ℕ) (c : Fin Tag.F4.rank → ℤ), (∀ p ∈ L, 24 ≤ p ∧ p ≤ 47) →
      (∀ p ∈ L, ∑ i, c i * orbitCertRoot .F4 p i = 0) → ¬ (89 : ℤ) ∣ c ⟨0, by decide⟩ →
      ∃ z : adjointGroup .F4 K, orderOf z = 89 ∧ Commute z (f4Rep K L) := by
    intro L c hL hc hc0
    refine ⟨⟨rootDiagUnit .F4 fun i => ε ^ c i,
      rootDiagUnit_mem_adjointGroup_of_charTwo (Or.inr (Or.inl rfl)) h2 _⟩, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact orderOf_rootDiagUnit_eq_prime hε c ⟨0, by decide⟩ hc0
    · exact Subtype.ext (commute_rootDiagUnit_f4CollProd L hL c hc ε).eq
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact key [47] ![2, -2, 0, 1] (by decide) (by decide) (by decide)
  · exact key [44] ![2, -2, 0, 1] (by decide) (by decide) (by decide)
  · exact key [47, 44] ![2, -2, 0, 1] (by decide) (by decide) (by decide)
  · exact key [41, 45] ![2, -1, 0, 0] (by decide) (by decide) (by decide)

theorem lie23To89At_F4 : Lie23To89At .F4 := by
  intro X _ _ n f hadm hM τ hτ h23
  have hn : n = 0 := hadm.2.2
  subst hn
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hM.chevalleyExceptionalModel (by decide)
  have hK2 : ringChar K = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hadm.2.1 hcard
  haveI : CharP K 2 := ringChar.of_eq hK2
  have h11 : 11 ∣ f := eleven_dvd_of_twentythree_dvd_card (by simp) hadm hM
    (dvd_trans h23 (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨ε, hε⟩ := exists_unit_orderOf_eightynine_of_card hcard h11
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  exact prime_dvd_card_centralizer_of_classesCover (e.trans (adjointQuotientEquiv .F4 K))
    classesCover_AS (f4_exists_order_eightynine_commute hε) hτ

end CFSG.ComponentClassification.CatFC.DS81.Ex

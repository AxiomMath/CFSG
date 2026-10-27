module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6Reps
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport
public import CFSG.LieType.Chevalley.E6EvenRootTorusAutFix

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.RankTwoExceptional.E6Sec8
  CFSG.ComponentClassification.RankTwoExceptional.Exc
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.Chevalley.E6EvenInvolution
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6EvenRootTorus

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem thetaTorusHom_eq_rootDiagUnit (ε : Kˣ) :
    thetaTorusHom K ε =
      rootDiagUnit TwistTag.E6.tag (fun i => ε ^ (Pi.single (e6Idx 1) (1 : ℤ) :
        Fin TwistTag.E6.tag.rank → ℤ) i) := by
  show rootDiagUnit TwistTag.E6.tag (Pi.mulSingle (e6Idx 1) ε) = _
  congr 1
  funext i
  by_cases h : i = e6Idx 1
  · subst h
    simp
  · simp [Pi.mulSingle_apply, Pi.single_apply, h]

theorem rootDiagUnit_theta_mem_adjointGroup (h2 : (2 : K) = 0) (ε : Kˣ) :
    rootDiagUnit .E6 (fun i => ε ^ (Pi.single (e6Idx 1) (1 : ℤ) : Fin Tag.E6.rank → ℤ) i) ∈
      adjointGroup .E6 K := by
  have h := thetaTorusHom_mem_adjointGroup h2 ε
  rw [thetaTorusHom_eq_rootDiagUnit] at h
  exact h

theorem e6_exists_order_eightynine_commute [Finite K] [CharP K 2] {ε : Kˣ}
    (hε : orderOf ε = 89) :
    ∀ y ∈ (e6Reps (K := K)), ∃ z : adjointGroup .E6 K, orderOf z = 89 ∧ Commute z y := by
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hmem := rootDiagUnit_theta_mem_adjointGroup h2 ε
  have h0 : ∀ β ∈ frame₁ ++ frame₂ ++ frame₃, β (e6Idx 1) = 0 := by decide
  have hroots : ∀ β ∈ frame₁ ++ frame₂ ++ frame₃, IsRoot .E6 β := by
    intro β hβ
    simp only [frame₁, frame₂, frame₃, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hβ
    rcases hβ with (rfl | rfl | rfl) | rfl | rfl | rfl <;> exact isRoot_single _ _
  have key : ∀ F : List (Fin Tag.E6.rank → ℤ), (∀ β ∈ F, β ∈ frame₁ ++ frame₂ ++ frame₃) →
      ∃ z : adjointGroup .E6 K, orderOf z = 89 ∧ Commute z (frameRep F) := by
    intro F hF
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact orderOf_rootDiagUnit_eq_prime hε _ (e6Idx 1) (by decide)
    · exact Subtype.ext (commute_rootDiagUnit_single_framePt (e6Idx 1) F
        (fun β hβ => hroots β (hF β hβ)) (fun β hβ => h0 β (hF β hβ)) ε).eq
  intro y hy
  simp only [e6Reps, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · exact key frame₁ (fun β hβ => List.mem_append_left _ (List.mem_append_left _ hβ))
  · exact key frame₂ (fun β hβ => List.mem_append_left _ (List.mem_append_right _ hβ))
  · exact key frame₃ (fun β hβ => List.mem_append_right _ hβ)

theorem lie23To89At_E6 : Lie23To89At .E6 := by
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
  exact prime_dvd_card_centralizer_of_classesCover (e.trans (adjointQuotientEquiv .E6 K))
    classesCover_e6Reps (e6_exists_order_eightynine_commute hε) hτ

end CFSG.ComponentClassification.CatFC.DS81.Ex

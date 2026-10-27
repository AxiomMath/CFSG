module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSLClasses
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSLFour
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma44

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (innerDiagonalAction)
open CFSG.ComponentClassification.CatalogueBLinearSemilinear (semilinearAction)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.CatalogueBGraphField (graphFieldAction)
open CFSG.ComponentClassification.SolMax.FiveCat.C5PSL

namespace C5PSL

theorem a5Shape_graph {n f : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ f) (A : GL (Fin n) K)
    (hord : orderOf (pureGraphAction n K A) = 2) :
    A5Shape n f (fixedSubgroup (pureGraphAction n K A)) := by
  intro L hL hA5 _ hu
  obtain ⟨t, m, e, hT, hadm', hm'⟩ := graph_psl_component_models Nat.prime_five
    (by norm_num : (5 : ℕ) ≠ 2) hK hn A hord hL
  obtain ⟨rfl, rfl, rfl⟩ := eq_psl_two_one_of_a5 (isClassicalTag_of_mem_graphTuples hT) hadm' hm'
    hA5
  rcases mem_graphTuples_psl_two_one hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact (a5_pureGraph_four (by simpa using hK) A hord hL hA5 hu).elim

theorem a5Shape_psl {J : Type} [Group J] {n f : ℕ} (hadm : StatedLieAdmissible .PSL n 5 f)
    (hm : Blueprint.LieModel J .PSL n 5 f) {α : MulAut J} (hα : orderOf α = 2) :
    A5Shape n f (fixedSubgroup α) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have key : ∀ γ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr e α = γ →
      (orderOf γ = 2 → A5Shape n f (fixedSubgroup γ)) → A5Shape n f (fixedSubgroup α) := by
    intro γ hγ h
    exact A5Shape.of_mulEquiv ((fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) (h (hγ ▸ hβ))
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e α = semilinearAction n K A σ → A5Shape n f (fixedSubgroup α) := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact key _ hAσ fun hord => a5Shape_inner hK hadm A hord
    · exact key _ hAσ fun _ => a5Shape_field hn hK hf A σ hσ (hAσ ▸ hβ2)
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := psl_two_normal_form (MulAut.congr e α)
    exact hsemi A σ hAσ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr e α))
    have hβ' : MulAut.congr e α = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
      exact hsemi A σ hβ'
    · rw [pow_one] at hβ'
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        exact key _ hβ' fun hord => a5Shape_graph hn3 hK A hord
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' fun hord => a5Shape_graphField hn3 hK hf A σ hσ hord

end C5PSL

private theorem eq_one_of_mem_center_of_zStar {P : Type} [Group P] [Finite P]
    (hZ : Open.fusionZStar P = pPrimeCore 2 P) {w : P} (hw : w ∈ center P) (hww : w * w = 1) :
    w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwZ : w ∈ Open.fusionZStar P := by
    rw [GrSLit.GrS4.fusionZStar_eq_comap_pPrimeCore, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw y]
  rw [hZ] at hwZ
  have hcop := LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore (p := 2) hwZ
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hww)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm h2)

theorem fivePump_char5_PSL : FivePumpCharFiveClause .PSL := by
  intro S _ _ hs hna ⟨n, f, hm⟩ σ P hP hZ eP huniq
  have hadm : StatedLieAdmissible .PSL n 5 f := hm.admissible
  have hσ1 : σ ≠ 1 := hP.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => hP.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hq : IsQuasisimple (P.subgroupOf (fixedSubgroup σ)) :=
    fixedTwoComponentsQuasisimple_lin (by norm_num : (5 : ℕ) ≠ 2) (Or.inl rfl) hadm hm σ hσσ hσ1
      _ hP.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := hP.fusionZStar_equiv_of_quasisimple hq
  have hA5 : Nonempty (↥(P.subgroupOf (fixedSubgroup σ)) ⧸
      center ↥(P.subgroupOf (fixedSubgroup σ)) ≃*
      alternatingGroup (Fin 5)) := ⟨eZ.symm.trans eP.some⟩
  have hz : ∀ z ∈ P.subgroupOf (fixedSubgroup σ),
      (∀ y ∈ P.subgroupOf (fixedSubgroup σ), z * y = y * z) → z * z = 1 → z = 1 := by
    intro z hzL hzc hzz
    have hzP : (z : S) ∈ P := mem_subgroupOf.mp hzL
    have hwc : (⟨(z : S), hzP⟩ : ↥P) ∈ center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := hzc ⟨(y : S), hP.2.1 y.2⟩ (mem_subgroupOf.mpr y.2)
      exact Subtype.ext (congrArg Subtype.val h1).symm
    have hzz' : (z : S) * (z : S) = 1 := congrArg Subtype.val hzz
    have hww : (⟨(z : S), hzP⟩ : ↥P) * ⟨(z : S), hzP⟩ = 1 := Subtype.ext hzz'
    have h1 := eq_one_of_mem_center_of_zStar hZ hwc hww
    have h2 : (z : S) = 1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hu : ∀ L' : Subgroup ↥(fixedSubgroup σ), IsComponent L' → L' = P.subgroupOf
      (fixedSubgroup σ) := by
    intro L' hL'
    have hLL : (L'.map (fixedSubgroup σ).subtype).subgroupOf (fixedSubgroup σ) = L' :=
      comap_map_eq_self_of_injective (subtype_injective _) L'
    have hP' : ProperFixedComponent σ (L'.map (fixedSubgroup σ).subtype) := by
      refine ⟨hP.1, map_subtype_le L', ?_, fun htop => hσ1 ?_⟩
      · rw [hLL]
        exact isPComponent_two_of_isComponent hL'
      · have hF : fixedSubgroup σ = ⊤ := top_le_iff.mp (htop ▸ map_subtype_le L')
        ext x
        have hx : x ∈ fixedSubgroup σ := hF ▸ mem_top x
        exact hx
    rw [← hLL, huniq _ hP']
  rcases C5PSL.a5Shape_psl hadm hm hσ2 _ hcomp hA5 hz hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))

end CFSG.ComponentClassification.SolMax.FiveCat

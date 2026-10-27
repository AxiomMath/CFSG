module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSUFour
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRow
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma44

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

namespace C5PSU

theorem not_mem_linUInnerTuples {n f : ℕ}
    (h : ((.PSL : StatedLieTag), 2, 1) ∈ linUInnerTuples n f) : False := by
  rcases h with ⟨k, -, -, h⟩ | ⟨-, h⟩
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · have h2 := (Prod.mk.inj (Prod.mk.inj h).2).2
    omega

theorem isClassicalTag_of_mem_linUInnerTuples {t : StatedLieTag} {m e n f : ℕ}
    (h : (t, m, e) ∈ linUInnerTuples n f) : IsClassicalTag t := by
  rcases h with ⟨k, -, -, h⟩ | ⟨-, h⟩
  · rw [(Prod.mk.inj h).1]; exact Or.inr (Or.inl rfl)
  · rw [(Prod.mk.inj h).1]; exact Or.inl rfl

theorem a5Shape_inner {n f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 5 f K)
    (hadm : StatedLieAdmissible .PSU n 5 f) (A : primeFormUnitary h (idGram K n))
    (hord : orderOf (primeFormConjHom h (idGram K n) A) = 2) :
    C5PSL.A5Shape n f (fixedSubgroup (primeFormConjHom h (idGram K n) A)) := by
  intro L hL hA5 hz hu
  rcases inner_psu_component_cases h (by norm_num) hadm A hord hL with
    ⟨z, hzL, hzc, hzz, hz1⟩ | ⟨t, m, e, hT, hadm', hm'⟩
  · exact absurd (hz z hzL hzc hzz) hz1
  · obtain ⟨rfl, rfl, rfl⟩ := C5PSL.eq_psl_two_one_of_a5
      (isClassicalTag_of_mem_linUInnerTuples hT) hadm' hm' hA5
    exact (not_mem_linUInnerTuples hT).elim

theorem a5Shape_graph {n f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 5 f K)
    (hadm : StatedLieAdmissible .PSU n 5 f) (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x)
    (hord : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2) :
    C5PSL.A5Shape n f (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)) := by
  intro L hL hA5 _ hu
  obtain ⟨t, m, e, hT, hadm', hm'⟩ := graph_psu_component_models h (by norm_num : (5 : ℕ) ≠ 2)
    hadm A φ hφ hord hL
  obtain ⟨rfl, rfl, rfl⟩ := C5PSL.eq_psl_two_one_of_a5 (isClassicalTag_of_mem_graphTuples hT)
    hadm' hm' hA5
  rcases C5PSL.mem_graphTuples_psl_two_one hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact (a5_psuGraph_four h A φ hφ hord hL hA5 hu).elim

theorem a5Shape_psu {J : Type} [Group J] {n f : ℕ} (hadm : StatedLieAdmissible .PSU n 5 f)
    (hm : Blueprint.LieModel J .PSU n 5 f) {α : MulAut J} (hα : orderOf α = 2) :
    C5PSL.A5Shape n f (fixedSubgroup α) := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ 5 ^ f = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq (MulAut.congr ψ α)
  have hff : primeFormFieldFactor h hC hn hq (MulAut.congr ψ α) = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one (MulAut.congr ψ α)
    rw [hβ] at h1
    rw [h1, map_one]
  refine C5PSL.A5Shape.of_mulEquiv (fixedSubgroupCongrEquiv ψ α) ?_
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · have hAα : MulAut.congr ψ α = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    have hord : orderOf (primeFormConjHom h _ A) = 2 := hAα ▸ hβ
    exact C5PSL.A5Shape.of_mulEquiv (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAα))
      (a5Shape_inner h hadm A hord)
  · have hord : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 := hAφ ▸ hβ
    exact C5PSL.A5Shape.of_mulEquiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAφ.symm))
      (a5Shape_graph h hadm A φ hφ hord)

end C5PSU

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

theorem fivePump_char5_PSU : FivePumpCharFiveClause .PSU := by
  intro S _ _ hs hna ⟨n, f, hm⟩ σ P hP hZ eP huniq
  have hadm : StatedLieAdmissible .PSU n 5 f := hm.admissible
  have hσ1 : σ ≠ 1 := hP.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => hP.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hq : IsQuasisimple (P.subgroupOf (fixedSubgroup σ)) :=
    fixedTwoComponentsQuasisimple_lin (by norm_num : (5 : ℕ) ≠ 2) (Or.inr rfl) hadm hm σ hσσ hσ1
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
        exact CatLeafProof.isPComponent_two_of_isComponent hL'
      · have hF : fixedSubgroup σ = ⊤ := top_le_iff.mp (htop ▸ map_subtype_le L')
        ext x
        have hx : x ∈ fixedSubgroup σ := hF ▸ mem_top x
        exact hx
    rw [← hLL, huniq _ hP']
  rcases C5PSU.a5Shape_psu hadm hm hσ2 _ hcomp hA5 hz hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hadm.2.2.1 (by norm_num)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))

end CFSG.ComponentClassification.SolMax.FiveCat

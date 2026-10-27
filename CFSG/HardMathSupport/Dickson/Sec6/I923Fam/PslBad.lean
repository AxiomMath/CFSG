module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Cyclic
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Diag
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.RankTwoClassical

theorem not_dvd_psl_three_four (r m : ℕ) (hr : 10 ≤ r) (hpp : IsPrimePow r)
    (hm : m + r = r ^ 3) : ¬ m ∣ 2 * 20160 := by
  intro hdvd
  have hle : m ≤ 2 * 20160 := Nat.le_of_dvd (by norm_num) hdvd
  have hr35 : r ≤ 34 := by
    by_contra hcon
    have h35 : 35 ≤ r := by omega
    have h1 : 35 * 35 * r ≤ r * r * r := Nat.mul_le_mul (Nat.mul_le_mul h35 h35) le_rfl
    have h2 : r ^ 3 = r * r * r := by ring
    rw [h2] at hm
    generalize r * r * r = u at h1 hm
    omega
  have hm' : m = r ^ 3 - r := by omega
  subst hm'
  interval_cases r <;> first
    | (simp at hdvd; done)
    | (exfalso; revert hpp; decide +kernel)

theorem noL2Layer_psl_three_four (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hX : LieModel X .PSL 3 2 2) (ψ : MulAut X) : NoL2Layer ψ := by
  obtain ⟨hfin, hM, -⟩ := hO X .PSL 3 2 2 hX.admissible hX
  have hcard : Nat.card X = 20160 := by
    simp only [lieOrderDivisor, lieOrderNumerator] at hM
    have hprod : (∏ x ∈ Finset.Icc 2 3, ((2 ^ 2) ^ x - 1)) = 945 := by decide
    rw [hprod] at hM
    norm_num at hM
    omega
  haveI := hfin
  refine noL2Layer_of_card_dvd_pp ψ (N := 20160) ?_ fun r m hr hpp hm =>
    not_dvd_psl_three_four r m hr hpp hm
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card _

theorem y923_lieRestAt_pslBad (hO : LieOrderFormulasInput) (hGA : GriessAllModelsStatement) :
    Y923_PslBad := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  obtain ⟨rfl, hn3, hdvd⟩ := hF
  by_cases h322 : n = 3 ∧ p = 2 ∧ f = 2
  · obtain ⟨rfl, rfl, rfl⟩ := h322
    exact noL2_of_famOK hq (MulEquiv.refl _)
      (fun ψ _ _ => ⟨1, ψ, by simp, noL2Layer_psl_three_four hO hm ψ⟩) h3 hnot hJ hr
  · have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n p f :=
      (lieModel_classical_iff (by decide)).mp hm
    have hM := isCyclic_hopfMultiplier_psl hGA hC hn3 h322 hdvd
    obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
    let e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
    have hψ3 : (MulAut.congr e (centerDescend Y α)) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, h3, map_one, map_one]
    by_cases hD : MulAut.congr e (centerDescend Y α) ∈ linearAutGroup n K
    · exact absurd (mem_innAutDerived_of_diag_psl hq e hM h3 hD) hnot
    · obtain ⟨σ, hσ, H, hψH⟩ :=
        linear_order_three_field_descent hn3 (MulAut.congr e (centerDescend Y α)) hψ3 hD
      exact noL2_of_conj_descent e α rfl hψH
        (noL2Layer_fieldAut_psl_gen hO hn3 hσ hadm.1 hadm.2.1 hK) hJ hr

section


theorem y923_pslbad_holds (hGA : GriessAllModelsStatement) : Y923_PslBad :=
  y923_lieRestAt_pslBad CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hGA

end

end CFSG.HardMathSupport.Dickson.Sec6.I923

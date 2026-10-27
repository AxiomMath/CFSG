module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRBase
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.OuterCent
public import CFSG.Sporadic.HeldB.OuterFixedCore

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct

theorem heP_centralizer_not_isPGroup
    (s : heP) (hs : orderOf s = 2) :
    ¬ IsPGroup 2 ↥(centralizer ({s} : Set heP)) := by
  intro hP
  have hs' : orderOf (s : Equiv.Perm (Fin 8330)) = 2 := by rw [Subgroup.orderOf_coe]; exact hs
  have h' := hP.of_equiv (heCentralizerEquiv s)
  rcases involution_conj_cases s.2 hs' with ⟨c, hc, he⟩ | ⟨c, hc, he⟩
  · have h0 : ¬ IsPGroup 2 ↥(centralizerIn heP (heGenPerm 0)) :=
      not_isPGroup_of_three_dvd (by rw [card_heP_cent0]; norm_num)
    rw [he] at h'
    exact not_isPGroup_inf_centralizer_conj hc h0 h'
  · have h1 : ¬ IsPGroup 2 ↥(centralizerIn heP heT1P) :=
      not_isPGroup_of_three_dvd (by rw [card_heP_cent1]; norm_num)
    rw [he] at h'
    exact not_isPGroup_inf_centralizer_conj hc h1 h'

theorem twoNilpFor_He :
    TwoNilpFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .He := by
  intro Y _ _ hY _ _ a ha hP
  exfalso
  obtain ⟨e⟩ := hY
  set θ : Y ≃* heP := e.trans heEquivP
  have hβ : orderOf (MulAut.congr θ a) = 2 := (orderOf_congr θ a).trans ha
  have hP' := isPGroup_fixedPoints_congr θ a hP
  by_cases hinn : MulAut.congr θ a ∈ (MulAut.conj : heP →* MulAut heP).range
  · obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (Hin.conj_injective_of_center heP_center_eq_bot) t, ht, hβ]
    rw [← ht, ← Hin.centralizer_eq_fixedPoints_conj] at hP'
    exact heP_centralizer_not_isPGroup t ht2 (isPGroup_of_pPrimeCore_eq_bot
      (ctbhi_held_inner_involution_centralizers_odd_core.2 t ht2) hP')
  · obtain ⟨x, hx, hxP, hx2⟩ :=
      exists_heConjR_eq ctbh_full_automorphism_permutation_model.1 _ hβ hinn
    obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
    have hfix : fixedPoints (MulAut.congr θ a) = fixedSubgroup (heConjR x) := by
      rw [← hx]
      rfl
    let f : ↥(fixedPoints (MulAut.congr θ a)) ≃* ↥(heP ⊓ centralizer {heAutU}) :=
      (MulEquiv.subgroupCongr hfix).trans (fixedSubgroupEquivOfConj x hg heAutU hxg)
    have hC := Q81.isPGroup_quotient_of_surjective f.toMonoidHom f.surjective hP'
    rw [← heOuterC_eq] at hC
    exact not_isPGroup_of_perfect heOuterD_le_C heOuterD_perfect
      (by rw [card_heOuterD]; norm_num) hC

end CFSG.ComponentClassification.HarrisLit.L33.SR

module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharOmSub
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Conf
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharOmModel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharOmTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Cases

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X11Char

open CFSG Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.CatLeaf (lieSylowExponent)

attribute [local instance] finite_linearEquiv

theorem false_of_orthTuples_psl_two_nine {Y : Type} [Group Y] {d : ℕ} (h5 : 5 ≤ d) (h8 : d ≤ 8)
    {t : StatedLieTag} {n e : ℕ} (hT : (t, n, e) ∈ orthTuples d 1) (hm : LieModel Y t n 3 e)
    (hX : LieModel Y .PSL 2 3 2) : False := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h2 := (lieOrder_of_lieModel_classical (Or.inl rfl) hp2 (by norm_num) hX).2
  have key : ∀ {t' : StatedLieTag} {n' : ℕ}, IsClassicalTag t' → n' ≠ 0 →
      LieModel Y t' n' 3 1 → lieSylowExponent t' n' = 2 := by
    intro t' n' ht hn h
    have h1 := (lieOrder_of_lieModel_classical ht hp2 hn h).2
    rw [h1] at h2
    simpa [lieSylowExponent] using h2
  have ht := isClassicalTag_of_mem_orthTuples hT
  rcases hT with ⟨hd, -⟩ | ⟨hd, -⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨hd, ⟨r, hr⟩, h⟩ | ⟨hd, -, h | h⟩
  · omega
  · omega
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact absurd (key ht (by norm_num) hm) (by decide)
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact absurd (key ht (by norm_num) hm) (by decide)
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact absurd (key ht (by norm_num) hm) (by decide)
  · obtain rfl : d = 7 := by omega
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact absurd (key ht (by norm_num) hm) (by decide)
  · obtain rfl : d = 8 := by omega
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact absurd (key ht (by norm_num) hm) (by decide)
  · obtain rfl : d = 8 := by omega
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact absurd (key ht (by norm_num) hm) (by decide)

theorem false_of_conf_pomegaMinus_three {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (hconf : GSThmB.X11.Conf G N) (hM : LieModel ↥N .POmegaMinus 4 3 1) : False := by
  obtain ⟨hNn, hC, -, a, -, J, -, ha, -, -, hJN, hJC, hJp, hJm, -, hbound, -⟩ := hconf
  have : N.Normal := hNn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨k, _, _, β, γ, hirr, Θ, hk, hinv⟩ := exists_model_of_normal hC hp hp2 le_rfl hM
  have hk3 : Nat.card k = 3 := by rw [hk, pow_one]
  obtain ⟨Da⟩ := hinv a ha
  have hnd := (regular_coordinateQuadMinus 4 k β γ le_rfl hirr).1
  have hnp := not_isPlusType_coordinateQuadMinus 4 (by norm_num) hirr
  have hdim : finrank k (Fin (2 * 4) → k) = 8 := by simp
  have hodd : Odd (Nat.card k) := by rw [hk3]; decide
  have h2 : (2 : k) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hsq : IsSquare (Da.c : k)
  swap
  ·
    obtain ⟨T, _, _, ι, hT⟩ := caseB_data hp hp2 le_rfl hk hnd hdim hnp Da hsq
    obtain ⟨M, hM, hMJ, hMε⟩ := corr_down Da ι J hJC hJN hJp
    subst hMJ
    obtain ⟨hq, hLM⟩ := hT _ hMε
    obtain ⟨hqJ, ⟨eJ⟩⟩ := centerQuotient_equiv Da ι M hq
    have h3 := pow_eq_of_lieModel_psl_two hp hp2 hp hp2 (lieModel_center_of_pPrimeCore hqJ hJm)
      (LieType.CurtisTits.lieModel_of_mulEquiv eJ.symm hLM)
    norm_num at h3
  obtain ⟨β', hβ'⟩ := hsq
  have hβ0 : β' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hβ'
    exact Units.ne_zero _ hβ'
  obtain ⟨W, W', ι, hcompl, hnd₁, hnd₂, hι⟩ := caseA_data hp hp2 le_rfl hk hnd hdim Da
    (Units.mk0 β' hβ0) (by rw [Units.val_mk0, hβ', sq])
  obtain ⟨M, hM, hMJ, hMε⟩ := corr_down Da ι J hJC hJN hJp
  subst hMJ
  obtain ⟨U, U', ψ, hcU, hndU, hndU', hψ, L, hL, hML⟩ :=
    left_normal_form Da ι hcompl hnd₁ hnd₂ hι M hMε
  have hLc := isComponent_of_pComponent hodd hndU hL
  obtain ⟨hJq, ⟨eJ⟩⟩ := quotient_of_left Da ψ M L hLc.1 hML
  have hLZ : LieModel (L ⧸ center L) .PSL 2 3 2 :=
    LieType.CurtisTits.lieModel_of_mulEquiv eJ (lieModel_center_of_pPrimeCore hJq hJm)
  have hmis : LieModel (L ⧸ center L) .PSL 2 3 1 → False := fun h1 => by
    have h3 := pow_eq_of_lieModel_psl_two hp hp2 hp hp2 hLZ h1
    norm_num at h3
  have hsum : finrank k U + finrank k U' = 8 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcU, hdim]
  have hU3 : 3 ≤ finrank k U := by
    by_contra h
    exact CatalogueBOrthogonal.orthogonal_small_no_pComponent _ h2 hndU (by omega) 2 L hL
  have hU4 : finrank k U = 4 := by
    by_contra h4
    rcases (show finrank k U = 3 ∨ 5 ≤ finrank k U by omega) with h3 | h5
    · exact hmis (pComponent_three hp hp2 le_rfl hk hndU h3 hL)
    · obtain ⟨t, n, e', hT, -, hm'⟩ :=
        orthogonal_component_models hp hp2 le_rfl hk _ hndU hU3 hLc
      exact false_of_orthTuples_psl_two_nine h5 (by omega) hT hm' hLZ
  have hnpU : ¬ IsPlusType ((coordinateQuadMinus 4 k (by norm_num) β γ).comp U.subtype) := by
    rintro ⟨S, hS2, hS⟩
    exact hmis (pComponent_split_four hp hp2 le_rfl hk hndU hU4 ⟨S, by omega, hS⟩ hL)
  have hU'4 : finrank k U' = 4 := by omega
  have horth := polar_eq_zero_of_decomp ψ hψ h2
  have hplus := isPlusType_of_compl hnp hcU horth hndU hU4 hnpU hndU' hU'4
  have hcard := card_orthogonalGroup_plus_four hk3 hndU' hU'4 hplus
  have h32 := dvd_card_comap_orthogonalDerived (rightFactor Da.A ψ) hcard
    (index_orthogonalDerived k β γ h2 hirr)
  have : Nontrivial U := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  obtain ⟨R, hR, hRle⟩ := exists_twoSubgroup_of_left Da ψ hψ h2 (exists_ne 0) M L hML (n := 5)
    (by rw [show (2 : ℕ) ^ 5 = 32 by norm_num]; exact h32)
  have h8 := hbound R hRle (IsPGroup.of_card hR)
  rw [hR] at h8
  norm_num at h8

end CFSG.ComponentClassification.CatLeafProof.X11Char

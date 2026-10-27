module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharOmModel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharLin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Cases

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X11Char

open CFSG Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
open CFSG.ComponentClassification.CatLeafProof.X10Lin

attribute [local instance] finite_linearEquiv

theorem psp_mem_orthTuples {d e f : ℕ} (h : (StatedLieTag.PSp, 2, e) ∈ orthTuples d f) :
    d = 5 ∧ e = f := by
  rcases h with ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨hd, h⟩ | ⟨-, h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h | h⟩ <;>
    simp_all

theorem lieModel_center_psp4_three {L : Type} [Group L] [Finite L] (hq : IsQuasisimple L)
    (h : LieModel (L ⧸ pPrimeCore 2 L) .PSp 2 3 1) : LieModel (L ⧸ center L) .PSp 2 3 1 :=
  LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq
    (GSThmB.X10Rec.center_eq_pPrimeCore hq (isSimpleGroup_of_lieModel_psp4_three h))).symm h

theorem eq_one_of_kConf_pomegaMinus {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (hconf : GSThmB.X11.KConf G N) {f : ℕ} (hM : LieModel ↥N .POmegaMinus 4 3 f) : f = 1 := by
  obtain ⟨hNn, hC, -, b, Kc, hb, hKN, hKC, hKp, hKm⟩ := hconf
  have : N.Normal := hNn
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf1 : 1 ≤ f := (GH74.statedClassicalModel_of_lieModel (by norm_num) hM).1.2.1
  obtain ⟨k, _, _, β, γ, hirr, Θ, hk, hinv⟩ := exists_model_of_normal hC hp hp2 hf1 hM
  obtain ⟨Db⟩ := hinv b hb
  have hnd := (regular_coordinateQuadMinus 4 k β γ le_rfl hirr).1
  have hnp := not_isPlusType_coordinateQuadMinus 4 (by norm_num) hirr
  have hdim : finrank k (Fin (2 * 4) → k) = 8 := by simp
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 : (2 : k) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hsq : IsSquare (Db.c : k)
  ·
    obtain ⟨β', hβ'⟩ := hsq
    have hβ0 : β' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hβ'
      exact Units.ne_zero _ hβ'
    obtain ⟨W, W', ι, hcompl, hnd₁, hnd₂, hι⟩ := caseA_data hp hp2 hf1 hk hnd hdim Db
      (Units.mk0 β' hβ0) (by rw [Units.val_mk0, hβ', sq])
    obtain ⟨M, hM, hMK, hMε⟩ := corr_down Db ι Kc hKC hKN hKp
    subst hMK
    obtain ⟨U, U', ψ, -, hndU, -, -, L, hL, hML⟩ :=
      left_normal_form Db ι hcompl hnd₁ hnd₂ hι M hMε
    have hLc := isComponent_of_pComponent hodd hndU hL
    obtain ⟨hKq, ⟨eK⟩⟩ := quotient_of_left Db ψ M L hLc.1 hML
    have hY := LieType.CurtisTits.lieModel_of_mulEquiv eK (lieModel_center_psp4_three hKq hKm)
    have hU3 : 3 ≤ finrank k U := by
      by_contra h
      exact CatalogueBOrthogonal.orthogonal_small_no_pComponent _ h2 hndU (by omega) 2 L hL
    obtain ⟨t, n, e', hT, hadm', hm'⟩ :=
      orthogonal_component_models hp hp2 hf1 hk _ hndU hU3 hLc
    obtain ⟨rfl, rfl, rfl⟩ :=
      eq_psp4_of_two_lieModels hp hp2 le_rfl (isClassicalTag_of_mem_orthTuples hT) hadm' hm' hY
    exact (psp_mem_orthTuples hT).2.symm
  ·
    exfalso
    obtain ⟨T, _, _, ι, hT⟩ := caseB_data hp hp2 hf1 hk hnd hdim hnp Db hsq
    obtain ⟨M, hM, hMK, hMε⟩ := corr_down Db ι Kc hKC hKN hKp
    subst hMK
    obtain ⟨hq, hLM⟩ := hT _ hMε
    obtain ⟨hqK, ⟨eK⟩⟩ := centerQuotient_equiv Db ι M hq
    have hY := LieType.CurtisTits.lieModel_of_mulEquiv eK (lieModel_center_psp4_three hqK hKm)
    obtain ⟨h1, -⟩ := eq_psp4_of_two_lieModels hp hp2 le_rfl (Or.inl rfl)
      (GH74.statedClassicalModel_of_lieModel (by norm_num) hLM).1 hLM hY
    exact absurd h1 (by decide)

end CFSG.ComponentClassification.CatLeafProof.X11Char

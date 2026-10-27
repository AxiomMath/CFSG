module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabHubModels
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallE
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyOrth
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallB
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallD
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin

namespace MuTab

section Spin

variable {p e : ℕ} [Fact p.Prime]

theorem not_isSquare_neg_one_galoisField (he : 1 ≤ e) (hq3 : p ^ e % 4 = 3) :
    ¬ IsSquare (-1 : GaloisField p e) := by
  have : Fintype (GaloisField p e) := Fintype.ofFinite _
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card,
    GaloisField.card p e (by omega)]
  omega

theorem exists_unitaryPair_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaOdd 3 p e) (hq3 : p ^ e % 4 = 3) :
    ∃ R₁ ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p e)),
      ∃ R₂ ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p e)),
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have S := ModelFacts.spinCtx_pOmegaOdd (p := p) (n := 3) (e := e) (by norm_num) hp2 hq
  obtain ⟨fr₁, fr₂, hpair⟩ := OrthHub.exists_unitaryPair (K := GaloisField p e)
    (K' := GaloisField p (2 * e)) (p := p) (f := e) OrthHub.oddSys S.card_eq S.card_eq' S.odd_card
    (not_isSquare_neg_one_galoisField S.one_le hq3)
  obtain ⟨R₁, hR₁, e₁⟩ := (fundCorr_odd hp2 hq hadm).2 fr₁.La.range
    ⟨_, IsFundamental.of_frame fr₁⟩
  obtain ⟨R₂, hR₂, e₂⟩ := (fundCorr_odd hp2 hq hadm).2 fr₂.La.range
    ⟨_, IsFundamental.of_frame fr₂⟩
  refine ⟨R₁, hR₁, R₂, hR₂, S.unitary_of_map
    (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁)
    (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₂)
    ⟨fr₁.La.range ⊔ fr₂.La.range, ?_⟩⟩
  rw [e₁, e₂]
  exact hpair

theorem exists_unitaryPair_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p e) (hq3 : p ^ e % 4 = 3) :
    ∃ R₁ ∈ fundamentalSubgroups .POmegaMinus
        (Twisted.minusDatum 4 (minusCoeffs_irr p e)),
      ∃ R₂ ∈ fundamentalSubgroups .POmegaMinus
          (Twisted.minusDatum 4 (minusCoeffs_irr p e)),
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have S := ModelFacts.spinCtx_pOmegaMinus hadm hp2 hq
  obtain ⟨fr₁, fr₂, hpair⟩ := OrthHub.exists_unitaryPair (K := GaloisField p e)
    (K' := GaloisField p (2 * e)) (p := p) (f := e)
    (OrthHub.minusSys (minusCoeffs p e).1 (minusCoeffs p e).2) S.card_eq S.card_eq' S.odd_card
    (not_isSquare_neg_one_galoisField S.one_le hq3)
  obtain ⟨R₁, hR₁, e₁⟩ := (fundCorr_minus hp2 hq hadm).2 fr₁.La.range
    ⟨_, IsFundamental.of_frame fr₁⟩
  obtain ⟨R₂, hR₂, e₂⟩ := (fundCorr_minus hp2 hq hadm).2 fr₂.La.range
    ⟨_, IsFundamental.of_frame fr₂⟩
  refine ⟨R₁, hR₁, R₂, hR₂, S.unitary_of_map
    (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁)
    (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₂)
    ⟨fr₁.La.range ⊔ fr₂.La.range, ?_⟩⟩
  rw [e₁, e₂]
  exact hpair

end Spin

end MuTab

section Pairs

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem Ih8Model.muTab_unitaryPair_pOmegaOdd (M : Ih8Model p f Ω .POmegaOdd 3 e)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq3 : p ^ f % 4 = 3) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, ∃ W,
      UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have he := M.exp_eq_f (by decide)
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := MuTab.exists_unitaryPair_odd hp2 (he ▸ hq) M.admissible
    (he ▸ hq3)
  exact ⟨R₁, M.fund_subset_cls hne (by decide) (by decide) hR₁, R₂,
    M.fund_subset_cls hne (by decide) (by decide) hR₂, W, hW⟩

theorem Ih8Model.muTab_unitaryPair_pOmegaMinus (M : Ih8Model p f Ω .POmegaMinus 4 e)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq3 : p ^ f % 4 = 3) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, ∃ W,
      UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have he := M.exp_eq_f (by decide)
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := MuTab.exists_unitaryPair_minus hp2 (he ▸ hq) M.admissible
    (he ▸ hq3)
  exact ⟨R₁, M.fund_subset_cls hne (by decide) (by decide) hR₁, R₂,
    M.fund_subset_cls hne (by decide) (by decide) hR₂, W, hW⟩

end Pairs

namespace MuTab

section Split

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem split_pOmegaOdd3_minus (M : Ih8Model p f Ω .POmegaOdd 3 e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq3 : p ^ f % 4 = 3) :
    ∃ K ∈ Ω, dComp Ω K ≠ dstarComp Ω K := by
  have hG2 : StatedLieTag.POmegaOdd ≠ .G2 := by decide
  have hD4 : StatedLieTag.POmegaOdd ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.POmegaOdd = .PSL ∧ (3 : ℕ) = 2) := by simp
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS' hAB hAS hBS cAB cAS =>
    noThree_odd3 hp2 hq' M.admissible (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS
      cAB cAS
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_unitaryPair_pOmegaOdd hp2 hq hne hq3
  obtain ⟨-, hnc⟩ := M.muTab_unitary_ne_nc hp2 hq hD4 hR₁ hR₂ hW
  have hadj := M.muTab_dstarAdj_unitary hΩ hp2 hq hD4 hnpsl hq3 hR₁ hR₂ hW
  exact ⟨_, M.map_mem hR₁, M.muTab_dComp_ne hΩ hp2 hq hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

theorem split_pOmegaMinus4_minus (M : Ih8Model p f Ω .POmegaMinus 4 e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq3 : p ^ f % 4 = 3) :
    ∃ K ∈ Ω, dComp Ω K ≠ dstarComp Ω K := by
  have hG2 : StatedLieTag.POmegaMinus ≠ .G2 := by decide
  have hD4 : StatedLieTag.POmegaMinus ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.POmegaMinus = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS' hAB hAS hBS cAB cAS =>
    noThree_minus4 hp2 hq' M.admissible (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS
      cAB cAS
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_unitaryPair_pOmegaMinus hp2 hq hne hq3
  obtain ⟨-, hnc⟩ := M.muTab_unitary_ne_nc hp2 hq hD4 hR₁ hR₂ hW
  have hadj := M.muTab_dstarAdj_unitary hΩ hp2 hq hD4 hnpsl hq3 hR₁ hR₂ hW
  exact ⟨_, M.map_mem hR₁, M.muTab_dComp_ne hΩ hp2 hq hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

end Split

end MuTab

end CFSG.ClassicalInvolution.Asc77

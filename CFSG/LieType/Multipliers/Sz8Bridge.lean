module

public import CFSG.LieType.Multipliers.Sz8Matrix
public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.LieType.Multipliers.Sz8BridgeInputs
public import Certificates.Certificate10008
public meta import CFSG.LieType.Multipliers.Sz8Matrix
public meta import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.LieType.Multipliers.Sz8

open TauCeti CFSG.CosetTable

theorem mem_allF8 (c : F8) : c ∈ allF8 := by
  obtain ⟨c0, c1, c2⟩ := c
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> decide

theorem wordMat_eq_one {w : List (Fin 2 × Bool)} (h : wordArr w = ofMat 1) : wordMat w = 1 := by
  rw [wordMat, h, toMat_ofMat]

theorem rootMat_eq_wordMat_of_genCheck (h : genCheck = true) (c d : F8) :
    rootMat c d = wordMat (genWord c d) := by
  rw [genCheck, List.all_eq_true] at h
  have h' := h c (mem_allF8 c)
  rw [List.all_eq_true] at h'
  rw [wordMat, ← of_decide_eq_true (h' d (mem_allF8 d)), toMat_ofMat]

theorem matCheck_rels : matCheck rels = true :=
  Certificates.certificate10008.1

theorem genCheck_eq_true : genCheck = true :=
  Certificates.certificate10008.2.1

theorem card_le :
    Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 29120 :=
  Certificates.certificate10008.2.2

theorem lift_genSz_rels :
    ∀ r ∈ wordSet rels, FreeGroup.lift genSz r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  have h := matCheck_rels
  rw [matCheck, List.all_eq_true] at h
  exact lift_genSz_eq_one (wordMat_eq_one (of_decide_eq_true (h w hw)))

theorem closure_genSz : Subgroup.closure (Set.range genSz) = ⊤ :=
  closure_range_genSz (rootMat_eq_wordMat_of_genCheck genCheck_eq_true)

theorem isPresentation_genSz :
    IsPresentation genSz (wordSet rels) := by
  obtain ⟨hfin, hle⟩ := card_le
  exact IsPresentation.of_card_le lift_genSz_rels closure_genSz
    (hle.trans (by rw [card_suzukiGroup]))

theorem isPresentation
    {X : Type} [Group X] (e : suzukiGroup 1 ≃* X) :
    IsPresentation (fun i => e (genSz i)) (wordSet rels) :=
  isPresentation_genSz.mulEquiv e

end CFSG.LieType.Multipliers.Sz8

module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM11Check
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensusW
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Out
public import CFSG.Sporadic.Mathieu.M11
public import Certificates.Certificate110
public import Certificates.Certificate3120
public import Certificates.Certificate8041
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.Monster.Code.Weights

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M11

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ABGLocalTools CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem rep_m11Gens_zero : Rep 11 m11Gens[0]!
    (List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] *
      List.formPerm [7, 8]) := by
  intro x
  revert x
  decide

theorem rep_m11Gens_one : Rep 11 m11Gens[1]!
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]) := by
  intro x
  revert x
  decide

theorem closure_m11Gens : closure (permsA 11 m11Gens) = Blueprint.NativeSporadic.M11 := by
  have h : permsA 11 m11Gens =
      {List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8],
        List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]} := by
    ext x
    simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := hk
      interval_cases k
      · exact .inl (permOfArr_eq_of_rep rep_m11Gens_zero)
      · exact .inr (permOfArr_eq_of_rep rep_m11Gens_one)
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, permOfArr_eq_of_rep rep_m11Gens_zero⟩
      · exact ⟨1, by decide, permOfArr_eq_of_rep rep_m11Gens_one⟩
  rw [h]
  rfl

theorem m11_center_eq_bot : center ↥Blueprint.NativeSporadic.M11 = ⊥ := by
  have : IsSimpleGroup ↥Blueprint.NativeSporadic.M11 :=
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥Blueprint.NativeSporadic.M11) with
    h | h
  · exact h
  · exfalso
    let a : ↥Blueprint.NativeSporadic.M11 := ⟨_, subset_closure (Set.mem_insert _ _)⟩
    let b : ↥Blueprint.NativeSporadic.M11 :=
      ⟨_, subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
    have ha : a ∈ center ↥Blueprint.NativeSporadic.M11 := h ▸ mem_top a
    have hab := congrArg (fun x : ↥Blueprint.NativeSporadic.M11 =>
      ((x : Equiv.Perm (Fin 11)) 0 : ℕ)) (mem_center_iff.mp ha b)
    revert hab
    decide

theorem m11AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .M11) ↥Blueprint.NativeSporadic.M11 ⊤ where
  normal := inferInstance
  centralizer_eq_bot := by rw [coe_top, centralizer_univ, m11_center_eq_bot]
  nonempty_mulEquiv := ⟨Subgroup.topEquiv⟩
  exists_conj α := by
    obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Unc25G2.aut_inner (MulAut.congr Subgroup.topEquiv α)
    refine ⟨g, fun x => ?_⟩
    have h := hg (Subgroup.topEquiv x)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h
    exact h

theorem census_of_m11CheckW {dt dw : ℕ}
    (h : m11CheckW dt dw = true) :
    YCensus17 (⊤ : Subgroup ↥Blueprint.NativeSporadic.M11) (fun _ => False) := by
  simp only [m11CheckW, validK_eq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hg, hc⟩, hgen⟩, hsize⟩ := h
  exact yCensus17_top_of_checkW (k := 4) (m := 495) m11PS_lt
    (fun a hv ha => closure_m11Gens ▸ mem_closure_of_inWords hg hv ha) hc hgen hsize
    (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num) (by decide)

theorem sporadicCaseOdd_M11 (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .M11 :=
  sporadicCaseOdd_of_yCensus17 h32 h33 m11AutModel le_top yCensus_top_le_top
    (census_of_m11CheckW m11_check)

end CFSG.ComponentClassification.RankTwoSporadic.M11

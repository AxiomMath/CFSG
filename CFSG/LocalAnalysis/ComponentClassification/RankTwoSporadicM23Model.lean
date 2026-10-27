module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM23Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.Sporadic.Mathieu.M23

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M23

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem rep_m23Gens_zero : Rep 23 m23Gens[0]!
    (List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
      List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
      List.formPerm [20, 21]) := by
  intro x
  revert x
  decide

theorem rep_m23Gens_one : Rep 23 m23Gens[1]!
    (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
      List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]) := by
  intro x
  revert x
  decide

theorem closure_m23Gens : closure (permsA 23 m23Gens) = Blueprint.NativeSporadic.M23 := by
  have h : permsA 23 m23Gens =
      {List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
        List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
        List.formPerm [20, 21],
        List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
        List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]} := by
    ext x
    simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := hk
      interval_cases k
      · exact .inl (permOfArr_eq_of_rep rep_m23Gens_zero)
      · exact .inr (permOfArr_eq_of_rep rep_m23Gens_one)
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, permOfArr_eq_of_rep rep_m23Gens_zero⟩
      · exact ⟨1, by decide, permOfArr_eq_of_rep rep_m23Gens_one⟩
  rw [h]
  rfl

theorem card_m23 : Nat.card ↥Blueprint.NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq, Nat.card_eq_fintype_card]
  exact CFSG.M23.M23Group.card_M23

theorem m23_center_eq_bot : center ↥Blueprint.NativeSporadic.M23 = ⊥ := by
  have : IsSimpleGroup ↥Blueprint.NativeSporadic.M23 :=
    CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥Blueprint.NativeSporadic.M23) with
    h | h
  · exact h
  · exfalso
    let a : ↥Blueprint.NativeSporadic.M23 := ⟨_, subset_closure (Set.mem_insert _ _)⟩
    let b : ↥Blueprint.NativeSporadic.M23 :=
      ⟨_, subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
    have ha : a ∈ center ↥Blueprint.NativeSporadic.M23 := h ▸ mem_top a
    have hab := congrArg (fun x : ↥Blueprint.NativeSporadic.M23 =>
      ((x : Equiv.Perm (Fin 23)) 0 : ℕ)) (mem_center_iff.mp ha b)
    revert hab
    decide

theorem m23AutModel_of (hi : OuterAutomorphisms.inner ↥Blueprint.NativeSporadic.M23 = ⊤) :
    AutModel (Blueprint.NativeSporadic.Carrier .M23) ↥Blueprint.NativeSporadic.M23 ⊤ where
  normal := inferInstance
  centralizer_eq_bot := by rw [coe_top, centralizer_univ, m23_center_eq_bot]
  nonempty_mulEquiv := ⟨Subgroup.topEquiv⟩
  exists_conj α := by
    have hβ : MulAut.congr Subgroup.topEquiv α ∈
        OuterAutomorphisms.inner ↥Blueprint.NativeSporadic.M23 := by
      rw [hi]
      trivial
    obtain ⟨g, hg⟩ := hβ
    refine ⟨g, fun x => ?_⟩
    have h := congrArg (fun φ : MulAut ↥Blueprint.NativeSporadic.M23 => φ (Subgroup.topEquiv x))
      hg
    simp only [MulAut.conj_apply, MulAut.congr_apply] at h
    exact h.symm

theorem census_of_m23Check {sc sp : String} (h : m23Check sc sp = true) :
    YCensus17 (⊤ : Subgroup ↥Blueprint.NativeSporadic.M23) (fun _ => False) := by
  simp only [m23Check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hslp, hc⟩, hgen⟩, hsize⟩ := h
  exact yCensus17_top_of_check (k := 7) (m := 79695) closure_m23Gens m23PS_lt hslp hc hgen hsize
    (by rw [card_m23]; norm_num) (by decide)

end CFSG.ComponentClassification.RankTwoSporadic.M23

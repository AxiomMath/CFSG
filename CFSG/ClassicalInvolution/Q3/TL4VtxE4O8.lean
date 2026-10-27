module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Arr
public import CFSG.ClassicalInvolution.Q3.Q3TLTO8
public import Certificates.Certificate125

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.O8Data CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem forall₂_perms {L : List (Array ℕ)} (h : ∀ a ∈ L, ∃ g, Rep 360 a g) :
    List.Forall₂ (Rep 360) L (perms L) := by
  induction L with
  | nil => exact .nil
  | cons a L ih =>
    obtain ⟨g, hg⟩ := h a List.mem_cons_self
    refine .cons ?_ (ih fun b hb => h b (List.mem_cons_of_mem _ hb))
    rw [permOfArr_eq_of_rep hg]
    exact hg

theorem words_spec {ws : List (List ℤ)} (h : wordsOK ws = true) :
    List.Forall₂ (Rep 360) (ws.map omegaW) (perms (ws.map omegaW)) ∧
      ∀ g ∈ perms (ws.map omegaW), g ∈ omegaT := by
  have h' : ∀ w ∈ ws, lettersOK 17 w = true := List.all_eq_true.mp h
  refine ⟨forall₂_perms fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    exact ⟨_, (omegaW_spec (h' w hw)).1⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    exact (omegaW_spec (h' w hw)).2

theorem rep_main {i : ℕ} (hi : i < 3) :
    Rep 360 (xA i) (mainPerm i) := O8.main_rep hi

theorem data_spec {a : Array ℕ} (ha : a ∈ [u0A (), v0A (), threeA ()] ++ wsA ()) :
    Rep 360 a (permOfArr 360 a) ∧ permOfArr 360 a ∈ omegaT := by
  obtain ⟨g, hg, hr⟩ := Certificates.certificate125.1 a ha
  rw [permOfArr_eq_of_rep hr]
  exact ⟨hr, hg⟩

theorem u0_spec : Rep 360 (u0A ()) u0 ∧ u0 ∈ omegaT := data_spec (by simp)

theorem v0_spec : Rep 360 (v0A ()) v0 ∧ v0 ∈ omegaT := data_spec (by simp)

theorem three_spec : Rep 360 (threeA ()) three ∧ three ∈ omegaT := data_spec (by simp)

theorem forall₂_L0 : List.Forall₂ (Rep 360) (L0A ()) L0P :=
  forall₂_q8A (rep_main (by norm_num)) u0_spec.1 v0_spec.1

theorem u0_sq : u0 * u0 = mainPerm 0 := Certificates.certificate125.2.1.1

theorem x0_sq : mainPerm 0 * mainPerm 0 = 1 := Certificates.certificate125.2.1.2.1

theorem x0_ne_one : mainPerm 0 ≠ 1 := Certificates.certificate125.2.1.2.2.1

theorem mem_K0_iff (x : Equiv.Perm (Fin 360)) : x ∈ K0 ↔ x ∈ L0P :=
  Certificates.certificate125.2.1.2.2.2 x

theorem K0_le : K0 ≤ omegaT := by
  rw [K0, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact u0_spec.2
  · exact v0_spec.2

end CFSG.ClassicalInvolution.Q3.TL4.E4O8

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Act
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshWordCard

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b

section Alpha

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

variable {d : G} {α β : ℕ}

theorem mem_V_of_centralizes (he2 : orderOf e = 2) {y : G} (hye : e * y = y * e)
    (hyc : cG e₀ * y = y * cG e₀)
    (hyv1 : valG e₀ (wA1 ++ wB1) * y = y * valG e₀ (wA1 ++ wB1))
    (hyv2 : valG e₀ (wA2 ++ wB2) * y = y * valG e₀ (wA2 ++ wB2)) :
    ∃ m, m < 16 ∧ y = valG e₀ (vWord14 m) := by
  have hyHc : y ∈ HcG e₀ :=
    ⟨mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hye,
      mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hyc⟩
  obtain ⟨k, a, σ, hk, hy, hrep⟩ := exists_index_of_mem_Hc e₀ hyHc
  have c1 : commT yEl[k]! (tblW wJ) = true :=
    commT_of_commute_valG e₀ hy hrep (by rw [valG_wJ]; exact hyc.symm)
  have c2 : commT yEl[k]! (tblW (wA1 ++ wB1)) = true :=
    commT_of_commute_valG e₀ hy hrep hyv1.symm
  have c3 : commT yEl[k]! (tblW (wA2 ++ wB2)) = true :=
    commT_of_commute_valG e₀ hy hrep hyv2.symm
  have c4 : commT yEl[k]! (tblW wE) = true :=
    commT_of_commute_valG e₀ hy hrep
      (by rw [show valG e₀ wE = e from valG_tau e₀ he2]; exact hye.symm)
  have hcv : cvCheck = true := lemma5_parts.2.2.2.2.1
  unfold cvCheck at hcv
  have h1 := List.all_eq_true.1 hcv k (List.mem_range.2 hk)
  simp only [c1, c2, c3, c4, Bool.and_self, Bool.not_true, Bool.false_or] at h1
  obtain ⟨m, hm, hm2⟩ := List.any_eq_true.1 h1
  exact ⟨m, List.mem_range.1 hm, eq_valG_of_tblEq e₀ hy hrep hm2⟩

theorem valG_vWord14 (m : ℕ) :
    valG e₀ (vWord14 m) = valG e₀ wJ ^ (m % 2) * valG e₀ (wA1 ++ wB1) ^ (m / 2 % 2) *
      valG e₀ (wA2 ++ wB2) ^ (m / 4 % 2) * valG e₀ wE ^ (m / 8 % 2) := by
  unfold vWord14
  simp only [valG_append, valG_powW]

theorem lift_vWordE (g : Fin 6 → G) (m : ℕ) :
    FreeGroup.lift g (FreeGroup.mk (vWordE m)) =
      FreeGroup.lift g (FreeGroup.mk (swE [1, 1])) ^ (m % 2) *
        FreeGroup.lift g (FreeGroup.mk (swE [1, 3])) ^ (m / 2 % 2) *
        FreeGroup.lift g (FreeGroup.mk (swE [2, 4])) ^ (m / 4 % 2) *
        FreeGroup.lift g (FreeGroup.mk (swE [6])) ^ (m / 8 % 2) := by
  unfold vWordE
  simp only [lift_mk_append, lift_mk_powW]

theorem vgen_values :
    FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (swE [1, 1])) = valG e₀ wJ ∧
    FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (swE [1, 3])) = valG e₀ (wA1 ++ wB1) ∧
    FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (swE [2, 4])) = valG e₀ (wA2 ++ wB2) ∧
    FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (swE [6])) = valG e₀ wE := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hw : swE [1, 1] = [(0, true)] ++ [(0, true)] := by decide
    rw [hw, lift_mk_append, lift_mk_single]
    show gen5 e₀ d α β 0 * gen5 e₀ d α β 0 = _
    rw [gen5_a1, ← valG_append]
    exact valG_eq_of_tblEq e₀ (by
      have h : sActOK = true := lemma5_parts.1
      simp only [sActOK, Bool.and_eq_true] at h
      exact h.2)
  · have hw : swE [1, 3] = [(0, true)] ++ [(2, true)] := by decide
    rw [hw, lift_mk_append, lift_mk_single, lift_mk_single, valG_append]
    show gen5 e₀ d α β 0 * gen5 e₀ d α β 2 = _
    rw [gen5_a1, gen5_b1]
  · have hw : swE [2, 4] = [(1, true)] ++ [(3, true)] := by decide
    rw [hw, lift_mk_append, lift_mk_single, lift_mk_single, valG_append]
    show gen5 e₀ d α β 1 * gen5 e₀ d α β 3 = _
    rw [gen5_a2, gen5_b2]
  · have hw : swE [6] = [(5, true)] := by decide
    rw [hw, lift_mk_single]
    show gen5 e₀ d α β 5 = _
    rw [gen5_e]

theorem eModel_true : ModelOK 16 16 6 eGens relE 128 := eModelOK

theorem eGens_size : eGens.size = 6 := rfl

theorem comp_fix (hα : α < 2) (hβ : β < 2) (hd : CentralSwap e₀ α d)
    (hrel : ∀ r ∈ rel4 α β, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1) :
    ∀ w ∈ vgenE,
      (sG e₀ * gen5 e₀ d α β 6 * sG e₀ * gen5 e₀ d α β 6 * sG e₀ * gen5 e₀ d α β 6)⁻¹ *
          FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk w) *
        (sG e₀ * gen5 e₀ d α β 6 * sG e₀ * gen5 e₀ d α β 6 * sG e₀ * gen5 e₀ d α β 6) =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk w) := by
  intro w hw
  have hrel5 := gen5_relNQL e₀ hα hβ hrel
  have hrelE := gE_rel e₀ hrel5
  have hcomp := comp_conj (hx := gE_x e₀ hα hβ hrel5) (hs := gE_s e₀ hd (β := β))
  rw [conj_lift_substW _ (gE e₀ d α β) (compF α β) hcomp w]
  have hcf : compFixV α β = true := (lemma5_parts.2.2.2.2.2.2.1 α β hα hβ).2.1
  have h1 := List.all_eq_true.1 hcf w hw
  exact lift_eq_of_modelEq (n := 16) (m := 16) (by norm_num) eGens_size eModel_true
    (gE e₀ d α β) hrelE (w₁ := substW (compF α β) w) (w₂ := w) h1

theorem gE_injective (hrelE : ∀ r ∈ relE, FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk r) = 1) :
    Function.Injective (modelHomOf (by norm_num : (16 : ℕ) < 2 ^ 32) eGens_size eModel_true
      (gE e₀ d α β) hrelE) := by
  refine modelHomOf_injective (by norm_num : (16 : ℕ) < 2 ^ 32) eGens_size eModel_true
    lemma5_model_parts.1 (j := 7) (by norm_num) (gE e₀ d α β) hrelE [(0, true), (0, true)]
    ((tblEq_iff_eq (rep_modelT (by norm_num : (16 : ℕ) < 2 ^ 32) eGens_size eModel_true _)
      (rep_modelT (by norm_num : (16 : ℕ) < 2 ^ 32) eGens_size eModel_true _)).2 rfl) ?_
  have h := (vgen_values e₀ (d := d) (α := α) (β := β)).1
  rw [show swE [1, 1] = [(0, true), (0, true)] from by decide, valG_wJ] at h
  rw [h]
  exact cG_ne_one e₀

theorem lemma5_alpha_eq (he2 : orderOf e = 2) (hα : α < 2) (hβ : β < 2)
    (hd : CentralSwap e₀ α d)
    (hrel : ∀ r ∈ rel4 α β, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1) :
    α = β ∧ ∃ k : ℕ, k < 2 ∧
      sG e₀ * gen5 e₀ d α β 6 * sG e₀ * gen5 e₀ d α β 6 * sG e₀ * gen5 e₀ d α β 6 =
        cG e₀ ^ k := by
  have hrel5 := gen5_relNQL e₀ hα hβ hrel
  have hrelE := gE_rel e₀ hrel5
  have hcomp := comp_conj (hx := gE_x e₀ hα hβ hrel5) (hs := gE_s e₀ hd (β := β))
  have hfix := comp_fix e₀ hα hβ hd hrel
  obtain ⟨vc, v1, v2, ve⟩ := vgen_values e₀ (d := d) (α := α) (β := β)
  set y := sG e₀ * gen5 e₀ d α β 6 * sG e₀ * gen5 e₀ d α β 6 * sG e₀ * gen5 e₀ d α β 6 with hy
  have hcomm : ∀ w ∈ vgenE, FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk w) * y =
      y * FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk w) := by
    intro w hw
    have h := hfix w hw
    calc FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk w) * y =
        y * (y⁻¹ * FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk w) * y) := by group
      _ = y * FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk w) := by rw [h]
  have hc : cG e₀ * y = y * cG e₀ := by
    have := hcomm (swE [1, 1]) (by simp [vgenE])
    rwa [vc, valG_wJ] at this
  have hv1 : valG e₀ (wA1 ++ wB1) * y = y * valG e₀ (wA1 ++ wB1) := by
    have := hcomm (swE [1, 3]) (by simp [vgenE])
    rwa [v1] at this
  have hv2 : valG e₀ (wA2 ++ wB2) * y = y * valG e₀ (wA2 ++ wB2) := by
    have := hcomm (swE [2, 4]) (by simp [vgenE])
    rwa [v2] at this
  have hye : e * y = y * e := by
    have := hcomm (swE [6]) (by simp [vgenE])
    rwa [ve, show valG e₀ wE = e from valG_tau e₀ he2] at this
  obtain ⟨m, hm, hym⟩ := mem_V_of_centralizes e₀ he2 hye hc hv1 hv2
  have hyE : y = FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (vWordE m)) := by
    rw [hym, valG_vWord14, lift_vWordE, vc, v1, v2, ve]
  have hconj : ∀ i : Fin 6, FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (compF α β i)) =
      FreeGroup.lift (gE e₀ d α β)
        (FreeGroup.mk (invW (vWordE m) ++ [(i, true)] ++ vWordE m)) := by
    intro i
    rw [← hcomp i, lift_mk_append, lift_mk_append, lift_mk_invW, lift_mk_single, ← hyE]
  have hinj := gE_injective e₀ (d := d) (α := α) (β := β) hrelE
  have htab : ∀ i : Fin 6, tblEq 16 (eT (compF α β i))
      (eT (invW (vWordE m) ++ [(i, true)] ++ vWordE m)) = true := fun i =>
    modelT_eq_of_lift_eq (by norm_num) eGens_size eModel_true (gE e₀ d α β) hrelE hinj (hconj i)
  have hin : compInnerV α β = true := (lemma5_parts.2.2.2.2.2.2.1 α β hα hβ).2.2
  unfold compInnerV at hin
  have h1 := List.all_eq_true.1 hin m (List.mem_range.2 hm)
  have hall : ((List.finRange 6).all fun i => tblEq 16 (eT (compF α β i))
      (eT (invW (vWordE m) ++ [(i, true)] ++ vWordE m))) = true :=
    List.all_eq_true.2 (fun i _ => htab i)
  rw [hall] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h1
  refine ⟨h1.1, m, h1.2, ?_⟩
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
  · rw [hym, valG_vWord14]
    simp
  · rw [hym, valG_vWord14, valG_wJ]
    simp

end Alpha

end CFSG.EvenSporadicStandard.M12Std.Yosh

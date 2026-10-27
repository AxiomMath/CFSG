module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarEval
public import CFSG.Sporadic.SmallOddCore.HS
public import Certificates.Certificate26130

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.LieType.Multipliers
open scoped commutatorElement

section Rho


theorem harModelOK_true : harModelOK = true := Certificates.certificate26130.1

@[expose] noncomputable def harYPerm (i : Fin 6) : Equiv.Perm (Fin 11200) := tp 11200 (harY i)

theorem rep_harY (i : Fin 6) :
    Rep 11200 (harY i) (harYPerm i) ∧ Rep 11200 (harYI i) (harYPerm i)⁻¹ := by
  have h := harModelOK_true
  simp only [harModelOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨hperm, -⟩, -⟩ := h
  obtain ⟨hp, hi⟩ := hperm i
  have hr := rep_tp (n := 11200) hp
  exact ⟨hr, Rep.inv_of_invOK hr hi⟩

theorem harY_relators :
    (∀ i, ∀ r ∈ wordSet hsRels, ⁅harYPerm i, FreeGroup.lift harYPerm r⁆ = 1) ∧
      ∀ i, FreeGroup.lift harYPerm (hsCommW i) = harYPerm i := by
  have h := harModelOK_true
  simp only [harModelOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨-, hrel⟩, hcomm⟩ := h
  have hn : (11200 : ℕ) < 2 ^ 32 := by norm_num
  constructor
  · intro i r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have := rep_evalW hn (g := harY) (gi := harYI) (f := harYPerm)
      (fun i => (rep_harY i).1) (fun i => (rep_harY i).2) w
    have hc := (commTT_iff (rep_harY i).1 this).1 (hrel w hw i)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hc
  · intro i
    have := rep_evalW hn (g := harY) (gi := harYI) (f := harYPerm)
      (fun i => (rep_harY i).1) (fun i => (rep_harY i).2) (hsCommWord i)
    exact (tblEq_iff_eq this (rep_harY i).1).1 (hcomm i)

noncomputable def harRhoHom : HSCover →* Equiv.Perm (Fin 11200) :=
  PresentedGroup.toGroup (f := harYPerm) (lift_coverRelators_eq_one_iff.2 harY_relators)

theorem harRhoHom_of (i : Fin 6) : harRhoHom (PresentedGroup.of i) = harYPerm i :=
  PresentedGroup.toGroup.of _

end Rho

section Pi


theorem harPOK_true : harPOK = true := Certificates.certificate26130.2.1

@[expose] noncomputable def harXPerm (i : Fin 6) : Equiv.Perm (Fin 3850) :=
  FreeGroup.lift (fun j : Fin 2 => hsGen j.val) (FreeGroup.mk (hsGenWords.getD i.val []))

theorem rep_harA (j : Fin 2) :
    Rep 3850 (harA j) (hsGen j.val) ∧ Rep 3850 (harAI j) (hsGen j.val)⁻¹ := by
  have h := harPOK_true
  simp only [harPOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨⟨⟨hA, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  obtain ⟨-, hi⟩ := hA j
  have hr : Rep 3850 (harA j) (hsGen j.val) := by
    have := hs_groupData.rep j.val (by
      have : hsPGTbls.size = 2 := rfl
      omega)
    simpa [harA] using this
  exact ⟨hr, Rep.inv_of_invOK hr hi⟩

theorem rep_harX (i : Fin 6) :
    Rep 3850 (harX i) (harXPerm i) ∧ Rep 3850 (harXI i) (harXPerm i)⁻¹ := by
  have h := rep_evalW (n := 3850) (by norm_num) (g := harA) (gi := harAI)
    (f := fun j : Fin 2 => hsGen j.val) (fun j => (rep_harA j).1) (fun j => (rep_harA j).2)
    (hsGenWords.getD i.val [])
  have h2 : Rep 3850 (harX i) (harXPerm i) := h
  have hPOK := harPOK_true
  simp only [harPOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at hPOK
  obtain ⟨⟨⟨⟨⟨-, hX⟩, -⟩, -⟩, -⟩, -⟩ := hPOK
  obtain ⟨-, hi⟩ := hX i
  exact ⟨h2, Rep.inv_of_invOK h2 hi⟩

theorem harXPerm_mem (i : Fin 6) : harXPerm i ∈ hsP := by
  have hgen : ∀ j : Fin 2, hsGen j.val ∈ hsP := fun j =>
    hs_groupData.mem (by
      have : hsPGTbls.size = 2 := rfl
      omega)
  exact CFSG.Sporadic.Recognition.CoverTransfer.lift_mk_mem (K := hsP) (fun l _ => hgen l.1)

end Pi

section PiHom


theorem harX_relators :
    (∀ i, ∀ r ∈ wordSet hsRels, ⁅harXPerm i, FreeGroup.lift harXPerm r⁆ = 1) ∧
      ∀ i, FreeGroup.lift harXPerm (hsCommW i) = harXPerm i := by
  have h := harPOK_true
  simp only [harPOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, hrel⟩, hcomm⟩, -⟩, -⟩ := h
  have hn : (3850 : ℕ) < 2 ^ 32 := by norm_num
  constructor
  · intro i r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have := rep_evalW hn (g := harX) (gi := harXI) (f := harXPerm)
      (fun i => (rep_harX i).1) (fun i => (rep_harX i).2) w
    have h1 : FreeGroup.lift harXPerm (FreeGroup.mk w) = 1 :=
      (tblEq_idT_iff hn this).1 (hrel w hw)
    rw [h1]
    simp
  · intro i
    have := rep_evalW hn (g := harX) (gi := harXI) (f := harXPerm)
      (fun i => (rep_harX i).1) (fun i => (rep_harX i).2) (hsCommWord i)
    exact (tblEq_iff_eq this (rep_harX i).1).1 (hcomm i)

@[expose] noncomputable def harPiHom0 : HSCover →* Equiv.Perm (Fin 3850) :=
  PresentedGroup.toGroup (f := harXPerm) (lift_coverRelators_eq_one_iff.2 harX_relators)

theorem harPiHom0_of (i : Fin 6) : harPiHom0 (PresentedGroup.of i) = harXPerm i :=
  PresentedGroup.toGroup.of _

theorem harPiHom0_mem (x : HSCover) : harPiHom0 x ∈ hsP := by
  have hx : x ∈ closure (Set.range (PresentedGroup.of : Fin 6 → HSCover)) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [harPiHom0_of]
    exact harXPerm_mem i
  | one => simp
  | mul y z _ _ hy hz => rw [map_mul]; exact hsP.mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact hsP.inv_mem hy

@[expose] noncomputable def harPiHom : HSCover →* ↥hsP :=
  harPiHom0.codRestrict hsP harPiHom0_mem

theorem harPiHom_of (i : Fin 6) :
    ((harPiHom (PresentedGroup.of i) : ↥hsP) : Equiv.Perm (Fin 3850)) = harXPerm i :=
  harPiHom0_of i

theorem harPiHom_coe (x : HSCover) :
    ((harPiHom x : ↥hsP) : Equiv.Perm (Fin 3850)) = harPiHom0 x := rfl

theorem hom_lift_of {M : Type*} [Group M] (f : HSCover →* M) (w : FreeGroup (Fin 6)) :
    f (FreeGroup.lift (PresentedGroup.of : Fin 6 → HSCover) w) =
      FreeGroup.lift (fun i => f (PresentedGroup.of i)) w := by
  have : f.comp (FreeGroup.lift (PresentedGroup.of : Fin 6 → HSCover)) =
      FreeGroup.lift (fun i => f (PresentedGroup.of i)) :=
    FreeGroup.ext_hom _ _ (fun i => by simp)
  exact DFunLike.congr_fun this w

theorem harPiHom0_lift (w : FreeGroup (Fin 6)) :
    harPiHom0 (FreeGroup.lift (PresentedGroup.of : Fin 6 → HSCover) w) =
      FreeGroup.lift harXPerm w := by
  rw [hom_lift_of]
  congr 1

theorem harPiHom_surjective : Function.Surjective harPiHom := by
  have hPOK := harPOK_true
  simp only [harPOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at hPOK
  obtain ⟨⟨-, hA⟩, hB⟩ := hPOK
  have hn : (3850 : ℕ) < 2 ^ 32 := by norm_num
  have hword : ∀ (w : List (Fin 6 × Bool)) (j : Fin 2),
      tblEq 3850 (evalW 3850 harX harXI w) (harA j) = true →
      hsGen j.val ∈ harPiHom0.range := by
    intro w j h
    have hr := rep_evalW hn (g := harX) (gi := harXI) (f := harXPerm)
      (fun i => (rep_harX i).1) (fun i => (rep_harX i).2) w
    have heq : FreeGroup.lift harXPerm (FreeGroup.mk w) = hsGen j.val :=
      (tblEq_iff_eq hr (rep_harA j).1).1 h
    exact ⟨FreeGroup.lift (PresentedGroup.of : Fin 6 → HSCover) (FreeGroup.mk w), by
      rw [harPiHom0_lift, heq]⟩
  have h0 := hword hsSurjA 0 hA
  have h1 := hword hsSurjB 1 hB
  have hle : hsP ≤ harPiHom0.range := by
    rw [hs_groupData.gen, closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl2 : l < 2 := by simpa [hsPGTbls] using hl
    interval_cases l
    · exact h0
    · exact h1
  intro y
  obtain ⟨x, hx⟩ := hle y.2
  exact ⟨x, Subtype.ext hx⟩

end PiHom

end CFSG.EvenSporadicStandard.TwoHS

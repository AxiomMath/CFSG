module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarEval
public import Certificates.Certificate26760

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.LieType.Multipliers
  CFSG.EvenSporadicStandard.TwoHS
open scoped commutatorElement

@[expose] noncomputable def h1408GenPerm (j : Fin 7) : Equiv.Perm (Fin 1408) :=
  tp 1408 (h1408T j.val)

@[expose] noncomputable def h1408XPerm (i : Fin 6) : Equiv.Perm (Fin 1408) :=
  tp 1408 (h1408X i)

@[expose] noncomputable def h1408VPerm : Equiv.Perm (Fin 1408) := tp 1408 h1408V

@[expose] def blocks1408 : Subgroup (Equiv.Perm (Fin 1408)) where
  carrier := {g | ∀ i : Fin 1408, (g i).val < 704 ↔ i.val < 704}
  mul_mem' := by
    intro g h hg hh i
    rw [Equiv.Perm.mul_apply]
    exact (hg (h i)).trans (hh i)
  one_mem' := by
    intro i
    simp
  inv_mem' := by
    intro g hg i
    have h := hg (g⁻¹ i)
    simpa using h.symm

@[expose] def relVal (r : List (Fin 6 × Bool)) : HSCover :=
  FreeGroup.lift (PresentedGroup.of : Fin 6 → HSCover) (FreeGroup.mk r)

theorem h1408GenPerm_castSucc (i : Fin 6) : h1408GenPerm (Fin.castSucc i) = h1408XPerm i := rfl

theorem h1408GenPerm_last : h1408GenPerm 6 = h1408VPerm := rfl

section Cert


theorem h1408PermOK_true : h1408PermOK = true := Certificates.certificate26760.1

theorem h1408RelOK_true : h1408RelOK = true := Certificates.certificate26760.2.1

theorem h1408SigmaOK_true : h1408SigmaOK = true := Certificates.certificate26760.2.2.1

theorem h1408CentralOK_true : h1408CentralOK = true :=
  Certificates.certificate26760.2.2.2.1

theorem h1408BlockOK_true : h1408BlockOK = true := Certificates.certificate26760.2.2.2.2

private theorem h1408PermOK_parts :
    ((∀ i : Fin 6, permOK 1408 (h1408X i) = true ∧
        invOK 1408 (h1408X i) (h1408XI i) = true) ∧
      permOK 1408 h1408V = true) ∧ invoOK 1408 h1408V = true := by
  have h := h1408PermOK_true
  simpa only [h1408PermOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] using h

private theorem h1408RelOK_parts :
    (∀ r ∈ hsRels, ∀ i : Fin 6,
        commTT 1408 (h1408X i) (evalW 1408 h1408X h1408XI r) = true) ∧
      ∀ i : Fin 6, tblEq 1408 (evalW 1408 h1408X h1408XI (hsCommWord i)) (h1408X i) = true := by
  have h := h1408RelOK_true
  simpa only [h1408RelOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] using h

private theorem h1408SigmaOK_parts :
    ∀ i : Fin 6, tblEq 1408 (conjT 1408 h1408V h1408V (h1408X i))
      (wordTbl 1408 h1408Xs (sigWords.getD i.val [])) = true := by
  have h := h1408SigmaOK_true
  simpa only [h1408SigmaOK, List.all_eq_true, List.mem_finRange, forall_const] using h

private theorem h1408CentralOK_parts :
    involOK 1408 h1408T25 = true ∧
      ∀ p : ℕ, p ∈ List.range 1408 → ap h1408T25 p ≠ p := by
  have h := h1408CentralOK_true
  simp only [h1408CentralOK, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1, fun p hp => by simpa only [bne_iff_ne, ne_eq] using h.2 p hp⟩

private theorem h1408BlockOK_parts :
    (∀ i : Fin 6, (∀ k : ℕ, k < 704 → ap (h1408X i) k < 704) ∧
        (∀ k : ℕ, k < 704 → 704 ≤ ap (h1408X i) (704 + k))) ∧
      (∀ k : ℕ, k < 704 → ap h1408V k = 704 + k ∧ ap h1408V (704 + k) = k) := by
  have h := h1408BlockOK_true
  simp only [h1408BlockOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    List.mem_range, decide_eq_true_eq, beq_iff_eq, forall_const] at h
  exact h

theorem rep_h1408X (i : Fin 6) :
    Rep 1408 (h1408X i) (h1408XPerm i) ∧ Rep 1408 (h1408XI i) (h1408XPerm i)⁻¹ := by
  obtain ⟨hp, hi⟩ := h1408PermOK_parts.1.1 i
  have hr := rep_tp (n := 1408) hp
  exact ⟨hr, Rep.inv_of_invOK hr hi⟩

theorem rep_h1408V : Rep 1408 h1408V h1408VPerm := by
  exact rep_tp (n := 1408) h1408PermOK_parts.1.2

theorem rep_h1408Gen (j : Fin 7) : Rep 1408 (h1408T j.val) (h1408GenPerm j) := by
  by_cases hj : j.val < 6
  · exact (rep_h1408X ⟨j.val, hj⟩).1
  · have h6 : j = 6 := Fin.ext (by omega)
    subst h6
    exact rep_h1408V

theorem h1408VPerm_mul_self : h1408VPerm * h1408VPerm = 1 := by
  have h := sq_eq_one_of_invoOK rep_h1408V h1408PermOK_parts.2
  simpa [pow_two] using h

theorem h1408X_relators :
    (∀ i, ∀ r ∈ wordSet hsRels, ⁅h1408XPerm i, FreeGroup.lift h1408XPerm r⁆ = 1) ∧
      ∀ i, FreeGroup.lift h1408XPerm (hsCommW i) = h1408XPerm i := by
  have hrel := h1408RelOK_parts.1
  have hcomm := h1408RelOK_parts.2
  have hn : (1408 : ℕ) < 2 ^ 32 := by norm_num
  constructor
  · intro i r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have := rep_evalW hn (g := h1408X) (gi := h1408XI) (f := h1408XPerm)
      (fun i => (rep_h1408X i).1) (fun i => (rep_h1408X i).2) w
    have hc := (commTT_iff (rep_h1408X i).1 this).1 (hrel w hw i)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hc
  · intro i
    have := rep_evalW hn (g := h1408X) (gi := h1408XI) (f := h1408XPerm)
      (fun i => (rep_h1408X i).1) (fun i => (rep_h1408X i).2) (hsCommWord i)
    exact (tblEq_iff_eq this (rep_h1408X i).1).1 (hcomm i)

noncomputable def rho1408 : HSCover →* Equiv.Perm (Fin 1408) :=
  PresentedGroup.toGroup (f := h1408XPerm) (lift_coverRelators_eq_one_iff.2 h1408X_relators)

theorem rho1408_of (i : Fin 6) : rho1408 (PresentedGroup.of i) = h1408XPerm i :=
  PresentedGroup.toGroup.of _

theorem h1408VPerm_conj (i : Fin 6) :
    h1408VPerm * h1408XPerm i * h1408VPerm⁻¹ =
      wordVal ((List.finRange 6).map h1408XPerm) (sigWords.getD i.val []) := by
  have hSig := h1408SigmaOK_parts i
  have hconj : Rep 1408 (conjT 1408 h1408V h1408V (h1408X i))
      (h1408VPerm * h1408XPerm i * h1408VPerm⁻¹) :=
    Rep.compT (Rep.compT rep_h1408V (rep_h1408X i).1)
      (Rep.inv_of_invoOK rep_h1408V h1408PermOK_parts.2)
  have hg : ∀ g ∈ h1408Xs, permOK 1408 g = true := by
    intro g hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact (h1408PermOK_parts.1.1 j).1
  have hlen : h1408Xs.length = 6 := by simp [h1408Xs]
  have hw : ∀ l ∈ sigWords.getD i.val [], 1 ≤ l ∧ l ≤ h1408Xs.length := by
    rw [hlen]
    fin_cases i <;> decide
  have hrep := rep_wordTbl'' (n := 1408) (by norm_num) (gs := h1408Xs) hg
    (sigWords.getD i.val []) hw
  have hmap : h1408Xs.map (tp 1408) = (List.finRange 6).map h1408XPerm := rfl
  rw [hmap] at hrep
  exact (tblEq_iff_eq hconj hrep).1 hSig

theorem h1408R25_mem : h1408R25 ∈ hsRels := by
  decide

theorem relVal_mem_center {r : List (Fin 6 × Bool)} (hr : r ∈ hsRels) :
    relVal r ∈ center HSCover := by
  have hmem : FreeGroup.mk r ∈ wordSet hsRels :=
    List.mem_map.mpr ⟨r, hr, rfl⟩
  have hlift : FreeGroup.lift (PresentedGroup.of : Fin 6 → HSCover) =
      PresentedGroup.mk (coverRelators (wordSet hsRels) hsCommW) :=
    FreeGroup.ext_hom _ _ fun i => by simp [FreeGroup.lift_apply_of, PresentedGroup.of]
  have hrel : relVal r =
      PresentedGroup.mk (coverRelators (wordSet hsRels) hsCommW) (FreeGroup.mk r) := by
    rw [relVal, hlift]
  rw [hrel]
  exact mk_mem_center (R := wordSet hsRels) (w := hsCommW) hmem

theorem rho1408_relVal (r : List (Fin 6 × Bool)) :
    rho1408 (relVal r) = FreeGroup.lift h1408XPerm (FreeGroup.mk r) := by
  have h : rho1408.comp (FreeGroup.lift (PresentedGroup.of : Fin 6 → HSCover)) =
      FreeGroup.lift (fun i => rho1408 (PresentedGroup.of i)) :=
    FreeGroup.ext_hom _ _ fun i => by
      simp [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  have h2 := DFunLike.congr_fun h (FreeGroup.mk r)
  simp only [MonoidHom.comp_apply, rho1408_of] at h2
  simpa [relVal] using h2

theorem rho1408_relVal_R25_ne_one : rho1408 (relVal h1408R25) ≠ 1 := by
  intro h1
  have hg : Rep 1408 h1408T25 (FreeGroup.lift h1408XPerm (FreeGroup.mk h1408R25)) := by
    simpa only [h1408T25] using
      rep_evalW (n := 1408) (by norm_num) (g := h1408X) (gi := h1408XI)
        (f := h1408XPerm) (fun i => (rep_h1408X i).1) (fun i => (rep_h1408X i).2) h1408R25
  rw [rho1408_relVal] at h1
  rw [h1] at hg
  have h0 := hg 0 (by norm_num)
  rw [idx_one] at h0
  exact (h1408CentralOK_parts.2 0 (by simp)) h0

theorem rho1408_mem_blocks (x : HSCover) : rho1408 x ∈ blocks1408 := by
  have hx : x ∈ closure (Set.range (PresentedGroup.of : Fin 6 → HSCover)) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [rho1408_of]
    rintro ⟨v, hv⟩
    change (h1408XPerm i ⟨v, hv⟩).val < 704 ↔ v < 704
    have hp : ap (h1408X i) v = (h1408XPerm i ⟨v, hv⟩).val := by
      have h0 := (rep_h1408X i).1 v hv
      rwa [idx_of_lt (h1408XPerm i) hv, Equiv.Perm.smul_def] at h0
    have hblock := h1408BlockOK_parts.1 i
    constructor
    · intro h
      by_contra hlt
      have hk : v - 704 < 704 := by omega
      have hc := hblock.2 (v - 704) hk
      rw [show 704 + (v - 704) = v by omega, hp] at hc
      omega
    · intro h
      have hc := hblock.1 v h
      rwa [hp] at hc
  | one => simpa using blocks1408.one_mem
  | mul y z _ _ hy hz => rw [map_mul]; exact blocks1408.mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact blocks1408.inv_mem hy

private theorem idx_eq_val (g : Equiv.Perm (Fin 1408)) (i : ℕ) (hi : i < 1408) :
    idx 1408 g i = (g ⟨i, hi⟩).val := by
  rw [idx_of_lt g hi, Equiv.Perm.smul_def]

private theorem rep_val_eq {T : Table} {g : Equiv.Perm (Fin 1408)}
    (h : Rep 1408 T g) (p : Fin 1408) (ha : ap T p.val = 704) :
    (g p).val = 704 := by
  rw [← idx_eq_val g p.val p.isLt, ← h p.val p.isLt]
  exact ha

@[expose] def h1408Pt0 : Fin 1408 := ⟨0, by norm_num⟩

theorem h1408VPerm_zero : (h1408VPerm h1408Pt0).val = 704 := by
  refine rep_val_eq (g := h1408VPerm) rep_h1408V ?_ ?_
  exact (h1408BlockOK_parts.2 0 (by norm_num : 0 < 704)).1

end Cert

end CFSG.EvenSporadicStandard.HNRecog

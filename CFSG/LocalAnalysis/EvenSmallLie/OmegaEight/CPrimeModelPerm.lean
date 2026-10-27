module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelBasic
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelAut

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrimeModel

open Subgroup Matrix CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.EvenSmallLie.OmegaEight.CPrime (reflRows)

variable {ε : Eps}

@[expose] noncomputable def sig (ε : Eps) : Equiv.Perm (Fin (deg ε)) :=
  permOfArr (deg ε) (sigArr ε)

theorem sig_parts (ε : Eps) :
    isInvA (deg ε) (sigArr ε) (invCand (deg ε) (sigArr ε)) = true ∧
      eqA (deg ε) (compA (deg ε) (sigArr ε) (sigArr ε)) (idA (deg ε)) = true ∧
      (∀ y < 64, eqA (deg ε) (conjA (deg ε) (sigArr ε) (psiArr ε y))
        (psiArr ε (bmulVec 6 6 (reflRows ε (n0 ε)) y)) = true) ∧
      ∀ k < 6, memU ε (conjA (deg ε) (sigArr ε) (uArr ε k)) = true := by
  have h := sigCheck_ok ε
  simp only [sigCheck, Bool.and_eq_true, allLt_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rep_sig : Rep (deg ε) (sigArr ε) (sig ε) ∧
    Rep (deg ε) (invCand (deg ε) (sigArr ε)) (sig ε)⁻¹ :=
  rep_permOfArr (sig_parts ε).1

theorem sig_mul_self : sig ε * sig ε = 1 :=
  eq_of_eqA (rep_compA rep_sig.1 rep_sig.1) rep_idA (sig_parts ε).2.1

theorem sig_act (v : V6) :
    sig ε * psiM ε v * (sig ε)⁻¹ = psiM ε (toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v) := by
  have h := (sig_parts ε).2.2.1 (vecBits v) (vecBits_lt v)
  rw [← vecBits_mulVec] at h
  exact eq_of_eqA (rep_compA (rep_compA rep_sig.1 (rep_psiM v).1) rep_sig.2) (rep_psiM _).1 h

theorem sig_conj_uM (k : Fin 6) : sig ε * uM ε k * (sig ε)⁻¹ ∈ UQm ε :=
  (memU_iff (rep_compA (rep_compA rep_sig.1 (rep_uM k).1) rep_sig.2)).1
    ((sig_parts ε).2.2.2 k k.2)

theorem sig_conj_mem_U {x : Equiv.Perm (Fin (deg ε))} (hx : x ∈ UQm ε) :
    sig ε * x * (sig ε)⁻¹ ∈ UQm ε := by
  have hle : UQm ε ≤ (UQm ε).comap (MulAut.conj (sig ε)).toMonoidHom := by
    calc UQm ε = closure (Set.range (fun j : Fin 6 => psiM ε (Pi.single j 1)) ∪
          Set.range (uM ε)) := UQm_eq
      _ ≤ _ := by
        rw [closure_le]
        rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
        · rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            sig_act]
          exact psiM_mem_U _
        · rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact sig_conj_uM k
  have := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

section Plus

open OmegaEight (gen omegaT autT stab0 res0)

theorem mem_omegaT_iff {g : Array ℕ} {G : Equiv.Perm (Fin 360)} (hG : Rep 360 g G) :
    G ∈ omegaT ↔ memOmPlus g = true :=
  (ofArrays_mem_iff (by norm_num) OmegaEight.omegaChain_ok.1 hG).symm

theorem coset_parts :
    (∀ i < 6, isInvA 360 (wArr i) (invCand 360 (wArr i)) = true ∧ memA .plus (wArr i) = true) ∧
    (∀ i < 6, ∀ j < 6, i = j ∨ memOmPlus (compA 360 (wArr j) (invCand 360 (wArr i))) = false) ∧
    memOmPlus (compA 360 (wArr 2) (wArr 2)) = false ∧
    memOmPlus (compA 360 (wArr 4) (wArr 4)) = false ∧
    (∀ j < 4, 120 ≤ (wArr (j + 2))[0]!) ∧
    (∀ p < 360, ((OmegaEight.genArrs[9]!)[p]! < 120 ↔ p < 120)) ∧
    eqA 360 (compA 360 OmegaEight.genArrs[9]! OmegaEight.genArrs[9]!) (idA 360) = true ∧
    eqA 360 (OmegaEight.conjArr (wArr 2) (wArr 3)) OmegaEight.genArrs[9]! = true ∧
    eqA 360 (OmegaEight.conjArr (wArr 4) (wArr 5)) OmegaEight.genArrs[9]! = true := by
  have h := cosetCheck_ok
  simp only [cosetCheck, Bool.and_eq_true, allLt_iff, Bool.not_eq_true', decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq, decide_eq_decide] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

@[expose] noncomputable def wPerm (j : ℕ) : Equiv.Perm (Fin 360) := permOfArr 360 (wArr j)

theorem rep_wPerm {j : ℕ} (hj : j < 6) :
    Rep 360 (wArr j) (wPerm j) ∧ Rep 360 (invCand 360 (wArr j)) (wPerm j)⁻¹ :=
  rep_permOfArr (coset_parts.1 j hj).1

theorem wPerm_mem {j : ℕ} (hj : j < 6) : wPerm j ∈ autT := by
  rw [← AT_plus]
  exact (memA_iff (ε := .plus) (rep_wPerm hj).1).1 (coset_parts.1 j hj).2

theorem exists_coset_plus {x : Equiv.Perm (Fin 360)} (hx : x ∈ autT) :
    ∃ j < 6, x * (wPerm j)⁻¹ ∈ omegaT := by
  obtain ⟨j, hj⟩ := exists_coset_rep (H := omegaT) (K := autT) (m := 6) (fun j => wPerm j)
    (fun j => wPerm_mem j.2) OmegaEight.omegaT_le_autT OmegaEight.card_autT_eq
    (fun i j h => by
      by_contra hij
      have hne : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
      rcases coset_parts.2.1 i i.2 j j.2 with e | e
      · exact hne e
      · rw [(mem_omegaT_iff (rep_compA (rep_wPerm j.2).1 (rep_wPerm i.2).2)).1 h] at e
        exact absurd e (by decide)) hx
  exact ⟨j, j.2, hj⟩

end Plus

end CFSG.EvenSmallLie.OmegaEight.CPrimeModel

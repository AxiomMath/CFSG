module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldFrame
public import CFSG.Sporadic.Recognition.PresentedWords
public import Certificates.Data.ChengHeldPres

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld CFSG.OddStandard.ChengHeld.M1b
open CFSG.Sporadic.Recognition.PresentedWords

section Rels

variable {E : Type*} [Group E]

attribute [local simp] evalE evalE_pw evalE_cj evalE_cm vt vpi vtau vmu vlam vze vxi

theorem rels4_of_frame4 (α : ℕ) (σ : ℕ → E)
    (h : Frame4 α (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6)) :
    ∀ e ∈ frame4Rels α, evalE σ e.1 = evalE σ e.2 := by
  intro e he
  simp only [frame4Rels, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using h.t4
  · simpa using h.pi2
  · simpa using h.tau4
  · simpa using h.mu2
  · simpa using h.lam2
  · simpa using h.ze2
  · simpa using h.xi2
  · simpa using h.tau_sq
  · simpa using h.pi_tau
  · simpa using h.pi_mu
  · simpa using h.pi_lam
  · simpa using h.pi_ze
  · simpa using h.pi_mulam
  · simpa using h.pi_xi
  · simpa using h.tau_xi
  · simpa using h.tau_lam
  · simpa using h.tau_ze
  · simpa using h.tau_mu
  · simpa using h.mu_lam
  · simpa using h.ze_xi
  · simpa using h.mu_xi
  · simpa using h.mu_ze
  · simpa using h.lam_xi
  · simpa using h.lam_ze

theorem rels2_of_frame2 (σ : ℕ → E)
    (h : Frame2 (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6)) :
    ∀ e ∈ frame2Rels, evalE σ e.1 = evalE σ e.2 := by
  obtain ⟨⟨hq, hpi, htau, hmu, hlam, hze, hxi⟩, hqc, hR1, hR2, hmx, hlx, hmz, hlz⟩ := h
  intro e he
  simp only [frame2Rels, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using hq
  · simpa using hpi
  · simpa using htau
  · simpa using hmu
  · simpa using hlam
  · simpa using hze
  · simpa using hxi
  · simpa using hqc (σ 1) (by simp)
  · simpa using hqc (σ 2) (by simp)
  · simpa using hqc (σ 3) (by simp)
  · simpa using hqc (σ 4) (by simp)
  · simpa using hqc (σ 5) (by simp)
  · simpa using hqc (σ 6) (by simp)
  · simpa using hR1 (σ 1) (by simp) (σ 2) (by simp)
  · simpa using hR1 (σ 1) (by simp) (σ 3) (by simp)
  · simpa using hR1 (σ 1) (by simp) (σ 4) (by simp)
  · simpa using hR1 (σ 2) (by simp) (σ 3) (by simp)
  · simpa using hR1 (σ 2) (by simp) (σ 4) (by simp)
  · simpa using hR1 (σ 3) (by simp) (σ 4) (by simp)
  · simpa using hR2 (σ 1) (by simp) (σ 5) (by simp)
  · simpa using hR2 (σ 1) (by simp) (σ 6) (by simp)
  · simpa using hR2 (σ 2) (by simp) (σ 5) (by simp)
  · simpa using hR2 (σ 2) (by simp) (σ 6) (by simp)
  · simpa using hR2 (σ 5) (by simp) (σ 6) (by simp)
  · simpa using hmx
  · simpa using hlx
  · simpa using hmz
  · simpa [mul_assoc] using hlz

@[expose] def kind0 : Kind → ℕ
  | .field => 0
  | .graph => 1
  | .unitary => 2

theorem rels_of_act (α : ℕ) (hα : α ≤ 1) (k : Kind) (σ : ℕ → E) (y : E)
    (h : k.Act α (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) y) :
    ∀ e ∈ actRels α (kind0 k), cj (σ e.1) y = evalE σ e.2 := by
  intro e he
  interval_cases α <;> cases k <;>
    simp (config := {decide := true}) only [Kind.Act, actRels, List.mem_cons,
      List.mem_nil_iff, or_false, ite_true, ite_false] at h he <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using ‹_›

theorem rels_of_act2 (k : Kind) (σ : ℕ → E) (y : E)
    (h : k.Act2 (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) y) :
    ∀ e ∈ act2Rels (kind0 k), cj (σ e.1) y = evalE σ e.2 := by
  intro e he
  cases k <;>
    simp (config := {decide := true}) only [Kind.Act2, act2Rels, List.mem_cons,
      List.mem_nil_iff, or_false, ite_true, ite_false] at h he <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using ‹_›

end Rels

section Words

variable {E : Type*} [Group E]

@[expose] def tmLt (n : ℕ) : Tm → Prop
  | .var i => i < n
  | .one => True
  | .mul a b => tmLt n a ∧ tmLt n b
  | .inv a => tmLt n a

theorem tmLt_pw {n : ℕ} {a : Tm} (ha : tmLt n a) (k : ℕ) : tmLt n (Tm.pw a k) := by
  induction k with
  | zero => simp [Tm.pw, tmLt]
  | succ k ih => simp only [Tm.pw, tmLt]; exact ⟨ih, ha⟩

theorem wprod_invRev {n : ℕ} (x : Fin n → E) (w : List (Fin n × Bool)) :
    wprod x (FreeGroup.invRev w) = (wprod x w)⁻¹ := by
  induction w with
  | nil => simp [FreeGroup.invRev_empty]
  | cons l w ih =>
    rw [FreeGroup.invRev_cons, wprod_append, ih, wprod_cons]
    cases l with
    | mk i b =>
      cases b <;> simp [FreeGroup.invRev, wprod, mul_inv_rev]

theorem wprod_toWord (σ : ℕ → E) {τ : Tm} (hτ : tmLt 7 τ) :
    wprod (fun i : Fin 7 => σ i.val) τ.toWord = evalE σ τ := by
  induction τ with
  | var i =>
    have hi : i < 7 := hτ
    simp [Tm.toWord, wprod, evalE, Fin.ofNat, Nat.mod_eq_of_lt hi]
  | one => simp [Tm.toWord, evalE]
  | mul a b iha ihb => rw [Tm.toWord, wprod_append, iha hτ.1, ihb hτ.2]; rfl
  | inv a ih => rw [Tm.toWord, wprod_invRev, ih (by simpa [tmLt] using hτ)]; rfl

theorem tmLt_frame4Rels (α : ℕ) : ∀ e ∈ frame4Rels α, tmLt 7 e.1 ∧ tmLt 7 e.2 := by
  have hv : ∀ i k : ℕ, i < 7 → tmLt 7 (Tm.pw (Tm.var i) k) :=
    fun i k hi => tmLt_pw (a := Tm.var i) (by simpa [tmLt] using hi) k
  intro e he
  simp only [frame4Rels, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [tmLt, Tm.cj, Tm.cm, vt, vpi, vtau, vmu, vlam, vze, vxi, hv]

theorem tmLt_frame2Rels : ∀ e ∈ frame2Rels, tmLt 7 e.1 ∧ tmLt 7 e.2 := by
  have hv : ∀ i k : ℕ, i < 7 → tmLt 7 (Tm.pw (Tm.var i) k) :=
    fun i k hi => tmLt_pw (a := Tm.var i) (by simpa [tmLt] using hi) k
  intro e he
  simp only [frame2Rels, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [tmLt, Tm.cm, vt, vpi, vtau, vmu, vlam, vze, vxi, hv]

@[expose] def natFam (x : Fin 7 → E) (i : ℕ) : E := x (Fin.ofNat 7 i)

omit [Group E] in
theorem natFam_fin (x : Fin 7 → E) (j : Fin 7) : natFam x j.val = x j := by
  simp only [natFam, Fin.ofNat]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt j.2)

theorem wprod_relWords4 (α : ℕ) (x : Fin 7 → E)
    (h : Frame4 α (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)) :
    ∀ w ∈ relWords4 α, wprod x w = 1 := by
  intro w hw
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
  have hx : x = fun j : Fin 7 => natFam x j.val := funext fun j => (natFam_fin x j).symm
  have hrel := rels4_of_frame4 α (natFam x) h e he
  obtain ⟨h1, h2⟩ := tmLt_frame4Rels α e he
  rw [hx, wprod_append, wprod_invRev, wprod_toWord _ h1, wprod_toWord _ h2, hrel, mul_inv_cancel]

theorem wprod_relWords2 (x : Fin 7 → E)
    (h : Frame2 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)) :
    ∀ w ∈ relWords2, wprod x w = 1 := by
  intro w hw
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
  have hx : x = fun j : Fin 7 => natFam x j.val := funext fun j => (natFam_fin x j).symm
  have hrel := rels2_of_frame2 (natFam x) h e he
  obtain ⟨h1, h2⟩ := tmLt_frame2Rels e he
  rw [hx, wprod_append, wprod_invRev, wprod_toWord _ h1, wprod_toWord _ h2, hrel, mul_inv_cancel]

end Words

end CFSG.OddStandard.ChengHeld.Model

module

public import Certificates.Data.Kernel.Misc.T84QuadK
public import Certificates.Data.T84Quad
public import CFSG.Certificates.Kernel.Misc.GL4EltSound

public section

namespace CFSG.KC.Misc.T84Q

open Matrix CFSG.KC.Misc.GL4
open Certificates.A5GL42 (Mat4 Vec4 ofCode vecOfCode)

theorem andQ_eq (a b : Bool) : andQ a b = (a && b) := by cases a <;> rfl

theorem false_of_notQ {b : Bool} (h : notQ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem allNQ_iff (m : ℕ) (f : ℕ → Bool) : allNQ m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ m ih =>
    have e : allNQ (m + 1) f = andQ (f m) (allNQ m f) := rfl
    rw [e, andQ_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem allLQ_iff (L : List ℕ) (f : ℕ → Bool) : allLQ L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [allLQ]
  | cons x L ih =>
    have e : allLQ (x :: L) f = andQ (f x) (allLQ L f) := rfl
    rw [e, andQ_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem anyLQ_iff (L : List ℕ) (f : ℕ → Bool) : anyLQ L f = true ↔ ∃ x ∈ L, f x = true := by
  induction L with
  | nil => simp [anyLQ]
  | cons x L ih =>
    have e : anyLQ (x :: L) f = (f x || anyLQ L f) := by
      change Bool.rec (motive := fun _ => Bool) (anyLQ L f) true (f x) = _
      cases f x <;> rfl
    rw [e, Bool.or_eq_true, ih]
    simp

theorem beq_iff {c u w : ℕ} (hc : c < 65536) (hu : u < 16) (hw : w < 16) :
    Nat.beq (mul4F c (colC u)) (colC w) = true ↔ ofCode c *ᵥ vecOfCode u = vecOfCode w := by
  rw [Nat.beq_eq]
  constructor
  · intro h
    apply colM_inj
    rw [← mul_colM, ← colC_ofCode u hu, ← mul4F_ofCode, h, colC_ofCode w hw]
  · intro h
    apply ofCode_inj (mul4F_lt _ _) (colC_lt w hw)
    rw [mul4F_ofCode, colC_ofCode u hu, mul_colM, h, colC_ofCode w hw]

theorem vecOfCode_zero : vecOfCode 0 = 0 := by
  funext i
  simp [vecOfCode]

theorem check_of {L : List ℕ} (hL : ∀ c ∈ L, c ∈ Certificates.Asc82NormA6.codesS0)
    (hb : q442350B L = true) (ht : q442350T L = true) (hf : q442350F L = true) :
    Certificates.T84Quad.check () = true := by
  have hlt : ∀ c ∈ L, c < 65536 := fun c hc => by
    have h := (allLQ_iff _ _).1 hb c hc
    rwa [Nat.blt_eq] at h
  have hmem : ∀ c ∈ L, ofCode c ∈ Certificates.T84Quad.matL := fun c hc => by
    rw [Certificates.T84Quad.mem_matL]
    unfold Certificates.T84Quad.matsS0
    exact List.mem_toFinset.2 (List.mem_map_of_mem (hL c hc))
  unfold Certificates.T84Quad.check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun v _ hv => ?_, fun w _ hw => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := vec_surj v
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hv vecOfCode_zero
    obtain ⟨c, hc, e⟩ := (anyLQ_iff _ _).1 ((allNQ_iff _ _).1 ht (u - 1) (by change u - 1 < 15; omega))
    have e1 : Nat.succ (u - 1) = u := by omega
    rw [e1] at e
    exact ⟨ofCode c, hmem c hc, (beq_iff (hlt c hc) (by decide) hu).1 e⟩
  · obtain ⟨u, hu, rfl⟩ := vec_surj w
    rcases (by omega : u = 0 ∨ u = 1 ∨ 2 ≤ u) with rfl | rfl | h2
    · exact Or.inl vecOfCode_zero
    · exact Or.inr rfl
    · exfalso
      obtain ⟨c, hc, e⟩ := (anyLQ_iff _ _).1 ((allNQ_iff _ _).1 hf (u - 2) (by change u - 2 < 14; omega))
      have e2 : Nat.succ (Nat.succ (u - 2)) = u := by omega
      rw [e2, andQ_eq, Bool.and_eq_true] at e
      have hfix := hw (ofCode c) (hmem c hc) ((beq_iff (hlt c hc) (by decide) (by decide)).1 e.1)
      have hne := false_of_notQ e.2
      rw [(beq_iff (hlt c hc) hu hu).2 hfix] at hne
      exact absurd hne (by decide)

end CFSG.KC.Misc.T84Q

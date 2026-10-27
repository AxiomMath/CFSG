module

public import Certificates.Data.Kernel.Spor.Fi24G2d
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound

public section

namespace CFSG.KC.Fi24G2dS

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb CFSG.KC.Fi24G2d

theorem fixLOK_spec {FL : ℕ → ℕ} {TG : ℕ → ℕ → ℕ} {u : List ℕ} {n m : ℕ}
    (h : fixLOK FL TG u n m = true) (hm : m ≤ 1024) :
    ∀ j < m, FL j < n ∧ walk TG u (FL j) = FL j ∧ (j + 1 < m → FL j < FL (j + 1)) := by
  intro j hj
  have h1 := Fi24FixS.allBelow_spec h (by omega) j hj
  have e : listStep FL TG u n m j = (andB (Nat.blt (FL j) n) (andB (Nat.beq (walk TG u (FL j)) (FL j))
      (orB (Nat.ble m (Nat.succ j)) (Nat.blt (FL j) (FL (Nat.succ j)))))) := by
    unfold listStep letB
    cases FL j <;> rfl
  rw [e] at h1
  unfold andB orB at h1
  cases h2 : Nat.blt (FL j) n <;> rw [h2] at h1
  · exact absurd h1 Bool.false_ne_true
  cases h3 : Nat.beq (walk TG u (FL j)) (FL j) <;> rw [h3] at h1
  · exact absurd h1 Bool.false_ne_true
  refine ⟨(by simpa using h2), Nat.eq_of_beq_eq_true h3, fun hj1 => ?_⟩
  have h4 : Nat.ble m (Nat.succ j) = false := by
    rw [Bool.eq_false_iff]
    intro h5
    have := Nat.le_of_ble_eq_true h5
    omega
  rw [h4] at h1
  simpa using h1

theorem card_filter_chunks (p : ℕ → Prop) [DecidablePred p] (B : ℕ) :
    ∀ k r, ((Finset.range (B * k + r)).filter p).card =
      ∑ c ∈ Finset.range k, ((Finset.range B).filter fun t => p (B * c + t)).card +
        ((Finset.range r).filter fun t => p (B * k + t)).card := by
  intro k
  induction k with
  | zero =>
    intro r
    simp
  | succ k ih =>
    intro r
    have e : B * (k + 1) + r = B * k + (B + r) := by rw [Nat.mul_succ, Nat.add_assoc]
    rw [e, ih (B + r), Finset.sum_range_succ, add_assoc]
    congr 1
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    have e2 : B * k + (B + t) = B * (k + 1) + t := by rw [Nat.mul_succ, Nat.add_assoc]
    rw [e2]

theorem cntFix_idN (TG : ℕ → ℕ → ℕ) (w : List ℕ) (lo m hi : ℕ) (hm : m ≤ 64 * hi) :
    cntFix idN TG [] w lo m hi =
      ((Finset.range m).filter fun t => walk TG w (lo + t) = lo + t).card :=
  Fi24FixS.cntFix_eq idN TG [] w lo m hi hm

theorem card_fix_of_chunks (TG : ℕ → ℕ → ℕ) (w K : List ℕ)
    (h : ∀ c < 74, Nat.beq (cntFix idN TG [] w (4096 * c) 4096 64) (K.getD c 0) = true)
    (hl : Nat.beq (cntFix idN TG [] w 303104 3832 64) (K.getD 74 0) = true) :
    ((Finset.range 306936).filter fun r => walk TG w r = r).card =
      ∑ c ∈ Finset.range 75, K.getD c 0 := by
  have e : (306936 : ℕ) = 4096 * 74 + 3832 := rfl
  rw [Finset.sum_range_succ (fun c => K.getD c 0) 74, e,
    card_filter_chunks (fun r => walk TG w r = r) 4096 74 3832]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c hc => ?_) ?_
  · rw [← Nat.eq_of_beq_eq_true (h c (Finset.mem_range.1 hc)), cntFix_idN TG w _ 4096 64 (by omega)]
  · rw [← Nat.eq_of_beq_eq_true hl, cntFix_idN TG w _ 3832 64 (by omega)]

theorem fix_iff_of_list {TG : ℕ → ℕ → ℕ} {u : List ℕ} {FL : ℕ → ℕ} {n m : ℕ}
    (hL : ∀ j < m, FL j < n ∧ walk TG u (FL j) = FL j ∧ (j + 1 < m → FL j < FL (j + 1)))
    (hc : ((Finset.range n).filter fun r => walk TG u r = r).card = m) :
    ∀ r < n, walk TG u r = r ↔ ∃ j < m, FL j = r := by
  have mono : ∀ i j, i < j → j < m → FL i < FL j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have h1 := (hL j (by omega)).2.2 (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact (ih h (by omega)).trans h1
      · rw [h]
        exact h1
  have inj : Set.InjOn FL (Finset.range m : Set ℕ) := by
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd e (mono i j h hj).ne
    · exact h
    · exact absurd e (mono j i h hi).ne'
  have hsub : (Finset.range m).image FL ⊆ (Finset.range n).filter fun r => walk TG u r = r := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    have hj' := hL j (Finset.mem_range.1 hj)
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj'.1, hj'.2.1⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc, Finset.card_image_of_injOn inj,
    Finset.card_range])
  intro r hr
  constructor
  · intro hf
    have : r ∈ (Finset.range m).image FL := by
      rw [heq]
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hr, hf⟩
    obtain ⟨j, hj, e⟩ := Finset.mem_image.1 this
    exact ⟨j, Finset.mem_range.1 hj, e⟩
  · rintro ⟨j, hj, rfl⟩
    exact (hL j hj).2.1

end CFSG.KC.Fi24G2dS

end

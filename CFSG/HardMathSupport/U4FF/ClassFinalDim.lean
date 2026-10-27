module

public import CFSG.HardMathSupport.U4FF.ClassComb

public section

namespace CFSG.HardMathSupport.U4FF

namespace Lbl

variable {n : ℕ}

private lemma locM_eq_one_iff (x y z : Bool) :
    locM x y z = 1 ↔ x = false ∧ y = false ∧ z = false := by
  cases x <;> cases y <;> cases z <;> decide

private lemma locM_eq_four_iff (x y z : Bool) :
    locM x y z = 4 ↔ y = false ∧ ((x = true ∧ z = false) ∨ (x = false ∧ z = true)) := by
  cases x <;> cases y <;> cases z <;> decide

private lemma locM_eq_six_iff (x y z : Bool) :
    locM x y z = 6 ↔ x = false ∧ y = true ∧ z = false := by
  cases x <;> cases y <;> cases z <;> decide

private lemma locM_dvd_four (x y z : Bool) (h : locM x y z ∣ 4) :
    locM x y z = 1 ∨ locM x y z = 4 := by
  cases x <;> cases y <;> cases z <;> revert h <;> decide

private lemma locM_dvd_six (x y z : Bool) (h : locM x y z ∣ 6) :
    locM x y z = 1 ∨ locM x y z = 6 := by
  cases x <;> cases y <;> cases z <;> revert h <;> decide

theorem dim_eq_four_of_singleN {l : Lbl n} (h : l.SingleN) : l.dim = 4 := by
  unfold Lbl.SingleN at h
  obtain ⟨i₀, hz, hb, hac⟩ := h
  have h4 : locM (l.a i₀) (l.b i₀) (l.c i₀) = 4 := (locM_eq_four_iff _ _ _).2 ⟨hb, hac⟩
  have key : ∏ i, locM (l.a i) (l.b i) (l.c i) = locM (l.a i₀) (l.b i₀) (l.c i₀) := by
    apply Finset.prod_eq_single i₀
    · intro i _ hi
      exact (locM_eq_one_iff _ _ _).2 (hz i hi)
    · intro h'
      exact absurd (Finset.mem_univ i₀) h'
  unfold Lbl.dim
  exact key.trans h4

theorem dim_eq_six_of_singleO {l : Lbl n} (h : l.SingleO) : l.dim = 6 := by
  unfold Lbl.SingleO at h
  obtain ⟨i₀, hz, ha, hb, hc⟩ := h
  have h6 : locM (l.a i₀) (l.b i₀) (l.c i₀) = 6 := (locM_eq_six_iff _ _ _).2 ⟨ha, hb, hc⟩
  have key : ∏ i, locM (l.a i) (l.b i) (l.c i) = locM (l.a i₀) (l.b i₀) (l.c i₀) := by
    apply Finset.prod_eq_single i₀
    · intro i _ hi
      exact (locM_eq_one_iff _ _ _).2 (hz i hi)
    · intro h'
      exact absurd (Finset.mem_univ i₀) h'
  unfold Lbl.dim
  exact key.trans h6

theorem singleN_of_dim_eq_four {l : Lbl n} (h : l.dim = 4) : l.SingleN := by
  unfold Lbl.dim at h
  have hex : ∃ i₀, locM (l.a i₀) (l.b i₀) (l.c i₀) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact absurd (h.symm.trans (Finset.prod_eq_one (fun i _ => hcon i))) (by decide)
  obtain ⟨i₀, hi₀⟩ := hex
  have hdvd : locM (l.a i₀) (l.b i₀) (l.c i₀) ∣ ∏ i, locM (l.a i) (l.b i) (l.c i) :=
    Finset.dvd_prod_of_mem (fun i => locM (l.a i) (l.b i) (l.c i)) (Finset.mem_univ i₀)
  rw [h] at hdvd
  have h4 : locM (l.a i₀) (l.b i₀) (l.c i₀) = 4 := by
    rcases locM_dvd_four _ _ _ hdvd with h1 | h1
    · exact absurd h1 hi₀
    · exact h1
  have hprod : locM (l.a i₀) (l.b i₀) (l.c i₀) *
      (∏ i ∈ Finset.univ.erase i₀, locM (l.a i) (l.b i) (l.c i)) =
      ∏ i, locM (l.a i) (l.b i) (l.c i) :=
    Finset.mul_prod_erase Finset.univ (fun i => locM (l.a i) (l.b i) (l.c i)) (Finset.mem_univ i₀)
  rw [h4, h] at hprod
  have hR : ∏ i ∈ Finset.univ.erase i₀, locM (l.a i) (l.b i) (l.c i) = 1 := by
    omega
  have hone : ∀ i, i ≠ i₀ → locM (l.a i) (l.b i) (l.c i) = 1 := by
    intro i hi
    have hdvd' : locM (l.a i) (l.b i) (l.c i) ∣
        ∏ j ∈ Finset.univ.erase i₀, locM (l.a j) (l.b j) (l.c j) :=
      Finset.dvd_prod_of_mem (fun j => locM (l.a j) (l.b j) (l.c j))
        (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
    rw [hR] at hdvd'
    exact Nat.dvd_one.1 hdvd'
  unfold Lbl.SingleN
  exact ⟨i₀, fun i hi => (locM_eq_one_iff _ _ _).1 (hone i hi), (locM_eq_four_iff _ _ _).1 h4⟩

theorem singleO_of_dim_eq_six {l : Lbl n} (h : l.dim = 6) : l.SingleO := by
  unfold Lbl.dim at h
  have hex : ∃ i₀, locM (l.a i₀) (l.b i₀) (l.c i₀) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact absurd (h.symm.trans (Finset.prod_eq_one (fun i _ => hcon i))) (by decide)
  obtain ⟨i₀, hi₀⟩ := hex
  have hdvd : locM (l.a i₀) (l.b i₀) (l.c i₀) ∣ ∏ i, locM (l.a i) (l.b i) (l.c i) :=
    Finset.dvd_prod_of_mem (fun i => locM (l.a i) (l.b i) (l.c i)) (Finset.mem_univ i₀)
  rw [h] at hdvd
  have h6 : locM (l.a i₀) (l.b i₀) (l.c i₀) = 6 := by
    rcases locM_dvd_six _ _ _ hdvd with h1 | h1
    · exact absurd h1 hi₀
    · exact h1
  have hprod : locM (l.a i₀) (l.b i₀) (l.c i₀) *
      (∏ i ∈ Finset.univ.erase i₀, locM (l.a i) (l.b i) (l.c i)) =
      ∏ i, locM (l.a i) (l.b i) (l.c i) :=
    Finset.mul_prod_erase Finset.univ (fun i => locM (l.a i) (l.b i) (l.c i)) (Finset.mem_univ i₀)
  rw [h6, h] at hprod
  have hR : ∏ i ∈ Finset.univ.erase i₀, locM (l.a i) (l.b i) (l.c i) = 1 := by
    omega
  have hone : ∀ i, i ≠ i₀ → locM (l.a i) (l.b i) (l.c i) = 1 := by
    intro i hi
    have hdvd' : locM (l.a i) (l.b i) (l.c i) ∣
        ∏ j ∈ Finset.univ.erase i₀, locM (l.a j) (l.b j) (l.c j) :=
      Finset.dvd_prod_of_mem (fun j => locM (l.a j) (l.b j) (l.c j))
        (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
    rw [hR] at hdvd'
    exact Nat.dvd_one.1 hdvd'
  unfold Lbl.SingleO
  exact ⟨i₀, fun i hi => (locM_eq_one_iff _ _ _).1 (hone i hi), (locM_eq_six_iff _ _ _).1 h6⟩

end Lbl

end CFSG.HardMathSupport.U4FF

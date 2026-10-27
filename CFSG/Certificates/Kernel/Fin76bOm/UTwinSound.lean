module

public import Certificates.Data.Kernel.Fin76bOm.UTwin

public section

namespace CFSG.KC.Fin76bU

open CFSG.EvenSporadicStandard.Fin76b

theorem fldU_lt (w x i : Nat) : fldU w x i < 2 ^ w := Nat.mod_lt _ (by positivity)

theorem mU_lt (P a b : Nat) : mU P a b < 32 := fldU_lt 5 P _

theorem phU_lt (x a : Nat) : (phU x a).1 < 8 ∧ (phU x a).2 < 32 := by
  have h : fldU 8 x a < 256 := fldU_lt 8 x a
  simp only [phU]
  omega

theorem peqU_iff {m : Nat → Nat → Nat} {tI : Nat} {x y : Nat × Nat} :
    peqU m tI x y = true ↔ UPeq m tI x y := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp [peqU, UPeq, Prod.ext_iff]

theorem verU_spec {m : Nat → Nat → Nat} {tI : Nat} {u : Nat × Nat} {x : Nat}
    (h : verU m tI u x = true) : UWitness m tI u (phU x) := by
  simp only [verU, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun a _ => phU_lt x a, fun a ha b hb => peqU_iff.1 (h1 a ha b hb),
    fun a ha b hb hab => ?_, fun a ha => peqU_iff.1 (h3 a ha), fun a ha hu => ?_⟩
  · have h5 := h2 a ha b hb
    rw [peqU_iff.2 hab] at h5
    simpa using h5
  · have h5 := h4 a ha
    rw [peqU_iff.2 hu] at h5
    simp at h5

theorem allU_spec {m : Nat → Nat → Nat} {tI : Nat} :
    ∀ (ws : List Nat) (p : Nat), allU m tI ws p = true → ∀ j < ws.length,
      condU m tI ((p + j) / 32) ((p + j) % 32) = true →
      verU m tI ((p + j) / 32, (p + j) % 32) (ws.getD j 0) = true
  | [], _, _, j, hj, _ => absurd hj (by simp)
  | x :: ws, p, h, j, hj, hc => by
    have h' : ((!condU m tI (p / 32) (p % 32) || verU m tI (p / 32, p % 32) x) &&
        allU m tI ws (p + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.getD_cons_zero] at hc ⊢
      rw [hc] at h'
      simpa using h'.1
    | succ j =>
      have e : p + (j + 1) = p + 1 + j := by omega
      rw [e] at hc ⊢
      rw [List.getD_cons_succ]
      exact allU_spec ws (p + 1) h'.2 j (by simpa using hj) hc

theorem globU_spec {m : Nat → Nat → Nat} {tI : Nat} (h : globU m tI = true) :
    tI < 32 ∧ tI ≠ 0 ∧ m tI tI = 0 ∧ ∀ a < 32, (∀ b < 32, m a b = m b a) → a = 0 ∨ a = tI := by
  simp only [globU, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨of_decide_eq_true h1, by simpa using h2, by simpa using h3, fun a ha hc => ?_⟩
  have h5 := List.all_eq_true.1 h4 a (List.mem_range.2 ha)
  have hcen : ((List.range 32).all fun b => m a b == m b a) = true := by
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    exact hc
  simpa [hcen] using h5

theorem uChkU_spec {P tI : Nat} {WS : List Nat} (h : uChkU P tI WS = true) :
    UTableSpec (mU P) tI := by
  simp only [uChkU, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hg, hlen⟩, hall⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := globU_spec hg
  refine ⟨h1, h2, h3, h4, fun i hi k hk g1 g2 g3 =>
    ⟨phU (WS.getD (32 * i + k) 0), verU_spec ?_⟩⟩
  have hp : 32 * i + k < WS.length := by omega
  have e1 : (0 + (32 * i + k)) / 32 = i := by omega
  have e2 : (0 + (32 * i + k)) % 32 = k := by omega
  have q1 : peqU (mU P) tI (dMul i i, mU P k k) (0, 0) = true := peqU_iff.2 g1
  have q2 : peqU (mU P) tI (i, k) (0, 0) = false := by
    cases hh : peqU (mU P) tI (i, k) (0, 0)
    · rfl
    · exact absurd (peqU_iff.1 hh) g2
  have q3 : peqU (mU P) tI (i, k) (0, tI) = false := by
    cases hh : peqU (mU P) tI (i, k) (0, tI)
    · rfl
    · exact absurd (peqU_iff.1 hh) g3
  have hc : condU (mU P) tI ((0 + (32 * i + k)) / 32) ((0 + (32 * i + k)) % 32) = true := by
    rw [e1, e2]
    simp [condU, q1, q2, q3]
  have h5 := allU_spec WS 0 hall _ hp hc
  rw [e1, e2] at h5
  exact h5

end CFSG.KC.Fin76bU

end

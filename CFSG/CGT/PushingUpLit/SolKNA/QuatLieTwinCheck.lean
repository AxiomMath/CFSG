module

public import CFSG.GH74.KGroups.NativeChecks2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks

variable {n : ℕ}

@[expose] def twinCheckA (n : ℕ) (LA : List (Array ℕ)) (t : Array ℕ) : Bool :=
  let C := LA.filter fun g => eqA n (compA n g t) (compA n t g)
  C.all fun a => !eqA n (compA n a a) t ||
    (C.filter fun b => isInvolA n (compA n a b) && !eqA n (compA n a b) t).any fun b =>
      C.any fun g => eqA n (compA n b g) (compA n g a)

@[expose] def invCoverCheckA (n : ℕ) (LA ts : List (Array ℕ)) : Bool :=
  LA.all fun u => !isInvolA n u ||
    ts.any fun t => LA.any fun g => eqA n (compA n g t) (compA n u g)

theorem heq_toA (x y : Equiv.Perm (Fin n)) : eqA n (toA x) (toA y) = decide (x = y) :=
  eqA_eq_decide (rep_toA x) (rep_toA y)

theorem hceq_toA (x y z w : Equiv.Perm (Fin n)) :
    eqA n (compA n (toA x) (toA y)) (compA n (toA z) (toA w)) = decide (x * y = z * w) := by
  rw [toA_mul, toA_mul, heq_toA]

section Sound

variable (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)

include hQ

theorem toA_mem_enumA {x : Equiv.Perm (Fin n)} (hx : x ∈ Q.originalSubgroup) :
    toA x ∈ enumA Q := by
  rw [enumA_eq]
  exact List.mem_map.2 ⟨x, (mem_elemsT Q hQ x).2 hx, rfl⟩

theorem exists_toA_of_mem_enumA {y : Array ℕ} (hy : y ∈ enumA Q) :
    ∃ x ∈ Q.originalSubgroup, toA x = y := by
  rw [enumA_eq] at hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  exact ⟨x, (mem_elemsT Q hQ x).1 hx, rfl⟩

theorem twinCheckA_sound {t : Equiv.Perm (Fin n)} (h : twinCheckA n (enumA Q) (toA t) = true) :
    ∀ a ∈ Q.originalSubgroup, a * t = t * a → a ^ 2 = t →
      ∃ g ∈ Q.originalSubgroup, g * t = t * g ∧ (a * (g * a * g⁻¹)) ^ 2 = 1 ∧
        a * (g * a * g⁻¹) ≠ 1 ∧ a * (g * a * g⁻¹) ≠ t := by
  intro a ha hat ha2
  unfold twinCheckA at h
  rw [List.all_eq_true] at h
  have haC : toA a ∈ List.filter
      (fun g => eqA n (compA n g (toA t)) (compA n (toA t) g)) (enumA Q) := by
    rw [List.mem_filter]
    exact ⟨toA_mem_enumA Q hQ ha, by rw [hceq_toA]; exact decide_eq_true hat⟩
  have h1 := h _ haC
  have hsq : eqA n (compA n (toA a) (toA a)) (toA t) = true := by
    rw [toA_mul, heq_toA]
    exact decide_eq_true (by rw [← pow_two]; exact ha2)
  rw [hsq] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  obtain ⟨b', hb', hbg⟩ := List.any_eq_true.1 h1
  rw [List.mem_filter] at hb'
  obtain ⟨hbC, hbinv⟩ := hb'
  obtain ⟨g', hg', hgg⟩ := List.any_eq_true.1 hbg
  rw [List.mem_filter] at hbC hg'
  obtain ⟨hbE, hbcomm⟩ := hbC
  obtain ⟨hgE, hgcomm⟩ := hg'
  obtain ⟨b, hbP, rfl⟩ := exists_toA_of_mem_enumA Q hQ hbE
  obtain ⟨g, hgP, rfl⟩ := exists_toA_of_mem_enumA Q hQ hgE
  rw [hceq_toA, decide_eq_true_eq] at hgcomm hgg
  rw [toA_mul, isInvolA_rep (rep_toA _), heq_toA] at hbinv
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    ne_eq] at hbinv
  obtain ⟨⟨hb2, hb1⟩, hbt⟩ := hbinv
  have hbconj : b = g * a * g⁻¹ := by rw [eq_mul_inv_iff_mul_eq]; exact hgg
  refine ⟨g, hgP, hgcomm, ?_, ?_, ?_⟩
  · rw [← hbconj]; exact hb2
  · rw [← hbconj]; exact hb1
  · rw [← hbconj]; exact hbt

theorem invCoverCheckA_sound {ts : List (Equiv.Perm (Fin n))}
    (h : invCoverCheckA n (enumA Q) (ts.map toA) = true) :
    ∀ u ∈ Q.originalSubgroup, u ^ 2 = 1 → u ≠ 1 →
      ∃ t ∈ ts, ∃ g ∈ Q.originalSubgroup, g * t * g⁻¹ = u := by
  intro u hu hu2 hu1
  unfold invCoverCheckA at h
  rw [List.all_eq_true] at h
  have h1 := h _ (toA_mem_enumA Q hQ hu)
  have hinv : isInvolA n (toA u) = true := by
    rw [isInvolA_rep (rep_toA u)]
    simpa using ⟨hu2, hu1⟩
  rw [hinv] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  obtain ⟨t', ht', hex⟩ := List.any_eq_true.1 h1
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht'
  obtain ⟨g', hg', hgg⟩ := List.any_eq_true.1 hex
  obtain ⟨g, hgP, rfl⟩ := exists_toA_of_mem_enumA Q hQ hg'
  rw [hceq_toA, decide_eq_true_eq] at hgg
  exact ⟨t, ht, g, hgP, by rw [mul_inv_eq_iff_eq_mul]; exact hgg⟩

end Sound

end CFSG.CGT.PushingUpLit.SolKNA

module

public import CFSG.GH74.KGroups.Checks

public section

namespace CFSG.GH74.KGroups

open CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] def invConjCheck (L : List (Equiv.Perm (Fin n))) (t : Equiv.Perm (Fin n)) : Bool :=
  L.all fun u => bif decide (u ^ 2 = 1) && decide (u ≠ 1) then
    L.any fun g => decide (g * t * g⁻¹ = u) else true

theorem invConjCheck_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {t : Equiv.Perm (Fin n)} (h : invConjCheck (elemsT Q) t = true) :
    ∀ u ∈ Q.originalSubgroup, u ^ 2 = 1 → u ≠ 1 →
      ∃ g ∈ Q.originalSubgroup, g * t * g⁻¹ = u := by
  intro u hu hu2 hu1
  have h1 := (bif_imp _ _).1 (List.all_eq_true.1 h u ((mem_elemsT Q hQ u).2 hu))
    (by simp [hu2, hu1])
  obtain ⟨g, hg, hgu⟩ := List.any_eq_true.1 h1
  exact ⟨g, (mem_elemsT Q hQ g).1 hg, by simpa using hgu⟩

@[expose] def powInPCheck (LA : List (Equiv.Perm (Fin n))) (QP : RawSchreierDatum n) (k : ℕ) :
    Bool :=
  LA.all fun g => bif decide (g ^ k = 1) then QP.sift g 0 else true

theorem powInPCheck_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) {k : ℕ} (h : powInPCheck (elemsT QA) QP k = true) :
    ∀ g ∈ QA.originalSubgroup, g ^ k = 1 → g ∈ QP.originalSubgroup := by
  intro g hg hgk
  have h1 := (bif_imp _ _).1 (List.all_eq_true.1 h g ((mem_elemsT QA hQA g).2 hg))
    (by simp [hgk])
  exact (mem_iff_sift QP hQP g).2 h1

@[expose] def leCheck (QS QP : RawSchreierDatum n) : Bool :=
  QS.original.toList.all fun g => QP.sift g 0

theorem leCheck_sound (QS QP : RawSchreierDatum n) (hQP : ValidSchreier QP)
    (h : leCheck QS QP = true) : QS.originalSubgroup ≤ QP.originalSubgroup := by
  rw [RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ QS.original.toList := hg
  exact (mem_iff_sift QP hQP g).2 (List.all_eq_true.1 h g hg')

@[expose] def commCheck (L : List (Equiv.Perm (Fin n))) : Bool :=
  L.all fun x => L.all fun y => decide (x * y = y * x)

theorem commCheck_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (h : commCheck (elemsT Q) = true) :
    ∀ x ∈ Q.originalSubgroup, ∀ y ∈ Q.originalSubgroup, x * y = y * x := by
  intro x hx y hy
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h x ((mem_elemsT Q hQ x).2 hx)) y
    ((mem_elemsT Q hQ y).2 hy)
  simpa using h1

@[expose] def centralIn (L : List (Equiv.Perm (Fin n))) (a : Equiv.Perm (Fin n)) : Bool :=
  L.all fun y => decide (y * a = a * y)

theorem centralIn_iff (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (a : Equiv.Perm (Fin n)) :
    centralIn (elemsT Q) a = true ↔ ∀ y ∈ Q.originalSubgroup, y * a = a * y := by
  unfold centralIn
  rw [List.all_eq_true]
  constructor
  · intro h y hy
    simpa using h y ((mem_elemsT Q hQ y).2 hy)
  · intro h y hy
    simpa using h y ((mem_elemsT Q hQ y).1 hy)

@[expose] def isComm (L : List (Equiv.Perm (Fin n))) (a : Equiv.Perm (Fin n)) : Bool :=
  L.any fun u => L.any fun w => decide (u * w * u⁻¹ * w⁻¹ = a)

theorem isComm_iff (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (a : Equiv.Perm (Fin n)) :
    isComm (elemsT Q) a = true ↔
      ∃ u ∈ Q.originalSubgroup, ∃ w ∈ Q.originalSubgroup, u * w * u⁻¹ * w⁻¹ = a := by
  unfold isComm
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu, w, hw, h⟩
    exact ⟨u, (mem_elemsT Q hQ u).1 hu, w, (mem_elemsT Q hQ w).1 hw, h⟩
  · rintro ⟨u, hu, w, hw, h⟩
    exact ⟨u, (mem_elemsT Q hQ u).2 hu, w, (mem_elemsT Q hQ w).2 hw, h⟩

@[expose] def smallCheck (L : List (Equiv.Perm (Fin n))) (s0 : Equiv.Perm (Fin n)) : Bool :=
  decide (s0 ∈ L) && decide (s0 ≠ 1) && decide (s0 ^ 2 = 1) && centralIn L s0 &&
    L.all fun a => bif centralIn L a && decide (a ^ 2 = 1) then
      (decide (a = 1) || decide (a = s0)) && isComm L a else true

theorem smallCheck_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {s0 : Equiv.Perm (Fin n)} (h : smallCheck (elemsT Q) s0 = true) :
    s0 ∈ Q.originalSubgroup ∧ s0 ≠ 1 ∧ s0 ^ 2 = 1 ∧
      (∀ y ∈ Q.originalSubgroup, y * s0 = s0 * y) ∧
      (∀ a ∈ Q.originalSubgroup, (∀ y ∈ Q.originalSubgroup, y * a = a * y) → a ^ 2 = 1 →
        ∃ u ∈ Q.originalSubgroup, ∃ w ∈ Q.originalSubgroup, u * w * u⁻¹ * w⁻¹ = a) ∧
      (∀ a ∈ Q.originalSubgroup, (∀ y ∈ Q.originalSubgroup, y * a = a * y) → a ^ 2 = 1 →
        a = 1 ∨ a = s0) := by
  unfold smallCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hall := List.all_eq_true.1 h5
  refine ⟨(mem_elemsT Q hQ s0).1 h1, h2, h3, (centralIn_iff Q hQ s0).1 h4, ?_, ?_⟩
  · intro a ha hac ha2
    have := (bif_imp _ _).1 (hall a ((mem_elemsT Q hQ a).2 ha))
      (by simp [(centralIn_iff Q hQ a).2 hac, ha2])
    simp only [Bool.and_eq_true] at this
    exact (isComm_iff Q hQ a).1 this.2
  · intro a ha hac ha2
    have := (bif_imp _ _).1 (hall a ((mem_elemsT Q hQ a).2 ha))
      (by simp [(centralIn_iff Q hQ a).2 hac, ha2])
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.1

@[expose] def benderCheck (L : List (Equiv.Perm (Fin n))) (t : Equiv.Perm (Fin n)) (r : ℕ) :
    Bool :=
  (L.all fun x => bif decide (x ^ 2 = 1) then centralIn L x else true) &&
  (L.all fun a => bif centralIn L a then decide (a ^ 2 = 1) && isComm L a else true) &&
  (L.all fun y => decide (t * y * t⁻¹ ∈ L) && decide (t⁻¹ * y * t ∈ L)) &&
  (L.all fun a => bif centralIn L a && decide (a ≠ 1) then
    L.all fun b => bif centralIn L b && decide (b ≠ 1) then
      (List.range r).any fun k => decide (t ^ k * a * (t ^ k)⁻¹ = b) else true else true)

theorem benderCheck_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {t : Equiv.Perm (Fin n)} {r : ℕ} (h : benderCheck (elemsT Q) t r = true) :
    (∀ x ∈ Q.originalSubgroup, x ^ 2 = 1 → ∀ y ∈ Q.originalSubgroup, y * x = x * y) ∧
    (∀ a ∈ Q.originalSubgroup, (∀ y ∈ Q.originalSubgroup, y * a = a * y) → a ^ 2 = 1) ∧
    (∀ a ∈ Q.originalSubgroup, (∀ y ∈ Q.originalSubgroup, y * a = a * y) →
      ∃ u ∈ Q.originalSubgroup, ∃ w ∈ Q.originalSubgroup, u * w * u⁻¹ * w⁻¹ = a) ∧
    (∀ y ∈ Q.originalSubgroup, t * y * t⁻¹ ∈ Q.originalSubgroup) ∧
    (∀ y ∈ Q.originalSubgroup, t⁻¹ * y * t ∈ Q.originalSubgroup) ∧
    (∀ a ∈ Q.originalSubgroup, (∀ y ∈ Q.originalSubgroup, y * a = a * y) → a ≠ 1 →
      ∀ b ∈ Q.originalSubgroup, (∀ y ∈ Q.originalSubgroup, y * b = b * y) → b ≠ 1 →
        ∃ k : ℕ, t ^ k * a * (t ^ k)⁻¹ = b) := by
  unfold benderCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hx2 y hy
    have := (bif_imp _ _).1 (List.all_eq_true.1 h1 x ((mem_elemsT Q hQ x).2 hx)) (by simpa using hx2)
    exact (centralIn_iff Q hQ x).1 this y hy
  · intro a ha hac
    have := (bif_imp _ _).1 (List.all_eq_true.1 h2 a ((mem_elemsT Q hQ a).2 ha))
      ((centralIn_iff Q hQ a).2 hac)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · intro a ha hac
    have := (bif_imp _ _).1 (List.all_eq_true.1 h2 a ((mem_elemsT Q hQ a).2 ha))
      ((centralIn_iff Q hQ a).2 hac)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact (isComm_iff Q hQ a).1 this.2
  · intro y hy
    have := List.all_eq_true.1 h3 y ((mem_elemsT Q hQ y).2 hy)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact (mem_elemsT Q hQ _).1 this.1
  · intro y hy
    have := List.all_eq_true.1 h3 y ((mem_elemsT Q hQ y).2 hy)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact (mem_elemsT Q hQ _).1 this.2
  · intro a ha hac ha1 b hb hbc hb1
    have h5 := (bif_imp _ _).1 (List.all_eq_true.1 h4 a ((mem_elemsT Q hQ a).2 ha))
      (by simp [(centralIn_iff Q hQ a).2 hac, ha1])
    have h6 := (bif_imp _ _).1 (List.all_eq_true.1 h5 b ((mem_elemsT Q hQ b).2 hb))
      (by simp [(centralIn_iff Q hQ b).2 hbc, hb1])
    obtain ⟨k, -, hk⟩ := List.any_eq_true.1 h6
    exact ⟨k, by simpa using hk⟩

end CFSG.GH74.KGroups

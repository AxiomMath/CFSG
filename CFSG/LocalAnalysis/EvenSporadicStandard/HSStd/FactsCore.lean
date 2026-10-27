module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsData

public section

namespace CFSG.EvenSporadicStandard.HSStd

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

variable {n : ℕ}

theorem commPt_iff {x g : Tab} {X G : Equiv.Perm (Fin n)} (hx : TabRep x X) (hg : TabRep g G) :
    commPt n x g = true ↔ X * G = G * X := by
  simp only [commPt, allBelow_eq_true, beq_iff_eq]
  constructor
  · intro h
    ext i
    have h1 := h i.val i.2
    rw [hg.apply i, hx.apply (G i), hx.apply i, hg.apply (X i)] at h1
    exact h1
  · intro h k hk
    have h1 := congrArg (fun p => (p ⟨k, hk⟩ : ℕ)) h
    simp only [Equiv.Perm.mul_apply] at h1
    rw [hg.apply ⟨k, hk⟩, hx.apply (G ⟨k, hk⟩), hx.apply ⟨k, hk⟩, hg.apply (X ⟨k, hk⟩)]
    exact h1

theorem commPt2_iff {w x g : Tab} {W X G : Equiv.Perm (Fin n)} (hw : TabRep w W)
    (hx : TabRep x X) (hg : TabRep g G) :
    commPt2 n w x g = true ↔ (W * X) * G = G * (W * X) := by
  simp only [commPt2, allBelow_eq_true, beq_iff_eq]
  constructor
  · intro h
    ext i
    have h1 := h i.val i.2
    rw [hg.apply i, hx.apply (G i), hw.apply (X (G i)), hx.apply i, hw.apply (X i),
      hg.apply (W (X i))] at h1
    exact h1
  · intro h k hk
    have h1 := congrArg (fun p => (p ⟨k, hk⟩ : ℕ)) h
    simp only [Equiv.Perm.mul_apply] at h1
    rw [hg.apply ⟨k, hk⟩, hx.apply (G ⟨k, hk⟩), hw.apply (X (G ⟨k, hk⟩)), hx.apply ⟨k, hk⟩,
      hw.apply (X ⟨k, hk⟩), hg.apply (W (X ⟨k, hk⟩))]
    exact h1

theorem sqPt_iff {x : Tab} {X : Equiv.Perm (Fin n)} (hx : TabRep x X) :
    sqPt n x = true ↔ X * X = 1 := by
  simp only [sqPt, allBelow_eq_true, beq_iff_eq]
  constructor
  · intro h
    ext i
    have h1 := h i.val i.2
    rw [hx.apply i, hx.apply (X i)] at h1
    simpa using h1
  · intro h k hk
    have h1 := congrArg (fun p => (p ⟨k, hk⟩ : ℕ)) h
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id_eq] at h1
    rw [hx.apply ⟨k, hk⟩, hx.apply (X ⟨k, hk⟩)]
    exact h1

theorem sqPt2_iff {w x : Tab} {W X : Equiv.Perm (Fin n)} (hw : TabRep w W) (hx : TabRep x X) :
    sqPt2 n w x = true ↔ (W * X) * (W * X) = 1 := by
  simp only [sqPt2, allBelow_eq_true, beq_iff_eq]
  constructor
  · intro h
    ext i
    have h1 := h i.val i.2
    rw [hx.apply i, hw.apply (X i), hx.apply (W (X i)), hw.apply (X (W (X i)))] at h1
    simpa using h1
  · intro h k hk
    have h1 := congrArg (fun p => (p ⟨k, hk⟩ : ℕ)) h
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id_eq] at h1
    rw [hx.apply ⟨k, hk⟩, hw.apply (X ⟨k, hk⟩), hx.apply (W (X ⟨k, hk⟩)),
      hw.apply (X (W (X ⟨k, hk⟩)))]
    exact h1


theorem gs_all_iff {gs : Array Tab} {G : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ j < gs.size, TabRep gs[j]! (G j)) {x : Tab} {X : Equiv.Perm (Fin n)}
    (hx : TabRep x X) :
    gs.all (commPt n x) = true ↔ ∀ j < gs.size, X * G j = G j * X := by
  rw [Array.all_eq_true]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  have := hgs j hj
  rw [getElem!_pos gs j hj] at this
  exact commPt_iff hx this

theorem gs_all_iff2 {gs : Array Tab} {G : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ j < gs.size, TabRep gs[j]! (G j)) {w x : Tab} {W X : Equiv.Perm (Fin n)}
    (hw : TabRep w W) (hx : TabRep x X) :
    gs.all (commPt2 n w x) = true ↔ ∀ j < gs.size, (W * X) * G j = G j * (W * X) := by
  rw [Array.all_eq_true]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  have := hgs j hj
  rw [getElem!_pos gs j hj] at this
  exact commPt2_iff hw hx this

theorem sqCheck_spec {H : Subgroup (Equiv.Perm (Fin n))} {T : Array Tab}
    (hH : Enumerates H T.toList) {w : Tab} {W : Equiv.Perm (Fin n)} (hw : TabRep w W)
    {gs : Array Tab} {G : ℕ → Equiv.Perm (Fin n)} (hgs : ∀ j < gs.size, TabRep gs[j]! (G j))
    (h : sqCheck n T w gs = true) :
    (∀ y ∈ H, (∀ j < gs.size, y * G j = G j * y) → y * y = 1) ∧
      ∀ y ∈ H, (∀ j < gs.size, (W * y) * G j = G j * (W * y)) → (W * y) * (W * y) = 1 := by
  simp only [sqCheck, Array.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine ⟨fun y hy hc => ?_, fun y hy hc => ?_⟩
  · obtain ⟨k, hk, hr⟩ := hH.exists_pos hy
    rw [getElem!_pos T k hk] at hr
    rcases (h k hk).1 with h1 | h1
    · rw [Bool.eq_false_iff] at h1
      exact absurd ((gs_all_iff hgs hr).2 hc) h1
    · exact (sqPt_iff hr).1 h1
  · obtain ⟨k, hk, hr⟩ := hH.exists_pos hy
    rw [getElem!_pos T k hk] at hr
    rcases (h k hk).2 with h1 | h1
    · rw [Bool.eq_false_iff] at h1
      exact absurd ((gs_all_iff2 hgs hw hr).2 hc) h1
    · exact (sqPt2_iff hw hr).1 h1

end CFSG.EvenSporadicStandard.HSStd

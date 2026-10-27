module

public import CFSG.Certificates.Kernel.ListBridge.PackSound

public section

namespace CFSG.ClassicalInvolution.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.KC.ListBridge

variable {n w : Nat}

@[expose] def CR (n w X : Nat) (x : Equiv.Perm (Fin n)) : Prop :=
  canonK n w (mask w) (n * w) X = true ∧ PRep n w X x

@[expose] def TwinSet (n w : Nat) (L : List (Equiv.Perm (Fin n))) (N : Nat) (Q : Nat → Nat) :
    Prop :=
  (∀ k < N, canonK n w (mask w) (n * w) (Q k) = true) ∧
    (∀ x, x ∈ L ↔ ∃ k < N, PRep n w (Q k) x) ∧ ∀ k < N, ∃ x ∈ L, PRep n w (Q k) x

theorem CR.eq_iff {X Y : Nat} {x y : Equiv.Perm (Fin n)} (hX : CR n w X x) (hY : CR n w Y y) :
    x = y ↔ X = Y := by
  constructor
  · rintro rfl
    exact eq_of_prep hX.1 hY.1 hX.2 hY.2
  · rintro rfl
    exact prep_unique hX.2 hY.2

theorem CR.beq_iff {X Y : Nat} {x y : Equiv.Perm (Fin n)} (hX : CR n w X x) (hY : CR n w Y y) :
    x = y ↔ Nat.beq X Y = true := by
  rw [hX.eq_iff hY]
  exact ⟨fun e => by rw [e]; exact Nat.beq_refl Y, Nat.eq_of_beq_eq_true⟩

theorem CR.mul {X Y : Nat} {x y : Equiv.Perm (Fin n)} (hX : CR n w X x) (hY : CR n w Y y) :
    CR n w (pcomp n w (mask w) X Y) (x * y) := by
  obtain ⟨hn, -, -, -⟩ := CFSG.KS.PF.canon_facts hX.1
  exact ⟨canonK_pcomp hX.1 hY.1, prep_pcomp (by omega) hX.2 hY.2⟩

theorem CR.inv {X : Nat} {x : Equiv.Perm (Fin n)} (hX : CR n w X x) :
    CR n w (pinvS n w (mask w) X) x⁻¹ := by
  obtain ⟨-, hw, -, -⟩ := CFSG.KS.PF.canon_facts hX.1
  have hI : CFSG.KS.PinvS.InjK n w X :=
    ⟨fun i hi => by rw [hX.2 ⟨i, hi⟩]; exact (x ⟨i, hi⟩).2, fun a ha b hb e => by
      rw [hX.2 ⟨a, ha⟩, hX.2 ⟨b, hb⟩] at e
      exact congrArg Fin.val (x.injective (Fin.ext e))⟩
  exact ⟨CFSG.KS.PinvS.canonK_pinvS hX.1 hI,
    (CFSG.KS.SporSch.MOC.prep_pinvS (by omega) hX.2).1⟩

theorem CR.one (hsz : szOK n w = true) : CR n w (pidn n w) 1 := by
  obtain ⟨hn, hw⟩ := szOK_facts' hsz
  exact ⟨(PP.id hsz).1, prep_pidn hn hw⟩

theorem TwinSet.mem_iff {L : List (Equiv.Perm (Fin n))} {N X : Nat} {Q : Nat → Nat}
    {x : Equiv.Perm (Fin n)} (h : TwinSet n w L N Q) (hX : CR n w X x) :
    x ∈ L ↔ inK N Q X = true := by
  rw [h.2.1 x]
  unfold inK
  rw [anyN_eq, List.any_eq_true]
  constructor
  · rintro ⟨k, hk, hp⟩
    refine ⟨k, List.mem_range.2 hk, ?_⟩
    rw [eq_of_prep (h.1 k hk) hX.1 hp hX.2]
    exact Nat.beq_refl X
  · rintro ⟨k, hk, e⟩
    refine ⟨k, List.mem_range.1 hk, ?_⟩
    rw [Nat.eq_of_beq_eq_true e]
    exact hX.2

theorem TwinSet.cr {L : List (Equiv.Perm (Fin n))} {N : Nat} {Q : Nat → Nat}
    {x : Equiv.Perm (Fin n)} (h : TwinSet n w L N Q) (hx : x ∈ L) :
    ∃ k < N, CR n w (Q k) x := by
  obtain ⟨k, hk, hp⟩ := (h.2.1 x).1 hx
  exact ⟨k, hk, h.1 k hk, hp⟩

theorem TwinSet.exists_cr {L : List (Equiv.Perm (Fin n))} {N : Nat} {Q : Nat → Nat}
    (h : TwinSet n w L N Q) {k : Nat} (hk : k < N) : ∃ x ∈ L, CR n w (Q k) x := by
  obtain ⟨x, hx, hp⟩ := h.2.2 k hk
  exact ⟨x, hx, h.1 k hk, hp⟩

theorem prep_of_inK {N X : Nat} {T : Nat → Nat} {x : Equiv.Perm (Fin n)} (h : inK N T X = true)
    (hX : PRep n w X x) : ∃ j < N, PRep n w (T j) x := by
  obtain ⟨j, hj, e⟩ := inK_spec h
  exact ⟨j, hj, by rw [e]; exact hX⟩

theorem q8_twin {Q : Nat → Nat} {i j : Equiv.Perm (Fin n)} (hsz : szOK n w = true)
    (hc : ∀ k < 8, canonK n w (mask w) (n * w) (Q k) = true)
    (hI : PRep n w (Q 1) i) (hJ : PRep n w (Q 4) j) (h0 : Q 0 = pidn n w)
    (h2 : Q 2 = pcomp n w (mask w) (Q 1) (Q 1)) (h3 : Q 3 = pcomp n w (mask w) (Q 2) (Q 1))
    (h5 : Q 5 = pcomp n w (mask w) (Q 1) (Q 4)) (h6 : Q 6 = pcomp n w (mask w) (Q 2) (Q 4))
    (h7 : Q 7 = pcomp n w (mask w) (Q 3) (Q 4)) :
    TwinSet n w [1, i, i * i, i * i * i, j, i * j, i * i * j, i * i * i * j] 8 Q ∧
      PRep n w (Q 2) (i * i) ∧ PRep n w (Q 6) (i * i * j) ∧ PRep n w (Q 7) (i * i * i * j) := by
  obtain ⟨hn, hw⟩ := szOK_facts' hsz
  have hn32 : n < 2 ^ 32 := by omega
  have p0 : PRep n w (Q 0) 1 := by rw [h0]; exact prep_pidn hn hw
  have p2 : PRep n w (Q 2) (i * i) := by rw [h2]; exact prep_pcomp hn32 hI hI
  have p3 : PRep n w (Q 3) (i * i * i) := by rw [h3]; exact prep_pcomp hn32 p2 hI
  have p5 : PRep n w (Q 5) (i * j) := by rw [h5]; exact prep_pcomp hn32 hI hJ
  have p6 : PRep n w (Q 6) (i * i * j) := by rw [h6]; exact prep_pcomp hn32 p2 hJ
  have p7 : PRep n w (Q 7) (i * i * i * j) := by rw [h7]; exact prep_pcomp hn32 p3 hJ
  refine ⟨⟨hc, fun x => ⟨fun hx => ?_, fun ⟨k, hk, hp⟩ => ?_⟩, fun k hk => ?_⟩, p2, p6, p7⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num, p0⟩
    · exact ⟨1, by norm_num, hI⟩
    · exact ⟨2, by norm_num, p2⟩
    · exact ⟨3, by norm_num, p3⟩
    · exact ⟨4, by norm_num, hJ⟩
    · exact ⟨5, by norm_num, p5⟩
    · exact ⟨6, by norm_num, p6⟩
    · exact ⟨7, by norm_num, p7⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    interval_cases k
    · exact Or.inl (prep_unique hp p0)
    · exact Or.inr (Or.inl (prep_unique hp hI))
    · exact Or.inr (Or.inr (Or.inl (prep_unique hp p2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (prep_unique hp p3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prep_unique hp hJ)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prep_unique hp p5))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prep_unique hp p6)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (prep_unique hp p7)))))))
  · interval_cases k
    · exact ⟨1, by simp, p0⟩
    · exact ⟨i, by simp, hI⟩
    · exact ⟨i * i, by simp, p2⟩
    · exact ⟨i * i * i, by simp, p3⟩
    · exact ⟨j, by simp, hJ⟩
    · exact ⟨i * j, by simp, p5⟩
    · exact ⟨i * i * j, by simp, p6⟩
    · exact ⟨i * i * i * j, by simp, p7⟩

end CFSG.ClassicalInvolution.ListBridge

end

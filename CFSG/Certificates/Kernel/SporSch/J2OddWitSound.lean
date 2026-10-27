module

public import Certificates.Data.Kernel.SporSch.J2OddWit
public import CFSG.Certificates.Kernel.SporSch.ChainKPack

public section

namespace CFSG.KS.SporSch.J2OW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Sporadic.Schreier

variable {n w : Nat}

@[expose] def TabRep (n w nT : Nat) (ps : List Nat) (g : Nat → Equiv.Perm (Fin n)) : Prop :=
  ∀ i < nT, PRep n w (getK 0 ps i) (g i) ∧ getK 0 ps i >>> (n * w) = 0

theorem tabK_sound (hsz : szOK n w = true) {A B : Nat} {gA gB : Equiv.Perm (Fin n)}
    (pA : PRep n w A gA) (pB : PRep n w B gB) {nT : Nat} {ws : List (List Nat)} {ps : List Nat}
    (h : tabK n w (mask w) (pidn n w) A B (powK n w (mask w) (pidn n w) A 1)
      (powK n w (mask w) (pidn n w) B 2) nT ws ps = true) :
    TabRep n w nT ps fun i => (wordElts gA gB 2 3 (getW ws i)).prod := by
  intro i hi
  unfold tabK at h
  have e := Nat.eq_of_beq_eq_true (allN_spec h i hi)
  have hx := prep_xyWordK hsz pA pB 2 3 (getW ws i)
  rw [← e]
  exact hx

theorem wordElts_prod_mem {G : Type*} [Group G] {H : Subgroup G} {gA gB : G} (hA : gA ∈ H)
    (hB : gB ∈ H) (wd : List Nat) : (wordElts gA gB 2 3 wd).prod ∈ H := by
  refine Subgroup.list_prod_mem H (fun x hx => ?_)
  obtain ⟨l, -, hx⟩ := List.mem_flatMap.1 hx
  split_ifs at hx
  · rw [List.mem_singleton] at hx
    exact hx ▸ hA
  · rw [List.mem_singleton] at hx
    exact hx ▸ hB
  · exact (List.mem_replicate.1 hx).2 ▸ hA
  · exact (List.mem_replicate.1 hx).2 ▸ hB

variable {nT : Nat} {ps : List Nat} {g : Nat → Equiv.Perm (Fin n)}

theorem powsK_sound (hsz : szOK n w = true) (hT : TabRep n w nT ps g) :
    ∀ {L : List (Nat × Nat × Nat)}, powsK n w (mask w) (pidn n w) nT ps L = true →
      ∀ r ∈ L, r.1 < nT ∧ r.2.2 < nT ∧ g r.2.2 = g r.1 ^ r.2.1
  | [], _ => by simp
  | ⟨i, k, j⟩ :: L, h => by
    have h' : bAnd(bAnd(Nat.blt i nT, bAnd(Nat.blt j nT,
        Nat.beq (powK n w (mask w) (pidn n w) (getK 0 ps i) k) (getK 0 ps j))),
        powsK n w (mask w) (pidn n w) nT ps L) = true := h
    simp only [bAnd_iff, Nat.blt_eq] at h'
    obtain ⟨⟨hi, hj, h3⟩, h4⟩ := h'
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · refine ⟨hi, hj, ?_⟩
      have p1 := (prep_powK hsz (hT i hi).1 k).1
      rw [Nat.eq_of_beq_eq_true h3] at p1
      exact MOC.prep_unique (hT j hj).1 p1
    · exact powsK_sound hsz hT h4 r hr

theorem conjsK_sound (hsz : szOK n w = true) (hT : TabRep n w nT ps g) :
    ∀ {L : List (Nat × Nat × Nat)}, conjsK n w (mask w) nT ps L = true →
      ∀ r ∈ L, r.1 < nT ∧ r.2.1 < nT ∧ r.2.2 < nT ∧ g r.1 * g r.2.1 = g r.2.2 * g r.1
  | [], _ => by simp
  | ⟨d, x, y⟩ :: L, h => by
    have h' : bAnd(bAnd(Nat.blt d nT, bAnd(Nat.blt x nT, bAnd(Nat.blt y nT,
        Nat.beq (pcomp n w (mask w) (getK 0 ps d) (getK 0 ps x))
          (pcomp n w (mask w) (getK 0 ps y) (getK 0 ps d))))),
        conjsK n w (mask w) nT ps L) = true := h
    simp only [bAnd_iff, Nat.blt_eq] at h'
    obtain ⟨⟨hd, hx, hy, h3⟩, h4⟩ := h'
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · refine ⟨hd, hx, hy, ?_⟩
      have hn := szOK_lt hsz
      have p1 := prep_pcomp hn (hT d hd).1 (hT x hx).1
      rw [Nat.eq_of_beq_eq_true h3] at p1
      exact MOC.prep_unique p1 (prep_pcomp hn (hT y hy).1 (hT d hd).1)
    · exact conjsK_sound hsz hT h4 r hr

theorem commsK_sound (hsz : szOK n w = true) (hT : TabRep n w nT ps g) :
    ∀ {L : List (Nat × Nat)}, commsK n w (mask w) nT ps L = true →
      ∀ r ∈ L, r.1 < nT ∧ r.2 < nT ∧ g r.1 * g r.2 = g r.2 * g r.1
  | [], _ => by simp
  | ⟨x, y⟩ :: L, h => by
    have h' : bAnd(bAnd(Nat.blt x nT, bAnd(Nat.blt y nT,
        Nat.beq (pcomp n w (mask w) (getK 0 ps x) (getK 0 ps y))
          (pcomp n w (mask w) (getK 0 ps y) (getK 0 ps x)))),
        commsK n w (mask w) nT ps L) = true := h
    simp only [bAnd_iff, Nat.blt_eq] at h'
    obtain ⟨⟨hx, hy, h3⟩, h4⟩ := h'
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · refine ⟨hx, hy, ?_⟩
      have hn := szOK_lt hsz
      have p1 := prep_pcomp hn (hT x hx).1 (hT y hy).1
      rw [Nat.eq_of_beq_eq_true h3] at p1
      exact MOC.prep_unique p1 (prep_pcomp hn (hT y hy).1 (hT x hx).1)
    · exact commsK_sound hsz hT h4 r hr

theorem ordsK_sound (hsz : szOK n w = true) (hT : TabRep n w nT ps g) :
    ∀ {L : List (Nat × Nat)}, ordsK n w (mask w) (pidn n w) nT ps L = true →
      ∀ r ∈ L, r.1 < nT ∧ orderOf (g r.1) = r.2
  | [], _ => by simp
  | ⟨i, o⟩ :: L, h => by
    have h' : bAnd(bAnd(Nat.blt i nT, bAnd(Nat.blt 0 o,
        ordIs n w (mask w) (pidn n w) (getK 0 ps i) (Nat.sub o 1))),
        ordsK n w (mask w) (pidn n w) nT ps L) = true := h
    simp only [bAnd_iff, Nat.blt_eq] at h'
    obtain ⟨⟨hi, ho, h3⟩, h4⟩ := h'
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨hi, ordIs_orderOf hsz (hT i hi).1 (hT i hi).2 ho h3⟩
    · exact ordsK_sound hsz hT h4 r hr

theorem memK_spec {v : Nat} : ∀ {M : List Nat}, memK ps v M = true → ∃ k ∈ M, v = getK 0 ps k
  | [], h => by simp [memK] at h
  | j :: M, h => by
    have h' : bIf(Nat.beq v (getK 0 ps j), true, memK ps v M) = true := h
    cases hb : Nat.beq v (getK 0 ps j)
    · rw [hb] at h'
      obtain ⟨k, hk, e⟩ := memK_spec h'
      exact ⟨k, List.mem_cons_of_mem _ hk, e⟩
    · exact ⟨j, List.mem_cons_self, Nat.eq_of_beq_eq_true hb⟩

theorem memK_of {v j : Nat} : ∀ {M : List Nat}, j ∈ M → v = getK 0 ps j → memK ps v M = true
  | [], h, _ => by simp at h
  | k :: M, h, e => by
    have h' : memK ps v (k :: M) = bIf(Nat.beq v (getK 0 ps k), true, memK ps v M) := rfl
    rw [h']
    cases hb : Nat.beq v (getK 0 ps k)
    · rcases List.mem_cons.1 h with rfl | h
      · rw [e, Nat.beq_refl] at hb
        exact absurd hb (by decide)
      · exact memK_of h e
    · rfl

theorem allRec_spec {f : Nat → Bool} : ∀ {M : List Nat},
    List.rec (motive := fun _ => Bool) true (fun j _ ih => bAnd(f j, ih)) M = true →
      ∀ j ∈ M, f j = true
  | [], _ => by simp
  | k :: M, h => by
    have h' : bAnd(f k, List.rec (motive := fun _ => Bool) true (fun j _ ih => bAnd(f j, ih)) M)
        = true := h
    rw [bAnd_iff] at h'
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact h'.1
    · exact allRec_spec h'.2 j hj

theorem closedK_sound (hsz : szOK n w = true) (hT : TabRep n w nT ps g) {M : List Nat} :
    ∀ {L : List Nat}, closedK n w (mask w) nT ps M L = true →
      (∀ i ∈ L, i < nT) ∧ (L.map g).Nodup ∧
        ∀ i ∈ L, ∀ j ∈ M, memK ps (pcomp n w (mask w) (getK 0 ps i) (getK 0 ps j)) M = true
  | [], _ => by simp
  | i :: L, h => by
    have h' : bAnd(Nat.blt i nT, bAnd(bIf(memK ps (getK 0 ps i) L, false, true),
        bAnd(List.rec (motive := fun _ => Bool) true (fun j _ ih2 =>
          bAnd(memK ps (pcomp n w (mask w) (getK 0 ps i) (getK 0 ps j)) M, ih2)) M,
          closedK n w (mask w) nT ps M L))) = true := h
    simp only [bAnd_iff, Nat.blt_eq] at h'
    obtain ⟨hi, hnm, hall, hL⟩ := h'
    obtain ⟨ih1, ih2, ih3⟩ := closedK_sound hsz hT hL
    have hM := allRec_spec hall
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hi
      · exact ih1 j hj
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, ih2⟩
      obtain ⟨j, hj, e⟩ := List.mem_map.1 hmem
      have hw := PF.w_pos (szOK_facts hsz).2
      have hb := beq_prep hw (hT i hi).1 (hT j (ih1 j hj)).1 (hT i hi).2 (hT j (ih1 j hj)).2
      rw [e, decide_eq_true rfl] at hb
      have := memK_of (ps := ps) hj (Nat.eq_of_beq_eq_true hb)
      rw [this] at hnm
      exact absurd hnm (by decide)
    · intro i' hi' j hj
      rcases List.mem_cons.1 hi' with rfl | hi'
      · exact hM j hj
      · exact ih3 i' hi' j hj

end CFSG.KS.SporSch.J2OW

end

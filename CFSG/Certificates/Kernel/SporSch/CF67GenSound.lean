module

public import Certificates.Data.Kernel.SporSch.CF67GenK
public import Certificates.Data.CF67Check
public import CFSG.Certificates.Kernel.SporSch.OddWitSound

public section

namespace CFSG.KS.SporSch.CF67K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Certificates.CF67

variable {n w : Nat}

private theorem sylK_allN {k : Nat} {f : Nat → Bool} : allN k f = true ↔ ∀ i < k, f i = true := by
  rw [allN_eq, List.all_eq_true]
  simp only [List.mem_range]

private theorem sylK_tblEq {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g)
    (hT : Rep n T h) : CFSG.Sporadic.Schreier.Native.tblEq n S T = decide (g = h) := by
  by_cases e : g = h
  · rw [decide_eq_true e]
    subst e
    exact tblEq_iff.2 fun i hi => (hS i hi).trans (hT i hi).symm
  · rw [decide_eq_false e]
    cases hb : CFSG.Sporadic.Schreier.Native.tblEq n S T
    · rfl
    · exact absurd (rep_unique hS (rep_of_tblEq hT hb)) e

private theorem sylK_powT (hn : n < 2 ^ 32) {T : Table} {g : Equiv.Perm (Fin n)}
    (hT : Rep n T g) : ∀ k : ℕ, Rep n (cf67PowT n T k) (g ^ k)
  | 0 => by simpa [cf67PowT] using Rep.idT hn
  | k + 1 => by simpa [cf67PowT, pow_succ'] using Rep.compT hT (sylK_powT hn hT k)

private theorem sylK_powFix (hn : n < 2 ^ 32) (g : Equiv.Perm (Fin n)) (e : Nat) :
    CFSG.Sporadic.Schreier.Native.powFixW n [toTable g] e = decide (g ^ e = 1) := by
  have := powFixW_iff perm_faithful (List.Forall₂.cons (rep_toTable hn g) List.Forall₂.nil) e
  rw [List.prod_singleton] at this
  rw [Bool.eq_iff_iff, this, decide_eq_true_iff]

private theorem sylK_isPair (hsz : szOK n w = true) {A B : Nat} {a b : Equiv.Perm (Fin n)}
    (hA : PRep n w A a) (sA : A >>> (n * w) = 0) (hB : PRep n w B b) (sB : B >>> (n * w) = 0)
    (r : Nat) : isPairK n w r A B = cf67IsPair n r (toTable a) (toTable b) := by
  have hf := szOK_facts hsz
  have hn := szOK_lt hsz
  have hw := PF.w_pos hf.2
  have pI := prep_pidn hf.1 hf.2
  have sI := PF.pidn_shr hf.1 hf.2
  have e1 : Nat.beq (powK n w (mask w) (pidn n w) A r) (pidn n w) = decide (a ^ r = 1) :=
    OddWit.beq_eq_decide hw (prep_powK hsz hA r).1 pI (prep_powK hsz hA r).2 sI
  have e2 : Nat.beq (powK n w (mask w) (pidn n w) B r) (pidn n w) = decide (b ^ r = 1) :=
    OddWit.beq_eq_decide hw (prep_powK hsz hB r).1 pI (prep_powK hsz hB r).2 sI
  have e3 : Nat.beq A (pidn n w) = decide (a = 1) := OddWit.beq_eq_decide hw hA pI sA sI
  have e4 : ∀ k, Nat.beq B (powK n w (mask w) (pidn n w) A k) = decide (b = a ^ k) := fun k =>
    OddWit.beq_eq_decide hw hB (prep_powK hsz hA k).1 sB (prep_powK hsz hA k).2
  have e5 : Nat.beq (pcomp n w (mask w) A B) (pcomp n w (mask w) B A) = decide (a * b = b * a) :=
    OddWit.beq_eq_decide hw (prep_pcomp hn hA hB) (prep_pcomp hn hB hA) (PF.pcomp_shr _ _ hn hw)
      (PF.pcomp_shr _ _ hn hw)
  have t3 : CFSG.Sporadic.Schreier.Native.tblEq n (toTable a) (idT n) = decide (a = 1) :=
    sylK_tblEq (rep_toTable hn a) (Rep.idT hn)
  have t4 : ∀ k, CFSG.Sporadic.Schreier.Native.tblEq n (toTable b) (cf67PowT n (toTable a) k) =
      decide (b = a ^ k) := fun k =>
    sylK_tblEq (rep_toTable hn b) (sylK_powT hn (rep_toTable hn a) k)
  have t5 : CFSG.Sporadic.Schreier.Native.commT n (toTable a) (toTable b) =
      decide (a * b = b * a) :=
    sylK_tblEq (Rep.compT (rep_toTable hn a) (rep_toTable hn b))
      (Rep.compT (rep_toTable hn b) (rep_toTable hn a))
  rw [isPairK, cf67IsPair, e1, e2, e3, e5, sylK_powFix hn, sylK_powFix hn, t3, t5, allN_eq]
  simp only [e4, t4]

private theorem sylK_inGen (hsz : szOK n w = true) {A B C : Nat} {a b c : Equiv.Perm (Fin n)}
    (hA : PRep n w A a) (hB : PRep n w B b) (hC : PRep n w C c) (sC : C >>> (n * w) = 0)
    (r : Nat) (h : inGenK n w r A B C = true) : ∃ i < r, ∃ j < r, c = a ^ i * b ^ j := by
  have hf := szOK_facts hsz
  have hn := szOK_lt hsz
  have hw := PF.w_pos hf.2
  have e : ∀ i j, Nat.beq C (pcomp n w (mask w) (powK n w (mask w) (pidn n w) A i)
      (powK n w (mask w) (pidn n w) B j)) = decide (c = a ^ i * b ^ j) := fun i j =>
    OddWit.beq_eq_decide hw hC (prep_pcomp hn (prep_powK hsz hA i).1 (prep_powK hsz hB j).1) sC
      (PF.pcomp_shr _ _ hn hw)
  rw [inGenK] at h
  simp only [e, allN_eq] at h
  simpa [List.all_eq_true, List.mem_range] using h

private theorem sylK_gen (hn : n < 2 ^ 32) {a b c : Equiv.Perm (Fin n)} {r : Nat}
    (h : ∃ i < r, ∃ j < r, c = a ^ i * b ^ j) :
    (cf67Gen n r (toTable a) (toTable b)).any
      (CFSG.Sporadic.Schreier.Native.tblEq n (toTable c)) = true := by
  obtain ⟨i, hi, j, hj, rfl⟩ := h
  rw [cf67Gen, List.any_flatMap, List.any_eq_true]
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  rw [List.any_map, List.any_eq_true]
  refine ⟨j, List.mem_range.2 hj, ?_⟩
  rw [Function.comp_apply, sylK_tblEq (rep_toTable hn _)
    (Rep.compT (sylK_powT hn (rep_toTable hn a) i) (sylK_powT hn (rep_toTable hn b) j))]
  exact decide_eq_true rfl

private theorem sylK_nodupT (hn : n < 2 ^ 32) :
    ∀ {L : List (Equiv.Perm (Fin n))}, L.Pairwise (· ≠ ·) → cf67NodupT n (L.map toTable) = true
  | [], _ => rfl
  | a :: l, hL => by
    rw [List.pairwise_cons] at hL
    rw [List.map_cons, cf67NodupT, Bool.and_eq_true, List.all_map, List.all_eq_true]
    refine ⟨fun b hb => ?_, sylK_nodupT hn hL.2⟩
    rw [Function.comp_apply, sylK_tblEq (rep_toTable hn a) (rep_toTable hn b)]
    simpa using hL.1 b hb

private theorem sylK_exists {k : Nat} {f : Nat → Bool} (h : (!allN k fun i => !f i) = true) :
    ∃ i < k, f i = true := by
  by_contra hc
  have hall : allN k (fun i => !f i) = true := sylK_allN.2 fun i hi => by
    cases hfi : f i
    · rfl
    · exact (hc ⟨i, hi, hfi⟩).elim
  rw [hall] at h
  exact absurd h (by decide)

private theorem sylK_all_map {L : List (Equiv.Perm (Fin n))} {p : Table → Bool}
    (h : ∀ x ∈ L, p (toTable x) = true) : (L.map toTable).all p = true :=
  List.all_eq_true.2 fun _ ha => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    exact h x hx

private theorem sylK_any_map {L : List (Equiv.Perm (Fin n))} {p : Table → Bool}
    {x : Equiv.Perm (Fin n)} (hx : x ∈ L) (h : p (toTable x) = true) :
    (L.map toTable).any p = true :=
  List.any_eq_true.2 ⟨_, List.mem_map_of_mem hx, h⟩

theorem sylK_sound {n w r m c : Nat} (hsz : szOK n w = true) {P E₁ E₂ : Nat → Nat}
    {ps : List (Equiv.Perm (Fin n))} {es : List (Equiv.Perm (Fin n) × Equiv.Perm (Fin n))}
    (hm : ps.length = m) (hc : es.length = c)
    (hP : ∀ i < m, PRep n w (P i) (ps.getD i 1) ∧ P i >>> (n * w) = 0)
    (hE : ∀ e < c, PRep n w (E₁ e) (es.getD e (1, 1)).1 ∧ E₁ e >>> (n * w) = 0 ∧
      PRep n w (E₂ e) (es.getD e (1, 1)).2 ∧ E₂ e >>> (n * w) = 0)
    (h : sylK n w r m c P E₁ E₂ = true) :
    cf67NodupT n (ps.map toTable) = true ∧ cf67ClosedT n (ps.map toTable) = true ∧
      cf67CoverT n r (ps.map toTable) (es.map fun e => (toTable e.1, toTable e.2)) = true := by
  have hf := szOK_facts hsz
  have hn := szOK_lt hsz
  have hw := PF.w_pos hf.2
  have pI := prep_pidn hf.1 hf.2
  have sI := PF.pidn_shr hf.1 hf.2
  have hget : ∀ i (hi : i < ps.length), ps.getD i 1 = ps[i] := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have mem : ∀ i < m, ps.getD i 1 ∈ ps := fun i hi => by
    rw [hget i (by omega)]
    exact List.getElem_mem _
  have idx : ∀ x ∈ ps, ∃ i < m, ps.getD i 1 = x := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    exact ⟨i, by omega, hget i hi⟩
  simp only [sylK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_⟩
  ·
    apply sylK_nodupT hn
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hjm : j < m := by omega
    have hne := (sylK_allN.1 ((sylK_allN.1 h1) j hjm)) i hij
    rw [OddWit.beq_eq_decide hw (hP j hjm).1 (hP i (by omega)).1 (hP j hjm).2
      (hP i (by omega)).2, hget j hj, hget i hi] at hne
    have hne' : ps[j] ≠ ps[i] := by simpa using hne
    exact fun e => hne' e.symm
  · rw [cf67ClosedT, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    ·
      obtain ⟨i, hi, he⟩ := sylK_exists h2
      rw [OddWit.beq_eq_decide hw pI (hP i hi).1 sI (hP i hi).2] at he
      refine sylK_any_map (mem i hi) ?_
      rw [sylK_tblEq (Rep.idT hn) (rep_toTable hn _)]
      exact he
    ·
      refine sylK_all_map fun x hx => ?_
      obtain ⟨i, hi, rfl⟩ := idx x hx
      obtain ⟨j, hj, he⟩ := sylK_exists ((sylK_allN.1 h3) i hi)
      rw [OddWit.beq_eq_decide hw (prep_pcomp hn (hP i hi).1 (hP j hj).1) pI
        (PF.pcomp_shr _ _ hn hw) sI] at he
      refine sylK_any_map (mem j hj) ?_
      rw [sylK_tblEq (Rep.compT (rep_toTable hn _) (rep_toTable hn _)) (Rep.idT hn)]
      exact he
    ·
      refine sylK_all_map fun x hx => sylK_all_map fun y hy => ?_
      obtain ⟨i, hi, rfl⟩ := idx x hx
      obtain ⟨j, hj, rfl⟩ := idx y hy
      have hk := (sylK_allN.1 ((sylK_allN.1 h4) i hi)) j hj
      rw [Orb.strictB_eq] at hk
      obtain ⟨k, hk, he⟩ := sylK_exists hk
      rw [OddWit.beq_eq_decide hw (prep_pcomp hn (hP i hi).1 (hP j hj).1) (hP k hk).1
        (PF.pcomp_shr _ _ hn hw) (hP k hk).2] at he
      refine sylK_any_map (mem k hk) ?_
      rw [sylK_tblEq (Rep.compT (rep_toTable hn _) (rep_toTable hn _)) (rep_toTable hn _)]
      exact he
  ·
    rw [cf67CoverT]
    refine sylK_all_map fun x hx => sylK_all_map fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := idx x hx
    obtain ⟨j, hj, rfl⟩ := idx y hy
    rw [← sylK_isPair hsz (hP i hi).1 (hP i hi).2 (hP j hj).1 (hP j hj).2]
    have h5' := (sylK_allN.1 ((sylK_allN.1 h5) i hi)) j hj
    cases hpk : isPairK n w r (P i) (P j)
    · rfl
    · rw [hpk, Bool.not_true, Bool.false_or] at h5'
      obtain ⟨e, he, hboth⟩ := sylK_exists h5'
      rw [Bool.and_eq_true] at hboth
      have g1 := sylK_inGen hsz (hP i hi).1 (hP j hj).1 (hE e he).1 (hE e he).2.1 r hboth.1
      have g2 := sylK_inGen hsz (hP i hi).1 (hP j hj).1 (hE e he).2.2.1 (hE e he).2.2.2 r hboth.2
      have heM : es.getD e (1, 1) ∈ es := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact List.getElem_mem _
      rw [Bool.not_true, Bool.false_or]
      exact List.any_eq_true.2 ⟨_, List.mem_map_of_mem heM,
        Bool.and_eq_true_iff.2 ⟨sylK_gen hn g1, sylK_gen hn g2⟩⟩

end CFSG.KS.SporSch.CF67K

end

module

public import Certificates.Data.Kernel.TabWordK
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Make
public import CFSG.Certificates.Kernel.Spor.VOrbSound

public section

namespace CFSG.KC.TabWord

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.Sporadic.Th.Native

theorem fdN_eq (w x i : Nat) : fdN w x i = fd w x i := rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem fd_pidn {n w : Nat} (hn : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w) {x : Nat} (hx : x < n) :
    fd w (pidn n w) x = x := by
  rw [pidn_eq hn hw]
  exact fd_enc (fun i hi => Nat.lt_of_lt_of_le hi hw) hx

theorem fd_pmk {n w : Nat} {f : Nat → Nat} (hn : n ≤ 2 ^ 24) (hf : ∀ i < n, f i < 2 ^ w) {x : Nat}
    (hx : x < n) : fd w (pmk n w f) x = f x := by
  rw [pmk_eq hn hf]
  exact fd_enc hf hx

theorem fd_packU {w : Nat} {l : List UInt32} (hl : ∀ x ∈ l, x.toNat < 2 ^ w) {x : Nat}
    (hx : x < l.length) : fd w (CFSG.KS.Mathieu.packU w l) x = (l.getD x 0).toNat := by
  rw [packU_eq hl]
  exact fd_enc (fun i _ => by
    rcases Nat.lt_or_ge i l.length with h | h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
      exact hl _ (List.getElem_mem h)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]
      simpa using Nat.two_pow_pos w) hx

theorem allLtU_spec {n : Nat} : ∀ {l : List UInt32}, CFSG.KS.Mathieu.allLtU n l = true →
    ∀ y ∈ l, y.toNat < n
  | [], _, y, hy => absurd hy List.not_mem_nil
  | x :: l, h, y, hy => by
    have e : CFSG.KS.Mathieu.allLtU n (x :: l) = (Nat.blt x.toNat n && CFSG.KS.Mathieu.allLtU n l) := by
      change Bool.rec (motive := fun _ => Bool) false (CFSG.KS.Mathieu.allLtU n l)
        (Nat.blt x.toNat n) = _
      cases Nat.blt x.toNat n <;> rfl
    rw [e, Bool.and_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1
    · exact allLtU_spec h.2 y hy

theorem ite_pair {p : Prop} [Decidable p] {Q : Table → Nat → Prop} {T T' : Table} {L L' : Nat}
    (h : Q T L) (h' : Q T' L') : Q (if p then T else T') (if p then L else L') := by
  split
  exacts [h, h']

theorem ap_packU {w : Nat} {t : Table} (hl : ∀ y ∈ t.toList, y.toNat < 2 ^ w) {x : Nat}
    (hx : x < t.size) : ap t x = fd w (CFSG.KS.Mathieu.packU w t.toList) x := by
  rw [fd_packU hl (by simpa using hx), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using hx), Option.getD_some, Array.getElem_toList]
  unfold ap
  rw [getElem!_pos t x hx]

theorem fd_wordK {n w idn : Nat} (hn : n < 2 ^ 32) (hid : ∀ x < n, fd w idn x = x)
    (L : Int → Nat) : ∀ (u : List Int) {x : Nat}, x < n →
      fd w (wordK n w idn L u) x = u.foldr (fun z y => fd w (L z) y) x
  | [], x, hx => hid x hx
  | z :: u, x, hx => by
    have e : wordK n w idn L (z :: u) = pcomp n w (mask w) (L z) (wordK n w idn L u) := by
      unfold wordK
      exact strictN_eq' _ _
    rw [e, fd_pcomp hn _ _ _ hx, fd_wordK hn hid L u hx, List.foldr_cons]

theorem allLtK_spec {n w P : Nat} : ∀ {k : Nat}, allLtK n w P k = true → ∀ i < k, fd w P i < n
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, h, i, hi => by
    unfold allLtK at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact allLtK_spec h.1 i hi
    · exact h.2

theorem fd_inv {n w idn V P : Nat} (hn : n < 2 ^ 32) (hid : ∀ x < n, fd w idn x = x)
    (h : Nat.beq (pcomp n w (mask w) V P) idn = true) {x : Nat} (hx : x < n) :
    fd w V (fd w P x) = x := by
  rw [← fd_pcomp hn w V P hx, Nat.eq_of_beq_eq_true h, hid x hx]

theorem wordT_fd {n w idn : Nat} (hn : n < 2 ^ 32) (hid : ∀ x < n, fd w idn x = x)
    {gens : Int → Table} {L : Int → Nat}
    (hg : ∀ z, ∀ x < n, ap (gens z) x = fd w (L z) x ∧ fd w (L z) x < n) (u : List Int) :
    (wordT n gens u).size = n ∧
      ∀ x < n, ap (wordT n gens u) x = fd w (wordK n w idn L u) x ∧ fd w (wordK n w idn L u) x < n := by
  obtain ⟨hs, hv⟩ := CFSG.KS.VO.wordT_ap (G := fun z y => fd w (L z) y) hn hg u
  refine ⟨hs, fun x hx => ?_⟩
  rw [fd_wordK hn hid L u hx]
  exact hv x hx

theorem idT_size (n : Nat) : (idT n).size = n := by simp [idT]

theorem ap_idT {n : Nat} (hn : n < 2 ^ 32) {x : Nat} (hx : x < n) : ap (idT n) x = x := by
  unfold ap idT
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem beq_of_ap {n : Nat} {A B : Table} (hA : A.size = n) (hB : B.size = n)
    (h : ∀ x < n, ap A x = ap B x) : (A == B) = true := by
  rw [beq_iff_eq]
  refine Array.ext (by rw [hA, hB]) fun i hi hi' => ?_
  have e := h i (by omega)
  unfold ap at e
  rw [getElem!_pos A i hi, getElem!_pos B i hi'] at e
  exact UInt32.toNat_inj.1 e

theorem wordT_beq_idT {n w idn : Nat} (hn : n < 2 ^ 32) (hid : ∀ x < n, fd w idn x = x)
    {gens : Int → Table} {L : Int → Nat}
    (hg : ∀ z, ∀ x < n, ap (gens z) x = fd w (L z) x ∧ fd w (L z) x < n) {u : List Int}
    (h : Nat.beq (wordK n w idn L u) idn = true) : (wordT n gens u == idT n) = true := by
  obtain ⟨hs, hv⟩ := wordT_fd hn hid hg u
  refine beq_of_ap hs (idT_size n) fun x hx => ?_
  rw [(hv x hx).1, Nat.eq_of_beq_eq_true h, hid x hx, ap_idT hn hx]

theorem wordT_beq {n w idn : Nat} (hn : n < 2 ^ 32) (hid : ∀ x < n, fd w idn x = x)
    {gens : Int → Table} {L : Int → Nat}
    (hg : ∀ z, ∀ x < n, ap (gens z) x = fd w (L z) x ∧ fd w (L z) x < n) {u : List Int}
    {B : Table} {PB : Nat} (hB : B.size = n) (hPB : ∀ x < n, ap B x = fd w PB x)
    (h : Nat.beq (wordK n w idn L u) PB = true) : (wordT n gens u == B) = true := by
  obtain ⟨hs, hv⟩ := wordT_fd hn hid hg u
  refine beq_of_ap hs hB fun x hx => ?_
  rw [(hv x hx).1, Nat.eq_of_beq_eq_true h, hPB x hx]

theorem gen_facts {n w idn : Nat} (hn : n < 2 ^ 32) (hid : ∀ x < n, fd w idn x = x)
    {gens : Int → Table} {L : Int → Nat}
    (hg : ∀ z, ∀ x < n, ap (gens z) x = fd w (L z) x ∧ fd w (L z) x < n) (u : List Int) {V : Nat}
    (hV : allLtK n w V n = true)
    (hinv : Nat.beq (pcomp n w (mask w) V (wordK n w idn L u)) idn = true) :
    (∀ x < n, ap (wordT n gens u) x = fd w (wordK n w idn L u) x ∧
        fd w (wordK n w idn L u) x < n) ∧
      invOK n (wordT n gens u) (invT n (wordT n gens u)) = true ∧
      ∀ y < n, ap (invT n (wordT n gens u)) y = fd w V y ∧ fd w V y < n := by
  obtain ⟨-, hv⟩ := wordT_fd hn hid hg u
  obtain ⟨hi, hap⟩ := CFSG.KS.VO.invT_get (f := fun x => fd w (wordK n w idn L u) x)
    (g := fun y => fd w V y) hn fun x hx => ⟨(hv x hx).1, (hv x hx).2, fd_inv hn hid hinv hx⟩
  exact ⟨hv, hi, fun y hy => ⟨hap y hy, allLtK_spec hV y hy⟩⟩

end CFSG.KC.TabWord

end

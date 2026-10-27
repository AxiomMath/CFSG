module

public import Certificates.Data.Kernel.OrbRow.CentB
public import CFSG.Certificates.Kernel.OrbRow.WordRep

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp CFSG.KS

theorem cntK_eq (f : ℕ → Bool) : ∀ L : List ℕ, cntK L f = (L.filter f).length
  | [] => rfl
  | x :: L => by
    change Bool.rec (motive := fun _ => ℕ) (cntK L f) (Nat.succ (cntK L f)) (f x) = _
    rw [List.filter_cons, cntK_eq f L]
    cases f x <;> rfl

theorem cntN_eq (f : ℕ → Bool) : ∀ k : ℕ, cntN k f = ((List.range k).filter f).length
  | 0 => rfl
  | k + 1 => by
    change Bool.rec (motive := fun _ => ℕ) (cntN k f) (Nat.succ (cntN k f)) (f k) = _
    rw [List.range_succ, List.filter_append, List.length_append, cntN_eq f k, List.filter_cons,
      List.filter_nil]
    cases f k <;> rfl

theorem inD_iff (D x : ℕ) : inD D x = true ↔ depD D x ≠ 255 := by
  unfold inD
  cases h : Nat.beq (depD D x) 255
  · exact ⟨fun _ he => by rw [he] at h; exact absurd h (by decide), fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun hne => absurd (Nat.eq_of_beq_eq_true h) hne⟩

theorem degK_sound {n w m : ℕ} {S : List ℕ} {k lv b D : ℕ} {F : List ℕ} {p dg : ℕ}
    {wd : List ℕ} (h : degK n w m S k lv b D F p dg wd = true) :
    (∀ j ∈ wd, j < k ∧ Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1) = true) ∧
      pg w m (posWordK n w (getS S) wd) b = p ∧
      permOK n w m (n * w) (posWordK n w (getS S) wd)
        (CFSG.KS.pinvS n w m (posWordK n w (getS S) wd)) = true ∧
      (F.filter fun q => inD D (pg w m (CFSG.KS.pinvS n w m (posWordK n w (getS S) wd)) q)).length
        = dg := by
  unfold degK at h
  rw [strictB_apply, strictB_apply] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  refine ⟨lettersK_sound h1, Nat.eq_of_beq_eq_true h2, h3, ?_⟩
  rw [← cntK_eq]
  exact Nat.eq_of_beq_eq_true h4

theorem capK_sound {D : ℕ} {F : List ℕ} {c : ℕ} (h : capK D F c = true) :
    (F.filter (inD D)).length = c := by
  rw [← cntK_eq]
  exact Nat.eq_of_beq_eq_true h

private theorem centB_beq (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem centB_lenS : ∀ L : List ℕ, lenS L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (centB_lenS L)

private theorem centB_incK : ∀ {Q : List ℕ} {i prev : ℕ}, incK Q i prev = true →
    Q.Pairwise (· < ·) ∧ (i ≠ 0 → ∀ q ∈ Q, prev < q)
  | [], _, _, _ => ⟨List.Pairwise.nil, fun _ q hq => absurd hq List.not_mem_nil⟩
  | q :: Q, i, prev, h => by
    have h' : bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt prev q),
        incK Q (Nat.succ i) q) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨hs, hp⟩ := centB_incK h2
    refine ⟨List.pairwise_cons.2 ⟨hp (Nat.succ_ne_zero i), hs⟩, fun hi q' hq' => ?_⟩
    have hlt : prev < q := by
      have hb : Nat.beq i (nat_lit 0) = false := by
        cases hh : Nat.beq i (nat_lit 0)
        · rfl
        · exact absurd ((centB_beq _ _).1 hh) hi
      rw [hb] at h1
      exact Nat.le_of_ble_eq_true h1
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact hlt
    · exact Nat.lt_trans hlt (hp (Nat.succ_ne_zero i) q' hq')

theorem incK_sound {Q : List ℕ} (h : incK Q 0 0 = true) : Q.Nodup :=
  (centB_incK h).1.imp fun h => Nat.ne_of_lt h

theorem regK_sound {n w m : ℕ} {S : List ℕ} {k lv b D : ℕ} {Q : List ℕ} {V : List (List ℕ)}
    {cnt x cc : ℕ} (h : regK n w m S k lv b D Q V cnt x cc = true) :
    Q.length = cnt ∧ Q.Nodup ∧
      (∀ t < cnt, inD D (getS Q t) = true ∧
        (∀ j ∈ getLs V t, j < k ∧ Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1) = true) ∧
        pg w m (posWordK n w (getS S) (getLs V t)) b = getS Q t) ∧
      ((List.range cnt).filter fun t => commOK n w m (posWordK n w (getS S) (getLs V t)) x).length
        = cc := by
  unfold regK at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  refine ⟨by rw [← centB_lenS]; exact (centB_beq _ _).1 h1, incK_sound h2, fun t ht => ?_, ?_⟩
  · have h5 := allN_spec h3 t ht
    rw [strictB_apply] at h5
    obtain ⟨h6, h5⟩ := (bAnd_iff _ _).1 h5
    obtain ⟨h7, h8⟩ := (bAnd_iff _ _).1 h5
    exact ⟨h6, lettersK_sound h7, (centB_beq _ _).1 h8⟩
  · rw [← cntN_eq]
    exact (centB_beq _ _).1 h4

theorem rowsK_dep {n w m : ℕ} {S : List ℕ} {k lv D b cnt : ℕ} {R : List ℕ}
    (h : rowsK n w m S k lv D b cnt R = true) :
    ((Finset.range n).filter fun x => depD D x ≠ 255).card = cnt ∧
      ∀ x < n, depD D x ≠ 255 → OrbReach (fun j y => pg w m (getS S j) y) (lvOk k lv) b x :=
  rowsK_depth h

end CFSG.KC.OrbRow

end

module

public import CFSG.Certificates.Kernel.Spor.PK.Ord
public import Certificates.Data.Kernel.Spor.M11Class
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Make

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.M11Class

theorem lenN_eq (l : List Nat) : CFSG.KS.Mathieu.lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show Nat.succ (CFSG.KS.Mathieu.lenN l) = (x :: l).length
    rw [ih]
    rfl

theorem cntL_eq (p : Nat → Bool) (L : List Nat) : cntL p L = L.countP p := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    show strictN (cntL p L) (fun s => nIf(p x, Nat.succ s, s)) = _
    rw [strictN_eq, nIf_eq, ih, List.countP_cons]
    by_cases h : p x = true <;> simp [h]

theorem allL_iff (p : Nat → Bool) (L : List Nat) : allL p L = true ↔ ∀ x ∈ L, p x = true := by
  unfold allL
  rw [Nat.beq_eq, cntL_eq, lenN_eq, List.countP_eq_length]

theorem cntP_eq (p : Nat → Nat → Bool) (L : List (Nat × Nat)) :
    cntP p L = L.countP fun q => p q.1 q.2 := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    obtain ⟨x, xi⟩ := q
    show strictN (cntP p L) (fun s => nIf(p x xi, Nat.succ s, s)) = _
    rw [strictN_eq, nIf_eq, ih, List.countP_cons]
    by_cases h : p x xi = true <;> simp [h]

theorem lenP_eq (L : List (Nat × Nat)) : lenP L = L.length := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    show strictN (lenP L) (fun s => Nat.succ s) = _
    rw [strictN_eq, ih]
    rfl

theorem allP_iff (p : Nat → Nat → Bool) (L : List (Nat × Nat)) :
    allP p L = true ↔ ∀ q ∈ L, p q.1 q.2 = true := by
  unfold allP
  rw [Nat.beq_eq, cntP_eq, lenP_eq, List.countP_eq_length]

theorem rowCnt_eq (x xi : Nat) (Y : List (Nat × Nat)) :
    rowCnt x xi Y = Y.countP fun q => CFSG.KS.M11.pairOK x xi q.1 q.2 := by
  induction Y with
  | nil => rfl
  | cons q Y ih =>
    obtain ⟨y, yi⟩ := q
    show strictN (rowCnt x xi Y) (fun s => nIf(CFSG.KS.M11.pairOK x xi y yi, Nat.succ s, s)) = _
    rw [strictN_eq, nIf_eq, ih, List.countP_cons]
    by_cases h : CFSG.KS.M11.pairOK x xi y yi = true <;> simp [h]

theorem pairCntL_eq (X Y : List (Nat × Nat)) :
    pairCntL X Y = (X.map fun q => rowCnt q.1 q.2 Y).sum := by
  induction X with
  | nil => rfl
  | cons q X ih =>
    obtain ⟨x, xi⟩ := q
    show Nat.add (rowCnt x xi Y) (pairCntL X Y) = _
    rw [ih, List.map_cons, List.sum_cons]
    rfl

theorem pcomp11_eq (p q : Nat) :
    pcomp 11 4 15 p q = enc 4 (fun i => fd 4 p (fd 4 q i)) 11 := by
  have h : (15 : Nat) = mask 4 := rfl
  rw [h]
  exact pcomp_eq (by decide) 4 p q

private theorem fd_pcomp11 (p q i : Nat) (hi : i < 11) :
    fd 4 (pcomp 11 4 15 p q) i = fd 4 p (fd 4 q i) := by
  rw [pcomp11_eq]
  exact fd_enc (fun j _ => fd_lt _ _ _) hi

private theorem enc_eq_iff {w len : Nat} {f g : Nat → Nat} (hf : ∀ i < len, f i < 2 ^ w)
    (hg : ∀ i < len, g i < 2 ^ w) : enc w f len = enc w g len ↔ ∀ i < len, f i = g i :=
  ⟨fun h i hi => by rw [← fd_enc hf hi, ← fd_enc hg hi, h], fun h => enc_congr h⟩

private theorem pg4 (x i : Nat) : pg (nat_lit 4) (nat_lit 15) x i = fd 4 x i := pg_eq 4 x i

private theorem pidn11 : pidn 11 4 = enc 4 (fun i => i) 11 := pidn_eq (by decide) (by decide)

theorem invPair_iff {x xi : Nat} :
    invPair (pidn 11 4) x xi = true ↔ (∀ i < 11, fd 4 x i < 11 ∧ fd 4 xi i < 11) ∧
      (∀ i < 11, fd 4 x (fd 4 xi i) = i) ∧ ∀ i < 11, fd 4 xi (fd 4 x i) = i := by
  unfold invPair
  simp only [bAnd_eq, Bool.and_eq_true, allN_iff, Nat.blt_eq, Nat.beq_eq, pg4, pcomp11_eq, pidn11]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (enc_eq_iff (fun i _ => fd_lt _ _ _) (fun i hi => by omega)).1 h2,
      (enc_eq_iff (fun i _ => fd_lt _ _ _) (fun i hi => by omega)).1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, enc_congr h2, enc_congr h3⟩

theorem invPair_perm {x xi : Nat} (h : invPair (pidn 11 4) x xi = true) :
    IsPermN 11 (fd 4 x) ∧ ∀ i < 11, fd 4 xi i = finv 11 (fd 4 x) i := by
  obtain ⟨hlt, hxxi, hxix⟩ := invPair_iff.1 h
  have hperm : IsPermN 11 (fd 4 x) :=
    ⟨fun i hi => (hlt i hi).1, fun a ha b hb hab => by
      rw [← hxix a ha, ← hxix b hb, hab]⟩
  refine ⟨hperm, fun i hi => ?_⟩
  have := finv_apply hperm (x := fd 4 xi i) (hlt i hi).2
  rw [hxxi i hi] at this
  exact this.symm

theorem conjK_eq (g gi x : Nat) :
    conjK 11 4 15 g gi x = enc 4 (fun i => fd 4 g (fd 4 x (fd 4 gi i))) 11 := by
  unfold conjK
  rw [pcomp11_eq, pcomp11_eq]
  refine enc_congr fun i hi => ?_
  rw [fd_enc (fun j _ => fd_lt _ _ _) hi]

private theorem ordC11 (z : Nat) :
    ordC (nat_lit 11) (nat_lit 4) (nat_lit 15) z = ordF 11 (fd 4 z) :=
  ordC_eq 11 4 z

private theorem nbeq (a b : Nat) : Nat.beq a b = (a == b) := by
  apply Bool.eq_iff_iff.2
  simp [Nat.beq_eq]

theorem pairOK_eq {x xi y yi : Nat} (hx : invPair (pidn 11 4) x xi = true)
    (hy : invPair (pidn 11 4) y yi = true) :
    CFSG.KS.M11.pairOK x xi y yi =
      (ordF 11 (fun i => fd 4 x (fd 4 y i)) == 11 &&
        ordF 11 (fun i => fd 4 x (fd 4 y (finv 11 (fd 4 x) (finv 11 (fd 4 y) i)))) == 6) := by
  obtain ⟨hxp, hxi⟩ := invPair_perm hx
  obtain ⟨hyp, hyi⟩ := invPair_perm hy
  obtain ⟨hylt, -, -⟩ := invPair_iff.1 hy
  have e1 : ordF 11 (fd 4 (pcomp 11 4 15 x y)) = ordF 11 (fun i => fd 4 x (fd 4 y i)) := by
    refine ordF_congr (fun i hi => ?_) (fun i hi => fd_pcomp11 x y i hi)
    rw [fd_pcomp11 x y i hi]
    exact hxp.1 _ (hyp.1 i hi)
  have e2 : ordF 11 (fd 4 (pcomp 11 4 15 x (pcomp 11 4 15 y (pcomp 11 4 15 xi yi)))) =
      ordF 11 (fun i => fd 4 x (fd 4 y (finv 11 (fd 4 x) (finv 11 (fd 4 y) i)))) := by
    have key : ∀ i < 11, fd 4 (pcomp 11 4 15 x (pcomp 11 4 15 y (pcomp 11 4 15 xi yi))) i =
        fd 4 x (fd 4 y (finv 11 (fd 4 x) (finv 11 (fd 4 y) i))) := by
      intro i hi
      rw [fd_pcomp11 _ _ _ hi, fd_pcomp11 _ _ _ hi, fd_pcomp11 _ _ _ hi, hxi _ (hylt i hi).2,
        hyi i hi]
    refine ordF_congr (fun i hi => ?_) key
    rw [key i hi]
    exact hxp.1 _ (hyp.1 _ (finv_spec hxp (finv_spec hyp hi).1).1)
  unfold CFSG.KS.M11.pairOK
  rw [bAnd_eq, ordC11, ordC11, e1, e2, nbeq, nbeq]

end CFSG.KS.PK

end

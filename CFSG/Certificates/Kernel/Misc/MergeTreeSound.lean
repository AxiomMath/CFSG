module

public import Certificates.Data.Kernel.Misc.MergeTree
public import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.MTree

open CFSG.KC.Enum CFSG.Certificates
open CFSG.KS (mask bAnd_iff allN_spec)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem bIf_false {c t e : Bool} (hc : c = false) (h : bIf(c, t, e) = true) : e = true := by
  subst hc
  exact h

theorem bIf_true {c t e : Bool} (hc : c = true) (h : bIf(c, t, e) = true) : t = true := by
  subst hc
  exact h

theorem beq_false {a c : Nat} (h : a ≠ c) : Nat.beq a c = false := by
  cases e : Nat.beq a c
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem pairEq_spec {a c p q : Nat} (h : pairEq a c p q = true) :
    (a = p ∧ c = q) ∨ (a = q ∧ c = p) := by
  unfold pairEq at h
  by_cases e1 : a = p ∧ c = q
  · exact Or.inl e1
  · right
    have h0 : bAnd(Nat.beq a p, Nat.beq c q) = false := by
      cases h1 : Nat.beq a p
      · rfl
      · cases h2 : Nat.beq c q
        · rfl
        · exact absurd ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩ e1
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 (bIf_false h0 h)
    exact ⟨Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

variable {n m w : ℕ} {S : Fin m → Equiv.Perm (Fin n)} {b x : Fin n}
  {L : List (Fin m × Fin n × Fin n)}

theorem rel_equivalence : ∀ k, Equivalence (mergeRel S b x L k)
  | 0 => Relation.EqvGen.is_equivalence _
  | k + 1 => by
    unfold mergeRel
    split
    · exact Relation.EqvGen.is_equivalence _
    · exact rel_equivalence k

theorem rel_succ {k : ℕ} {a c : Fin n} (h : mergeRel S b x L k a c) :
    mergeRel S b x L (k + 1) a c := by
  rcases hk : L[k]? with _ | ⟨i, u, v⟩
  · simp only [mergeRel, hk]
    exact h
  · simp only [mergeRel, hk]
    exact Relation.EqvGen.rel _ _ (Or.inl h)

theorem rel_mono {k k' : ℕ} (hk : k ≤ k') {a c : Fin n} (h : mergeRel S b x L k a c) :
    mergeRel S b x L k' a c := by
  induction k', hk using Nat.le_induction with
  | base => exact h
  | succ k' _ ih => exact rel_succ ih

variable {GP I U V : ℕ → ℕ} {nI : ℕ} {par tim dep : ℕ → ℕ} {root : ℕ}

theorem edge_rel (hS : ∀ (i : Fin m) (y : Fin n), pg w (mask w) (GP i) y = (S i y : ℕ))
    (hL : L.length = nI)
    (hI : ∀ k (hk : k < L.length), I k = ((L[k]).1 : ℕ) ∧ U k = ((L[k]).2.1 : ℕ) ∧
      V k = ((L[k]).2.2 : ℕ))
    {p : ℕ} (hp : p < n) (hpr : p ≠ root)
    (he : edgeOK n w GP I U V nI b x par tim dep root p = true) :
    ∃ hq : par p < n, tim p ≤ nI ∧ dep p = dep (par p) + 1 ∧
      mergeRel S b x L (tim p) ⟨p, hp⟩ ⟨par p, hq⟩ := by
  unfold edgeOK at he
  have he1 := bIf_false (beq_false hpr) he
  rw [strictB_eq, strictB_eq] at he1
  obtain ⟨hq, he2⟩ := (bAnd_iff _ _).1 he1
  obtain ⟨hd, he3⟩ := (bAnd_iff _ _).1 he2
  have hq' : par p < n := Nat.blt_eq.mp hq
  refine ⟨hq', ?_⟩
  have hd' : dep p = dep (par p) + 1 := Nat.eq_of_beq_eq_true hd
  by_cases ht : tim p = 0
  · have hpe := pairEq_spec (bIf_true (by rw [ht]; rfl) he3)
    refine ⟨by omega, hd', ?_⟩
    rw [ht]
    rcases hpe with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have ea : (⟨p, hp⟩ : Fin n) = b := Fin.ext e1
      have ec : (⟨par p, hq'⟩ : Fin n) = x := Fin.ext e2
      rw [ea, ec]
      exact Relation.EqvGen.rel _ _ ⟨rfl, rfl⟩
    · have ea : (⟨p, hp⟩ : Fin n) = x := Fin.ext e1
      have ec : (⟨par p, hq'⟩ : Fin n) = b := Fin.ext e2
      rw [ea, ec]
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨rfl, rfl⟩)
  · have he4 := bIf_false (beq_false ht) he3
    obtain ⟨hle, he5⟩ := (bAnd_iff _ _).1 he4
    rw [strictB_eq, strictB_eq] at he5
    have hle' : tim p ≤ nI := Nat.le_of_ble_eq_true hle
    refine ⟨hle', hd', ?_⟩
    have hk : tim p - 1 < L.length := by omega
    have es : Nat.sub (tim p) (nat_lit 1) = tim p - 1 := rfl
    rw [es] at he5
    obtain ⟨e1, e2, e3⟩ := hI _ hk
    rw [e1, e2, e3, hS, hS] at he5
    have hpe := pairEq_spec he5
    have et : tim p = tim p - 1 + 1 := by omega
    rw [et, mergeRel_succ_of_lt hk]
    rcases hpe with ⟨f1, f2⟩ | ⟨f1, f2⟩
    · have ea : (⟨p, hp⟩ : Fin n) = S (L[tim p - 1]).1 (L[tim p - 1]).2.1 := Fin.ext f1
      have ec : (⟨par p, hq'⟩ : Fin n) = S (L[tim p - 1]).1 (L[tim p - 1]).2.2 := Fin.ext f2
      rw [ea, ec]
      exact Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
    · have ea : (⟨p, hp⟩ : Fin n) = S (L[tim p - 1]).1 (L[tim p - 1]).2.2 := Fin.ext f1
      have ec : (⟨par p, hq'⟩ : Fin n) = S (L[tim p - 1]).1 (L[tim p - 1]).2.1 := Fin.ext f2
      rw [ea, ec]
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩))

theorem topK_rel (hS : ∀ (i : Fin m) (y : Fin n), pg w (mask w) (GP i) y = (S i y : ℕ))
    (hL : L.length = nI)
    (hI : ∀ k (hk : k < L.length), I k = ((L[k]).1 : ℕ) ∧ U k = ((L[k]).2.1 : ℕ) ∧
      V k = ((L[k]).2.2 : ℕ))
    (hall : ∀ p < n, edgeOK n w GP I U V nI b x par tim dep root p = true) (k : ℕ) :
    ∀ fuel p (hp : p < n), ∃ h : topK par tim root k fuel p < n,
      mergeRel S b x L k ⟨p, hp⟩ ⟨topK par tim root k fuel p, h⟩
  | 0, p, hp => ⟨hp, (rel_equivalence k).refl _⟩
  | fuel + 1, p, hp => by
    have e : topK par tim root k (fuel + 1) p =
        nIf(bIf(Nat.beq p root, true, Nat.blt k (tim p)), p,
          strictN (par p) (topK par tim root k fuel)) := rfl
    by_cases hc : bIf(Nat.beq p root, true, Nat.blt k (tim p)) = true
    · rw [e, hc]
      exact ⟨hp, (rel_equivalence k).refl _⟩
    · have hpr : p ≠ root := fun h => hc (by rw [h, Nat.beq_refl])
      have hc' : ¬ Nat.blt k (tim p) = true := by
        rw [beq_false hpr] at hc
        exact hc
      have htk : tim p ≤ k := Nat.le_of_not_lt fun h => hc' (Nat.blt_eq.mpr h)
      rw [e, Bool.eq_false_iff.2 hc, strictN_eq]
      obtain ⟨hq, -, -, hrel⟩ := edge_rel hS hL hI hp hpr (hall p hp)
      obtain ⟨ht, hrel'⟩ := topK_rel hS hL hI hall k fuel (par p) hq
      exact ⟨ht, (rel_equivalence k).trans (rel_mono htk hrel) hrel'⟩

theorem valid_of_mtOK (hS : ∀ (i : Fin m) (y : Fin n), pg w (mask w) (GP i) y = (S i y : ℕ))
    (hL : L.length = nI)
    (hI : ∀ k (hk : k < L.length), I k = ((L[k]).1 : ℕ) ∧ U k = ((L[k]).2.1 : ℕ) ∧
      V k = ((L[k]).2.2 : ℕ))
    (h : mtOK n w GP I U V nI b x par tim dep root = true) : ValidInvariantMerge S b x L := by
  unfold mtOK at h
  obtain ⟨hr, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨he, hw⟩ := (bAnd_iff _ _).1 h2
  have hall := allN_spec he
  have hwalk := allN_spec hw
  have hroot : root < n := Nat.blt_eq.mp hr
  refine ⟨fun k hk => ?_, fun a c => ?_⟩
  · obtain ⟨-, e2, e3⟩ := hI k hk
    have hmeet := Nat.eq_of_beq_eq_true (hwalk k (by omega))
    have hu : U k < n := by rw [e2]; exact Fin.isLt _
    have hv : V k < n := by rw [e3]; exact Fin.isLt _
    obtain ⟨t1, r1⟩ := topK_rel hS hL hI hall k n (U k) hu
    obtain ⟨t2, r2⟩ := topK_rel hS hL hI hall k n (V k) hv
    have eu : (⟨U k, hu⟩ : Fin n) = (L[k]).2.1 := Fin.ext e2
    have ev : (⟨V k, hv⟩ : Fin n) = (L[k]).2.2 := Fin.ext e3
    have et : (⟨topK par tim root k n (U k), t1⟩ : Fin n) = ⟨topK par tim root k n (V k), t2⟩ :=
      Fin.ext hmeet
    rw [eu, et] at r1
    rw [ev] at r2
    exact (rel_equivalence k).trans r1 ((rel_equivalence k).symm r2)
  · have hR := rel_equivalence (S := S) (b := b) (x := x) (L := L) L.length
    have key : ∀ d, ∀ p (hp : p < n), dep p = d →
        mergeRel S b x L L.length ⟨p, hp⟩ ⟨root, hroot⟩ := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro p hp hd
        by_cases hpr : p = root
        · subst hpr
          exact hR.refl _
        · obtain ⟨hq, hle, hdq, hrel⟩ := edge_rel hS hL hI hp hpr (hall p hp)
          have h1 := ih (dep (par p)) (by omega) (par p) hq rfl
          exact hR.trans (rel_mono (by omega) hrel) h1
    exact hR.trans (key _ a a.isLt rfl) (hR.symm (key _ c c.isLt rfl))

end CFSG.KC.MTree

end

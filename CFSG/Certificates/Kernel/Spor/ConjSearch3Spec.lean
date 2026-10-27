module

public import Certificates.Data.CFSGNative.Schreier.Enum3
public import CFSG.Certificates.Kernel.SporSch.KeySearch

public section

namespace CFSG.KS.Raw.CS3

open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.KS.SporSch.KeySearch (forIn_range'_ind push_lt push_eq)

abbrev Tri := Nat × Nat × Nat

@[expose] def InR (L : Array Level) (x : Tri) : Prop :=
  x.1 < L[0]!.pts.size ∧ x.2.1 < L[1]!.pts.size ∧ x.2.2 < L[2]!.pts.size

@[expose] def sz (L : Array Level) : Nat := L[0]!.pts.size * L[1]!.pts.size * L[2]!.pts.size

@[expose] def dec (L : Array Level) (i : Nat) : Tri :=
  (i / (L[1]!.pts.size * L[2]!.pts.size), i / L[2]!.pts.size % L[1]!.pts.size,
    i % L[2]!.pts.size)

@[expose] def Agr (n : Nat) (L : Array Level) (g : Array Nat) (x : Tri) : Prop :=
  ∀ p < n, g[p]! = tr3 L x.1 x.2.1 x.2.2 p

@[expose] def conjA (n : Nat) (L : Array Level) (gens : Array (Array Nat)) (k : Nat) (x : Tri) :
    Array Nat :=
  compA n gens[k]! (compA n (prod3 n L x.1 x.2.1 x.2.2) (gens.map (invCand n))[k]!)

@[expose] def Valid (n : Nat) (L : Array Level) (us : Array (Array Nat)) (x : Tri) (j : Nat)
    (t : Tri) : Prop :=
  j < us.size ∧ InR L t ∧ conjOK3 L n us[j]! x.1 x.2.1 x.2.2 t.1 t.2.1 t.2.2 = true

structure Hyp (n : Nat) (L : Array Level) (base : Array Nat) (gens us : Array (Array Nat)) :
    Prop where
  pos : InR L (0, 0, 0)
  tr0 : ∀ p < n, tr3 L 0 0 0 p = p
  trlt : ∀ x, InR L x → ∀ p < n, tr3 L x.1 x.2.1 x.2.2 p < n
  coord : ∀ g x, InR L x → Agr n L g x → coords3 n L base g = x
  us : ∀ j < us.size, ∃ x, InR L x ∧ Agr n L us[j]! x
  conj : ∀ x, InR L x → ∀ k < gens.size, ∃ y, InR L y ∧ Agr n L (conjA n L gens k x) y
  mul : ∀ t, InR L t → ∀ k < gens.size, ∃ y, InR L y ∧
    Agr n L (compA n gens[k]! (prod3 n L t.1 t.2.1 t.2.2)) y
  invlt : ∀ k < gens.size, ∀ p < n, ((gens.map (invCand n))[k]!)[p]! < n
  inv : ∀ k < gens.size, ∀ p < n, ((gens.map (invCand n))[k]!)[(gens[k]!)[p]!]! = p

theorem idx_lt {L : Array Level} {x : Tri} (h : InR L x) : idx3 L x < sz L := by
  obtain ⟨h0, h1, h2⟩ := h
  unfold idx3 sz
  have a : (x.1 * L[1]!.pts.size + x.2.1) < L[0]!.pts.size * L[1]!.pts.size := by
    have := Nat.mul_le_mul_right (L[1]!.pts.size) (Nat.succ_le_of_lt h0)
    rw [Nat.succ_mul] at this
    omega
  have := Nat.mul_le_mul_right (L[2]!.pts.size) (Nat.succ_le_of_lt a)
  rw [Nat.succ_mul] at this
  omega

theorem dec_idx {L : Array Level} {x : Tri} (h : InR L x) : dec L (idx3 L x) = x := by
  obtain ⟨h0, h1, h2⟩ := h
  obtain ⟨a, b, c⟩ := x
  simp only at h0 h1 h2
  unfold dec idx3
  simp only
  have hc : ((a * L[1]!.pts.size + b) * L[2]!.pts.size + c) % L[2]!.pts.size = c := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
  have hq : ((a * L[1]!.pts.size + b) * L[2]!.pts.size + c) / L[2]!.pts.size =
      a * L[1]!.pts.size + b := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt h2, Nat.add_zero]
  have hb : (a * L[1]!.pts.size + b) % L[1]!.pts.size = b := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt h1]
  have ha : ((a * L[1]!.pts.size + b) * L[2]!.pts.size + c) / (L[1]!.pts.size * L[2]!.pts.size) =
      a := by
    rw [Nat.mul_comm (L[1]!.pts.size), ← Nat.div_div_eq_div_mul, hq, Nat.mul_comm,
      Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt h1, Nat.add_zero]
  rw [ha, hq, hb, hc]

theorem inR_dec {L : Array Level} {i : Nat} (h : i < sz L) : InR L (dec L i) := by
  unfold sz at h
  unfold dec InR
  simp only
  have h1 : 0 < L[1]!.pts.size := by
    rcases Nat.eq_zero_or_pos L[1]!.pts.size with e | e
    · rw [e] at h
      simp at h
    · exact e
  have h2 : 0 < L[2]!.pts.size := by
    rcases Nat.eq_zero_or_pos L[2]!.pts.size with e | e
    · rw [e] at h
      simp at h
    · exact e
  refine ⟨?_, Nat.mod_lt _ h1, Nat.mod_lt _ h2⟩
  rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos h1 h2), ← Nat.mul_assoc]
  exact h

theorem set_eq {α : Type} [Inhabited α] {a : Array α} {i : Nat} {v : α} (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ i (by simpa using h),
    Array.getElem_setIfInBounds_self]

theorem set_ne {α : Type} [Inhabited α] {a : Array α} {i j : Nat} {v : α} (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos a j hj, Array.getElem_setIfInBounds]
    all_goals simp [h, hj]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j hj]

theorem size_set {α : Type} {a : Array α} {i : Nat} {v : α} : (a.set! i v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem rep_get {α : Type} [Inhabited α] {S i : Nat} {v : α} (h : i < S) :
    (Array.replicate S v)[i]! = v := by
  rw [getElem!_pos _ i (by simpa using h), Array.getElem_replicate]

theorem prod3_get {n : Nat} {L : Array Level} {a b c p : Nat} (hp : p < n) :
    (prod3 n L a b c)[p]! = tr3 L a b c p := by
  rw [prod3, getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn]

section

variable {n : Nat} {L : Array Level} {base : Array Nat} {gens us : Array (Array Nat)}

theorem us_lt (H : Hyp n L base gens us) {j : Nat} (hj : j < us.size) {p : Nat} (hp : p < n) :
    (us[j]!)[p]! < n := by
  obtain ⟨x, hx, ha⟩ := H.us j hj
  rw [ha p hp]
  exact H.trlt x hx p hp

theorem valid_root (H : Hyp n L base gens us) {j : Nat} (hj : j < us.size) {x : Tri}
    (hx : Agr n L us[j]! x) : Valid n L us x j (0, 0, 0) := by
  refine ⟨hj, H.pos, allLt_iff.2 fun p hp => ?_⟩
  rw [beq_iff_eq, H.tr0 _ (us_lt H hj hp), H.tr0 p hp, hx p hp]

theorem valid_child (H : Hyp n L base gens us) {x y t t' : Tri} {j k : Nat}
    (hk : k < gens.size) (hv : Valid n L us x j t) (hx : InR L x)
    (hy : Agr n L (conjA n L gens k x) y)
    (ht' : Agr n L (compA n gens[k]! (prod3 n L t.1 t.2.1 t.2.2)) t') (hy' : InR L y)
    (hti : InR L t') : Valid n L us y j t' := by
  obtain ⟨hj, ht, hok⟩ := hv
  refine ⟨hj, hti, allLt_iff.2 fun p hp => ?_⟩
  rw [beq_iff_eq]
  have hu := us_lt H hj hp
  have htp := H.trlt t ht p hp
  have e1 : tr3 L t'.1 t'.2.1 t'.2.2 (us[j]!)[p]! = (gens[k]!)[tr3 L t.1 t.2.1 t.2.2 (us[j]!)[p]!]! := by
    rw [← ht' _ hu, compA_get hu, prod3_get hu]
  have e2 : tr3 L t'.1 t'.2.1 t'.2.2 p = (gens[k]!)[tr3 L t.1 t.2.1 t.2.2 p]! := by
    rw [← ht' _ hp, compA_get hp, prod3_get hp]
  have hgl : (gens[k]!)[tr3 L t.1 t.2.1 t.2.2 p]! < n := by
    rw [← e2]
    exact H.trlt t' hti p hp
  have e3 : tr3 L y.1 y.2.1 y.2.2 ((gens[k]!)[tr3 L t.1 t.2.1 t.2.2 p]!) =
      (gens[k]!)[tr3 L x.1 x.2.1 x.2.2 (tr3 L t.1 t.2.1 t.2.2 p)]! := by
    rw [← hy _ hgl, conjA, compA_get hgl, compA_get hgl, prod3_get (H.invlt k hk _ hgl),
      H.inv k hk _ htp]
  rw [e1, e2, e3, beq_iff_eq.1 (allLt_iff.1 hok p hp)]

end

abbrev St := Array (Nat × Nat × Nat × Nat) × Array Bool × Array (Tri × Nat × Tri)

abbrev OSt := Array (Nat × Nat × Nat × Nat) × Array Bool × Array (Tri × Nat × Tri) × Nat

@[expose] def body1 (n : Nat) (L : Array Level) (base : Array Nat) (us : Array (Array Nat))
    (j : Nat) (s : St) : Id (ForInStep St) :=
  if (!s.2.1[idx3 L (coords3 n L base us[j]!)]!) = true then
    pure (ForInStep.yield (s.1.set! (idx3 L (coords3 n L base us[j]!)) (j, 0, 0, 0),
      s.2.1.set! (idx3 L (coords3 n L base us[j]!)) true,
      s.2.2.push (coords3 n L base us[j]!, j, 0, 0, 0)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

@[expose] def innerBody (n : Nat) (L : Array Level) (base : Array Nat) (gens : Array (Array Nat))
    (Q : Array (Tri × Nat × Tri)) (h k : Nat) (s : St) : Id (ForInStep St) :=
  if (!s.2.1[idx3 L (coords3 n L base (compA n gens[k]! (compA n
      (prod3 n L Q[h]!.1.1 Q[h]!.1.2.1 Q[h]!.1.2.2) (Array.map (invCand n) gens)[k]!)))]!) = true then
    pure (ForInStep.yield
      (s.1.set! (idx3 L (coords3 n L base (compA n gens[k]! (compA n
          (prod3 n L Q[h]!.1.1 Q[h]!.1.2.1 Q[h]!.1.2.2) (Array.map (invCand n) gens)[k]!))))
        (Q[h]!.2.1,
          (coords3 n L base (compA n gens[k]! (prod3 n L Q[h]!.2.2.1 Q[h]!.2.2.2.1
            Q[h]!.2.2.2.2))).1,
          (coords3 n L base (compA n gens[k]! (prod3 n L Q[h]!.2.2.1 Q[h]!.2.2.2.1
            Q[h]!.2.2.2.2))).2.1,
          (coords3 n L base (compA n gens[k]! (prod3 n L Q[h]!.2.2.1 Q[h]!.2.2.2.1
            Q[h]!.2.2.2.2))).2.2),
        s.2.1.set! (idx3 L (coords3 n L base (compA n gens[k]! (compA n
          (prod3 n L Q[h]!.1.1 Q[h]!.1.2.1 Q[h]!.1.2.2) (Array.map (invCand n) gens)[k]!)))) true,
        s.2.2.push (coords3 n L base (compA n gens[k]! (compA n
            (prod3 n L Q[h]!.1.1 Q[h]!.1.2.1 Q[h]!.1.2.2) (Array.map (invCand n) gens)[k]!)),
          Q[h]!.2.1,
          coords3 n L base (compA n gens[k]! (prod3 n L Q[h]!.2.2.1 Q[h]!.2.2.2.1
            Q[h]!.2.2.2.2)))))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

@[expose] def outerBody (n : Nat) (L : Array Level) (base : Array Nat) (gens : Array (Array Nat))
    (_ : Nat) (s : OSt) : Id (ForInStep OSt) :=
  if s.2.2.2 < s.2.2.1.size then
    pure (ForInStep.yield (let t := Id.run (forIn (List.range' 0 gens.size) (s.1, s.2.1, s.2.2.1)
      (innerBody n L base gens s.2.2.1 s.2.2.2))
      (t.1, t.2.1, t.2.2, s.2.2.2 + 1)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def init (L : Array Level) : St :=
  (Array.replicate (sz L) (0, 0, 0, 0), Array.replicate (sz L) false, #[])

theorem search_eq (n : Nat) (L : Array Level) (base : Array Nat) (gens us : Array (Array Nat)) :
    conjSearch3 n L base gens us =
      (let s := Id.run (forIn (List.range' 0 us.size) (init L) (body1 n L base us))
      Id.run (forIn (List.range' 0 (sz L)) (s.1, s.2.1, s.2.2, 0) (outerBody n L base gens))).1 := by
  unfold conjSearch3
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

@[expose] def QI (n : Nat) (L : Array Level) (us : Array (Array Nat))
    (W : Array (Nat × Nat × Nat × Nat)) (Sn : Array Bool) (Q : Array (Tri × Nat × Tri)) : Prop :=
  W.size = sz L ∧ Sn.size = sz L ∧
    (∀ q < Q.size, InR L Q[q]!.1 ∧ Sn[idx3 L Q[q]!.1]! = true ∧ Valid n L us Q[q]!.1 Q[q]!.2.1 Q[q]!.2.2) ∧
    (∀ i < sz L, Sn[i]! = true → ∃ q < Q.size, idx3 L Q[q]!.1 = i) ∧
    (∀ i < sz L, Sn[i]! = true → Valid n L us (dec L i) W[i]!.1 (W[i]!.2.1, W[i]!.2.2.1, W[i]!.2.2.2)) ∧
    (∀ q < Q.size, ∀ q' < Q.size, idx3 L Q[q]!.1 = idx3 L Q[q']!.1 → q = q')

section

variable {n : Nat} {L : Array Level} {us : Array (Array Nat)}

theorem qi_init : QI n L us (init L).1 (init L).2.1 (init L).2.2 := by
  refine ⟨by simp [init], by simp [init], fun q hq => by simp [init] at hq, fun i hi h => ?_,
    fun i hi h => ?_, fun q hq => by simp [init] at hq⟩
  · rw [init, rep_get hi] at h
    exact absurd h (by decide)
  · rw [init, rep_get hi] at h
    exact absurd h (by decide)

theorem qi_push {W : Array (Nat × Nat × Nat × Nat)} {Sn : Array Bool} {Q : Array (Tri × Nat × Tri)}
    (hI : QI n L us W Sn Q) {y t : Tri} {j : Nat} (hy : InR L y) (hn : Sn[idx3 L y]! = false)
    (hv : Valid n L us y j t) :
    QI n L us (W.set! (idx3 L y) (j, t.1, t.2.1, t.2.2)) (Sn.set! (idx3 L y) true)
      (Q.push (y, j, t)) ∧ ∀ i : Nat, Sn[i]! = true → (Sn.set! (idx3 L y) true)[i]! = true := by
  obtain ⟨hW, hS, hQ, hcov, hval, hinj⟩ := hI
  have hiy := idx_lt hy
  have hsn : ∀ i : Nat, (Sn.set! (idx3 L y) true)[i]! = true ↔ i = idx3 L y ∨ Sn[i]! = true := by
    intro i
    by_cases e : i = idx3 L y
    · subst e
      rw [set_eq (by omega)]
      simp
    · rw [set_ne (Ne.symm e)]
      simp [e]
  have hold : ∀ q < Q.size, idx3 L Q[q]!.1 ≠ idx3 L y := fun q hq e => by
    have := (hQ q hq).2.1
    rw [e, hn] at this
    exact absurd this (by decide)
  refine ⟨⟨by rw [size_set, hW], by rw [size_set, hS], fun q hq => ?_, fun i hi h => ?_,
    fun i hi h => ?_, fun q hq q' hq' e => ?_⟩, fun i h => (hsn i).2 (Or.inr h)⟩
  · simp only [Array.size_push] at hq
    rcases Nat.lt_or_ge q Q.size with a | a
    · rw [push_lt a]
      obtain ⟨b1, b2, b3⟩ := hQ q a
      exact ⟨b1, (hsn _).2 (Or.inr b2), b3⟩
    · have : q = Q.size := by omega
      subst this
      rw [push_eq]
      exact ⟨hy, (hsn _).2 (Or.inl rfl), hv⟩
  · rcases (hsn i).1 h with e | e
    · exact ⟨Q.size, by simp, by rw [push_eq, e]⟩
    · obtain ⟨q, hq, e'⟩ := hcov i hi e
      exact ⟨q, by simp; omega, by rw [push_lt hq, e']⟩
  · by_cases e : i = idx3 L y
    · subst e
      rw [set_eq (by omega), dec_idx hy]
      exact hv
    · rw [set_ne (Ne.symm e)]
      exact hval i hi (by rwa [hsn, or_iff_right e] at h)
  · simp only [Array.size_push] at hq hq'
    rcases Nat.lt_or_ge q Q.size with a | a <;> rcases Nat.lt_or_ge q' Q.size with b | b
    · rw [push_lt a, push_lt b] at e
      exact hinj q a q' b e
    · have : q' = Q.size := by omega
      subst this
      rw [push_lt a, push_eq] at e
      exact absurd e (hold q a)
    · have : q = Q.size := by omega
      subst this
      rw [push_lt b, push_eq] at e
      exact absurd e.symm (hold q' b)
    · omega

theorem queue_le {W : Array (Nat × Nat × Nat × Nat)} {Sn : Array Bool} {Q : Array (Tri × Nat × Tri)}
    (hI : QI n L us W Sn Q) : Q.size ≤ sz L := by
  obtain ⟨-, -, hQ, -, -, hinj⟩ := hI
  have := Finset.card_le_card_of_injOn (s := Finset.range Q.size) (t := Finset.range (sz L))
    (fun q => idx3 L Q[q]!.1)
    (fun q hq => Finset.mem_range.2 (idx_lt (hQ q (Finset.mem_range.1 hq)).1))
    (fun a ha b hb e => hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e)
  simpa using this

end

section

variable {n : Nat} {L : Array Level} {base : Array Nat} {gens us : Array (Array Nat)}

theorem loop1_spec (H : Hyp n L base gens us) :
    let s := Id.run (forIn (List.range' 0 us.size) (init L) (body1 n L base us))
    QI n L us s.1 s.2.1 s.2.2 ∧
      ∀ j < us.size, s.2.1[idx3 L (coords3 n L base us[j]!)]! = true := by
  refine forIn_range'_ind us.size 0 (init L) (body1 n L base us)
    (fun m s => QI n L us s.1 s.2.1 s.2.2 ∧
      ∀ j < m, s.2.1[idx3 L (coords3 n L base us[j]!)]! = true)
    (fun j hj s hP => ?_) ⟨qi_init, fun j hj => absurd hj (by omega)⟩
  obtain ⟨hI, hr⟩ := hP
  rw [Nat.zero_add]
  obtain ⟨x, hx, ha⟩ := H.us j hj
  have hc : coords3 n L base us[j]! = x := H.coord _ x hx ha
  by_cases h : s.2.1[idx3 L (coords3 n L base us[j]!)]! = true
  · refine ⟨s, by rw [body1, if_neg (by rw [h]; decide)], hI, fun j' hj' => ?_⟩
    rcases Nat.lt_or_ge j' j with a | a
    · exact hr j' a
    · have : j' = j := by omega
      subst this
      exact h
  · have h0 : s.2.1[idx3 L (coords3 n L base us[j]!)]! = false := by simpa using h
    have h' : s.2.1[idx3 L x]! = false := by rw [← hc]; exact h0
    obtain ⟨hI', hmono⟩ := qi_push hI hx h' (valid_root H hj ha)
    refine ⟨(s.1.set! (idx3 L x) (j, 0, 0, 0), s.2.1.set! (idx3 L x) true, s.2.2.push (x, j, 0, 0, 0)),
      by rw [body1, if_pos (by rw [h0]; rfl), hc], hI', fun j' hj' => ?_⟩
    rcases Nat.lt_or_ge j' j with a | a
    · exact hmono _ (hr j' a)
    · have : j' = j := by omega
      subst this
      rw [hc, set_eq (by rw [hI.2.1]; exact idx_lt hx)]

theorem inner_spec (H : Hyp n L base gens us) {W : Array (Nat × Nat × Nat × Nat)} {Sn : Array Bool}
    {Q : Array (Tri × Nat × Tri)} {h : Nat} (hI : QI n L us W Sn Q) (hh : h < Q.size) :
    let t := Id.run (forIn (List.range' 0 gens.size) (W, Sn, Q) (innerBody n L base gens Q h))
    QI n L us t.1 t.2.1 t.2.2 ∧ Q.size ≤ t.2.2.size ∧ (∀ q < Q.size, t.2.2[q]! = Q[q]!) ∧
      (∀ i : Nat, Sn[i]! = true → t.2.1[i]! = true) ∧
      ∀ k < gens.size, t.2.1[idx3 L (coords3 n L base (conjA n L gens k Q[h]!.1))]! = true := by
  obtain ⟨hx, -, hv⟩ := hI.2.2.1 h hh
  refine forIn_range'_ind gens.size 0 (W, Sn, Q) (innerBody n L base gens Q h)
    (fun m s => QI n L us s.1 s.2.1 s.2.2 ∧ Q.size ≤ s.2.2.size ∧ (∀ q < Q.size, s.2.2[q]! = Q[q]!) ∧
      (∀ i : Nat, Sn[i]! = true → s.2.1[i]! = true) ∧
      ∀ k < m, s.2.1[idx3 L (coords3 n L base (conjA n L gens k Q[h]!.1))]! = true)
    (fun k hk s hP => ?_) ⟨hI, le_refl _, fun _ _ => rfl, fun _ h => h, fun k hk => absurd hk (by omega)⟩
  obtain ⟨hI', hle, hpre, hmono, hcl⟩ := hP
  rw [Nat.zero_add]
  obtain ⟨y, hy, hay⟩ := H.conj _ hx k hk
  have hcy : coords3 n L base (conjA n L gens k Q[h]!.1) = y := H.coord _ y hy hay
  obtain ⟨t', ht', hat'⟩ := H.mul _ hv.2.1 k hk
  have hct : coords3 n L base (compA n gens[k]! (prod3 n L Q[h]!.2.2.1 Q[h]!.2.2.2.1
      Q[h]!.2.2.2.2)) = t' := H.coord _ t' ht' hat'
  have hcy' : coords3 n L base (compA n gens[k]! (compA n
      (prod3 n L Q[h]!.1.1 Q[h]!.1.2.1 Q[h]!.1.2.2) (Array.map (invCand n) gens)[k]!)) = y := hcy
  by_cases hs : s.2.1[idx3 L y]! = true
  · refine ⟨s, by rw [innerBody, if_neg (by rw [hcy', hs]; decide)], hI', hle, hpre, hmono,
      fun k' hk' => ?_⟩
    rcases Nat.lt_or_ge k' k with a | a
    · exact hcl k' a
    · have : k' = k := by omega
      subst this
      rw [hcy]
      exact hs
  · have hs' : s.2.1[idx3 L y]! = false := by simpa using hs
    obtain ⟨hI'', hmono'⟩ := qi_push hI' hy hs' (valid_child H hk hv hx hay hat' hy ht')
    refine ⟨(s.1.set! (idx3 L y) (Q[h]!.2.1, t'.1, t'.2.1, t'.2.2), s.2.1.set! (idx3 L y) true,
        s.2.2.push (y, Q[h]!.2.1, t')),
      by rw [innerBody, if_pos (by rw [hcy', hs']; rfl), hcy', hct], hI'',
      by simp only [Array.size_push]; omega, fun q hq => by rw [push_lt (by omega), hpre q hq],
      fun i hi => hmono' i (hmono i hi), fun k' hk' => ?_⟩
    rcases Nat.lt_or_ge k' k with a | a
    · exact hmono' _ (hcl k' a)
    · have : k' = k := by omega
      subst this
      rw [hcy, set_eq (by rw [hI'.2.1]; exact idx_lt hy)]

@[expose] def OI (n : Nat) (L : Array Level) (base : Array Nat) (gens us : Array (Array Nat))
    (r : Nat) (s : OSt) : Prop :=
  QI n L us s.1 s.2.1 s.2.2.1 ∧ (∀ j < us.size, s.2.1[idx3 L (coords3 n L base us[j]!)]! = true) ∧
    s.2.2.2 ≤ s.2.2.1.size ∧ (s.2.2.2 = s.2.2.1.size ∨ r ≤ s.2.2.2) ∧
    ∀ q < s.2.2.2, ∀ k < gens.size,
      s.2.1[idx3 L (coords3 n L base (conjA n L gens k s.2.2.1[q]!.1))]! = true

theorem outer_spec (H : Hyp n L base gens us) {s0 : St} (h0 : QI n L us s0.1 s0.2.1 s0.2.2)
    (hr : ∀ j < us.size, s0.2.1[idx3 L (coords3 n L base us[j]!)]! = true) :
    OI n L base gens us (sz L)
      (Id.run (forIn (List.range' 0 (sz L)) (s0.1, s0.2.1, s0.2.2, 0) (outerBody n L base gens))) := by
  refine forIn_range'_ind (sz L) 0 _ (outerBody n L base gens) (OI n L base gens us)
    (fun r hr' s hQ => ?_) ⟨h0, hr, Nat.zero_le _, Or.inr (le_refl _),
      fun q hq => absurd hq (Nat.not_lt_zero q)⟩
  obtain ⟨hI, hroot, hle, hor, hcl⟩ := hQ
  rw [Nat.zero_add]
  by_cases hc : s.2.2.2 < s.2.2.1.size
  · obtain ⟨hI', hle', hpre, hmono, hcl'⟩ := inner_spec (h := s.2.2.2) H hI hc
    refine ⟨_, by rw [outerBody, if_pos hc], ?_⟩
    dsimp only
    generalize Id.run (forIn (List.range' 0 gens.size) (s.1, s.2.1, s.2.2.1)
      (innerBody n L base gens s.2.2.1 s.2.2.2)) = t at hI' hle' hpre hmono hcl' ⊢
    refine ⟨hI', fun j hj => hmono _ (hroot j hj), by simp only; omega,
      Or.inr (by simp only; omega), fun q hq k hk => ?_⟩
    simp only at hq ⊢
    rcases Nat.lt_or_ge q s.2.2.2 with a | a
    · rw [hpre q (by omega)]
      exact hmono _ (hcl q a k hk)
    · have : q = s.2.2.2 := by omega
      subst this
      rw [hpre _ hc]
      exact hcl' k hk
  · refine ⟨s, by rw [outerBody, if_neg hc], hI, hroot, hle, Or.inl (by omega), hcl⟩

theorem conjSearch3_spec (H : Hyp n L base gens us) :
    ∃ Sn : Array Bool,
      (∀ i < sz L, Sn[i]! = true → Valid n L us (dec L i) (conjSearch3 n L base gens us)[i]!.1
        ((conjSearch3 n L base gens us)[i]!.2.1, (conjSearch3 n L base gens us)[i]!.2.2.1,
          (conjSearch3 n L base gens us)[i]!.2.2.2)) ∧
      (∀ j < us.size, Sn[idx3 L (coords3 n L base us[j]!)]! = true) ∧
      ∀ i < sz L, Sn[i]! = true → ∀ k < gens.size,
        Sn[idx3 L (coords3 n L base (conjA n L gens k (dec L i)))]! = true := by
  rw [search_eq]
  obtain ⟨h1, h2⟩ := loop1_spec H
  generalize Id.run (forIn (List.range' 0 us.size) (init L) (body1 n L base us)) = s at h1 h2 ⊢
  obtain ⟨hI, hroot, hle, hor, hcl⟩ := outer_spec H h1 h2
  generalize Id.run (forIn (List.range' 0 (sz L)) (s.1, s.2.1, s.2.2, 0)
    (outerBody n L base gens)) = t at hI hroot hle hor hcl ⊢
  have hq := queue_le hI
  have hhd : t.2.2.2 = t.2.2.1.size := by omega
  refine ⟨t.2.1, fun i hi h => hI.2.2.2.2.1 i hi h, hroot, fun i hi h k hk => ?_⟩
  obtain ⟨q, hq', e⟩ := hI.2.2.2.1 i hi h
  have hx := (hI.2.2.1 q hq').1
  rw [← e, dec_idx hx]
  exact hcl q (by omega) k hk

end

end CFSG.KS.Raw.CS3

end

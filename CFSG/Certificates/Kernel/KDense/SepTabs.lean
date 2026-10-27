module

public import Certificates.Data.Kernel.KDense.Keys
public import CFSG.Certificates.Kernel.BenesSound
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.SuccPred

public section

namespace CFSG.KC.KDense.TabAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371

@[expose] def flt (P : ℕ → Bool) (n : ℕ) : List ℕ := (List.range n).filter P

theorem flt_succ (P : ℕ → Bool) (n : ℕ) :
    flt P (n + 1) = flt P n ++ (if P n then [n] else []) := by
  unfold flt
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : P n = true
  · simp [h]
  · simp [h]

theorem flt_get (P : ℕ → Bool) : ∀ n t (ht : t < (flt P n).length),
    (flt P n)[t] < n ∧ P (flt P n)[t] = true ∧ (flt P (flt P n)[t]).length = t
  | 0, t, ht => by simp [flt] at ht
  | n + 1, t, ht => by
    have e := flt_succ P n
    by_cases hn : P n = true
    · rw [hn, ite_eq_left rfl] at e
      have hlen : (flt P (n + 1)).length = (flt P n).length + 1 := by rw [e]; simp
      rcases Nat.lt_or_ge t (flt P n).length with h | h
      · have hg : (flt P (n + 1))[t] = (flt P n)[t] := by
          simp only [e]
          rw [List.getElem_append_left h]
        obtain ⟨h1, h2, h3⟩ := flt_get P n t h
        rw [hg]
        exact ⟨by omega, h2, h3⟩
      · have ht' : t = (flt P n).length := by omega
        have hg : (flt P (n + 1))[t] = n := by
          simp only [e]
          rw [List.getElem_append_right (by omega)]
          simp
        rw [hg]
        exact ⟨by omega, hn, ht'.symm⟩
    · have hn' : P n = false := by simpa using hn
      rw [hn'] at e
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at e
      have ht' : t < (flt P n).length := by rw [← e]; exact ht
      have hg : (flt P (n + 1))[t] = (flt P n)[t] := by simp only [e]
      obtain ⟨h1, h2, h3⟩ := flt_get P n t ht'
      rw [hg]
      exact ⟨by omega, h2, h3⟩

theorem flt_length_mono (P : ℕ → Bool) {a b : ℕ} (h : a ≤ b) :
    (flt P a).length ≤ (flt P b).length := by
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h1 | h1
    · refine le_trans (ih (by omega)) ?_
      rw [flt_succ]
      simp
    · obtain rfl : a = b + 1 := by omega
      exact le_rfl

theorem flt_length_succ {P : ℕ → Bool} {y : ℕ} (hy : P y = true) :
    (flt P (y + 1)).length = (flt P y).length + 1 := by
  rw [flt_succ, hy]
  simp

theorem flt_index {P : ℕ → Bool} {n y : ℕ} (hy : y < n) (hP : P y = true) :
    ∃ h : (flt P y).length < (flt P n).length, (flt P n)[(flt P y).length] = y := by
  have hlt : (flt P y).length < (flt P n).length := by
    have := flt_length_mono P (Nat.succ_le_of_lt hy)
    rw [flt_length_succ hP] at this
    omega
  refine ⟨hlt, ?_⟩
  obtain ⟨h1, h2, h3⟩ := flt_get P n _ hlt
  generalize (flt P n)[(flt P y).length] = z at h1 h2 h3
  rcases Nat.lt_trichotomy z y with h | h | h
  · have := flt_length_mono P (Nat.succ_le_of_lt h)
    rw [flt_length_succ h2] at this
    omega
  · exact h
  · have := flt_length_mono P (Nat.succ_le_of_lt h)
    rw [flt_length_succ hP] at this
    omega

theorem flt_congr {P Q : ℕ → Bool} {n : ℕ} (h : ∀ a < n, P a = Q a) : flt P n = flt Q n := by
  unfold flt
  apply List.filter_congr
  intro a ha
  exact h a (List.mem_range.1 ha)

@[expose] noncomputable def oStep (OCT : ℕ) : ℕ → Bool × ℕ → Bool × ℕ :=
  fun a ih => Prod.rec (motive := fun _ => Bool × Nat) (fun ok n =>
    Bool.rec (motive := fun _ => Bool × Nat) (ok, n)
      (andB ok (Nat.beq (f12 OCT n) a), Nat.add n (nat_lit 1))
      (Nat.beq (popc24 (wordT a)) (nat_lit 8))) ih

@[expose] noncomputable def oST (OCT a : ℕ) : Bool × ℕ :=
  Nat.rec (motive := fun _ => Bool × Nat) (true, nat_lit 0) (oStep OCT) a

@[expose] noncomputable def P8 (a : ℕ) : Bool := Nat.beq (popc24 (wordT a)) 8

theorem oST_spec (OCT : ℕ) : ∀ a, (oST OCT a).2 = (flt P8 a).length ∧
    ((oST OCT a).1 = true → ∀ t (ht : t < (flt P8 a).length), f12 OCT t = (flt P8 a)[t])
  | 0 => ⟨rfl, fun _ t ht => by simp [flt] at ht⟩
  | a + 1 => by
    obtain ⟨ih1, ih2⟩ := oST_spec OCT a
    have e : oST OCT (a + 1) = oStep OCT a (oST OCT a) := rfl
    generalize hs : oST OCT a = s at ih1 ih2 e
    obtain ⟨ok, n⟩ := s
    simp only at ih1 ih2
    rw [e]
    have e2 := flt_succ P8 a
    unfold oStep
    dsimp only
    cases hP : P8 a
    · have hP' : Nat.beq (popc24 (wordT a)) (nat_lit 8) = false := hP
      rw [hP']
      rw [hP] at e2
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at e2
      simp only [e2]
      exact ⟨ih1, ih2⟩
    · have hP' : Nat.beq (popc24 (wordT a)) (nat_lit 8) = true := hP
      rw [hP']
      rw [hP] at e2
      simp only [↓reduceIte] at e2
      dsimp only
      simp only [e2, List.length_append, List.length_singleton, nadd]
      refine ⟨by rw [ih1], fun hok t ht => ?_⟩
      have hok' := Benes.andB_true hok
      rcases Nat.lt_or_ge t (flt P8 a).length with h | h
      · rw [List.getElem_append_left h]
        exact ih2 hok'.1 t h
      · have ht' : t = (flt P8 a).length := by simp at ht; omega
        rw [List.getElem_append_right (by omega)]
        simp only [ht', Nat.sub_self, List.getElem_singleton]
        have := Nat.eq_of_beq_eq_true hok'.2
        rw [← ih1]
        exact this

theorem popc_agree : ∀ h < 64, ∀ l < 64,
    P8 (64 * h + l) = (Native.popcN 24 (Native.wordN (64 * h + l)) == 8) := by
  decide +kernel

theorem popc_agree' {a : ℕ} (ha : a < 4096) :
    P8 a = (Native.popcN 24 (Native.wordN a) == 8) := by
  have := popc_agree (a / 64) (by omega) (a % 64) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

theorem octTab_flt : Native.octTab () = (flt (fun a => Native.popcN 24 (Native.wordN a) == 8) 4096).toArray :=
  rfl

set_option maxRecDepth 100000 in
theorem f12_octOK {OCT : ℕ} (h : octOK OCT = true) {o : ℕ} (ho : o < 759) :
    f12 OCT o = (Native.octTab ())[o]! := by
  unfold octOK at h
  generalize hN : nat_lit 4096 = N at h
  have hs := oST_spec OCT N
  unfold oST oStep at hs
  generalize Nat.rec (motive := fun _ => Bool × Nat) (true, nat_lit 0) _ N = s at h hs
  obtain ⟨ok, n⟩ := s
  obtain ⟨hok, hn⟩ := Benes.andB_true h
  have hn' : n = 759 := Nat.eq_of_beq_eq_true hn
  obtain ⟨h1, h2⟩ := hs
  simp only at h1 h2
  have hN' : N = 4096 := hN.symm
  subst hN'
  have hlen : o < (flt P8 4096).length := by omega
  have e1 : flt P8 4096 = flt (fun a => Native.popcN 24 (Native.wordN a) == 8) 4096 :=
    flt_congr (fun a ha => popc_agree' ha)
  calc f12 OCT o = (flt P8 4096)[o] := h2 hok o hlen
    _ = (flt (fun a => Native.popcN 24 (Native.wordN a) == 8) 4096)[o]'(e1 ▸ hlen) :=
        List.getElem_of_eq e1 hlen
    _ = (flt (fun a => Native.popcN 24 (Native.wordN a) == 8) 4096)[o]! := (getElem!_pos _ _ _).symm
    _ = ((flt (fun a => Native.popcN 24 (Native.wordN a) == 8) 4096).toArray)[o]! := by
        rw [List.getElem!_toArray]
    _ = (Native.octTab ())[o]! := by rw [octTab_flt]

theorem evenTab_eq : ∀ m < 64, (Native.evenTab ())[m]! = 2 * m + parT 6 m := by
  decide +kernel

end CFSG.KC.KDense.TabAux

end

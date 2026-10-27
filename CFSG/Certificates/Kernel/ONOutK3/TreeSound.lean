module

public import CFSG.Certificates.Kernel.ONOutK3.Bfs3
public import CFSG.Sporadic.Schreier.ONPermArr

public section

namespace CFSG.KS.ONK3

open CFSG.KS.Bfs3 CFSG.KS.BfsReplay CFSG.ComponentClassification.SolMax.ONOut
open CFSG.ONSchreier.Native

theorem ofFn_get3 {α : Type} [Inhabited α] {n k : Nat} {f : Nat → α} (hk : k < n) :
    (Array.ofFn (n := n) fun i => f i.val)[k]! = f k := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem treeOK_iff {n ng : Nat} {step : Nat → Pt3 → Pt3} {start : Pt3} {par lab : Array Nat}
    {im : Array Pt3} :
    treeOK n ng step start par lab im = true ↔ im[0]! = start ∧
      ∀ k < n, k ≠ 0 → par[k]! < k ∧ lab[k]! < ng ∧ im[k]! = step lab[k]! im[par[k]!]! := by
  unfold treeOK
  rw [Bool.and_eq_true, beq_iff_eq, CFSG.ONSchreier.allBelowN_iff]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro k
  apply imp_congr Iff.rfl
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    tauto

theorem treeOK_of_R3 {step : Nat → Pt3 → Pt3} {k : Nat} {root : Pt3} {cnt : Nat} {T : Nat → Pt3}
    {par lab : Nat → Nat} {pos : Nat → Nat → Nat} (R : R3 step k root cnt T par lab pos) :
    treeOK cnt k step root (Array.ofFn (n := cnt) fun i => par i.val)
      (Array.ofFn (n := cnt) fun i => lab i.val) (Array.ofFn (n := cnt) fun i => T i.val) = true := by
  rw [treeOK_iff]
  refine ⟨by rw [ofFn_get3 R.pos_cnt, R.root_eq], fun i hi h0 => ?_⟩
  obtain ⟨a1, a2, a3⟩ := R.tree i (Nat.pos_of_ne_zero h0) hi
  rw [ofFn_get3 hi, ofFn_get3 hi, ofFn_get3 hi, ofFn_get3 (Nat.lt_trans a1 hi)]
  exact ⟨a1, a2, a3⟩

@[expose] def TTInv (step : Nat → Pt3 → Pt3) (start : Pt3) (par lab : Array Nat) (m : Nat)
    (s : Array Pt3) : Prop :=
  s.size = m ∧ s[0]! = start ∧ ∀ i, 0 < i → i < m → par[i]! < i → s[i]! = step lab[i]! s[par[i]!]!

theorem treeTriples_spec {step : Nat → Pt3 → Pt3} {start : Pt3} {par lab : Array Nat} {n : Nat}
    (hn : 0 < n) : TTInv step start par lab n (treeTriples step start par lab n) := by
  have e : treeTriples step start par lab n = Id.run (forIn (List.range' 1 (n - 1)) #[start]
      (fun k s => (pure (ForInStep.yield (s.push (step lab[k]! s[par[k]!]!))) :
        Id (ForInStep (Array Pt3))))) := by
    unfold treeTriples
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.add_sub_cancel, Nat.div_one]
    rfl
  rw [e]
  have := forIn_range'_yield (n - 1) 1 #[start]
    (fun k s => (pure (ForInStep.yield (s.push (step lab[k]! s[par[k]!]!))) : Id (ForInStep (Array Pt3))))
    (fun j s => TTInv step start par lab (j + 1) s)
    (fun j _ s hs => ⟨_, rfl, ?_⟩) ⟨rfl, rfl, fun i h0 hi => by omega⟩
  · rw [show n - 1 + 1 = n by omega] at this
    exact this
  · obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨by simp [h1], ?_, fun i h0 hi hp => ?_⟩
    · rw [push_lt (i := 0) (by omega)]
      exact h2
    · rcases Nat.lt_or_ge i (j + 1) with a | a
      · rw [push_lt (i := i) (by omega), push_lt (i := par[i]!) (by omega)]
        exact h3 i h0 a hp
      · have e : i = 1 + j := by omega
        subst e
        rw [push_lt (i := par[1 + j]!) (by omega), show 1 + j = s.size by omega, push_eq]

theorem treeTriples_get {step : Nat → Pt3 → Pt3} {start : Pt3} {par lab : Array Nat} {n : Nat}
    (hn : 0 < n) :
    (treeTriples step start par lab n).size = n ∧ (treeTriples step start par lab n)[0]! = start ∧
      ∀ i, 0 < i → i < n → par[i]! < i →
        (treeTriples step start par lab n)[i]! = step lab[i]! (treeTriples step start par lab n)[par[i]!]! :=
  treeTriples_spec hn

theorem treeOK_treeTriples {step : Nat → Pt3 → Pt3} {start : Pt3} {par lab : Array Nat}
    {n ng : Nat} (hn : 0 < n) (h : ∀ k < n, k ≠ 0 → par[k]! < k ∧ lab[k]! < ng) :
    treeOK n ng step start par lab (treeTriples step start par lab n) = true := by
  obtain ⟨-, h0, hs⟩ := treeTriples_get (step := step) (start := start) (par := par) (lab := lab) hn
  rw [treeOK_iff]
  refine ⟨h0, fun k hk h0' => ⟨(h k hk h0').1, (h k hk h0').2, ?_⟩⟩
  exact hs k (Nat.pos_of_ne_zero h0') hk (h k hk h0').1

theorem posMap3_spec {im : Array Pt3} {d : Nat}
    (hinj : ∀ a < im.size, ∀ b < im.size, im[a]! = im[b]! → a = b) :
    (∀ k < im.size, (posMap3 im).getD im[k]! d = k) ∧
      ∀ t, (∀ k < im.size, im[k]! ≠ t) → (posMap3 im).getD t d = d := by
  unfold posMap3
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  have := forIn_range'_yield im.size 0 (∅ : Std.HashMap Pt3 Nat)
    (fun k m => (pure (ForInStep.yield (m.insert im[k]! k)) : Id (ForInStep (Std.HashMap Pt3 Nat))))
    (fun j m => (∀ k < j, m.getD im[k]! d = k) ∧ ∀ t, (∀ k < j, im[k]! ≠ t) → m.getD t d = d)
    (fun j hj m hm => ⟨_, rfl, ?_⟩) ⟨fun k hk => by omega, fun t _ => Std.HashMap.getD_empty⟩
  · exact this
  · obtain ⟨h1, h2⟩ := hm
    rw [Nat.zero_add]
    refine ⟨fun k hk => ?_, fun t ht => ?_⟩
    · rw [Std.HashMap.getD_insert]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with a | a
      · have hne : (im[j]! == im[k]!) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          have := hinj j hj k (by omega) e
          omega
        rw [hne, if_neg (by simp)]
        exact h1 k a
      · subst a
        simp
    · rw [Std.HashMap.getD_insert]
      have hne : (im[j]! == t) = false := by
        rw [beq_eq_false_iff_ne]
        exact ht j (Nat.lt_succ_self j)
      rw [hne, if_neg (by simp)]
      exact h2 t fun k hk => ht k (Nat.lt_succ_of_lt hk)

theorem distinctOK_of_inj {n : Nat} {im : Array Pt3} (hn : im.size = n)
    (hinj : ∀ a < im.size, ∀ b < im.size, im[a]! = im[b]! → a = b) : distinctOK n im = true := by
  unfold distinctOK
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro k hk
  rw [beq_iff_eq]
  exact (posMap3_spec hinj).1 k (by omega)

theorem posMap3_mem {im : Array Pt3} {n : Nat} (hn : im.size = n)
    (hinj : ∀ a < im.size, ∀ b < im.size, im[a]! = im[b]! → a = b) (t : Pt3) :
    (decide ((posMap3 im).getD t n < n) && im[(posMap3 im).getD t n]! == t) = true ↔
      ∃ k < n, im[k]! = t := by
  constructor
  · intro h
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨_, h.1, h.2⟩
  · rintro ⟨k, hk, rfl⟩
    rw [(posMap3_spec hinj).1 k (by omega)]
    simp [hk]

theorem posMap3_nmem {im : Array Pt3} {n : Nat} (hn : im.size = n)
    (hinj : ∀ a < im.size, ∀ b < im.size, im[a]! = im[b]! → a = b) {t : Pt3}
    (ht : ∀ k < n, im[k]! ≠ t) :
    (decide ((posMap3 im).getD t n < n) && im[(posMap3 im).getD t n]! == t) = false := by
  rw [(posMap3_spec hinj).2 t fun k hk => ht k (by omega)]
  simp

end CFSG.KS.ONK3

end

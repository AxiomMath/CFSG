module

public import Certificates.Data.CFSGNative.Fi23.Tr
import CFSG.Certificates.Kernel.Fi22LH.Loops
import CFSG.Certificates.Kernel.Fi22LH.TreeSpec
import CFSG.Certificates.Kernel.Fi23Tr.TrBFS
import Mathlib.Data.Finset.Card

public section

namespace CFSG.KS.Fi23Tr

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.KS.Fi22LH

theorem ap_set!_self {r : Table} {i : Nat} (hi : i < r.size) (v : UInt32) :
    ap (r.set! i v) i = v.toNat := by
  unfold ap
  rw [get!_set! _ hi hi, if_pos rfl]

theorem ap_set!_ne {r : Table} {i j : Nat} (hij : i ≠ j) (v : UInt32) :
    ap (r.set! i v) j = ap r j := by
  unfold ap
  rw [Array.getElem!_set!_ne _ _ _ _ hij]

theorem setFold_spec (P : Nat → Bool) (F : Nat → Nat) (v : UInt32) (N : Nat) :
    ∀ n, n < 2 ^ 32 → (∀ f < n, P f = false → F f < N) →
      ((List.range n).foldl (fun r f => if (!P f) = true then r.set! (F f) (UInt32.ofNat f) else r)
        (Array.replicate N v)).size = N ∧ ∀ y < N,
      (((List.range n).foldl (fun r f => if (!P f) = true then r.set! (F f) (UInt32.ofNat f) else r)
        (Array.replicate N v))[y]! = v ∧ ∀ f < n, P f = false → F f ≠ y) ∨
      (ap ((List.range n).foldl (fun r f => if (!P f) = true then r.set! (F f) (UInt32.ofNat f)
          else r) (Array.replicate N v)) y < n ∧
        P (ap ((List.range n).foldl (fun r f => if (!P f) = true then r.set! (F f) (UInt32.ofNat f)
          else r) (Array.replicate N v)) y) = false ∧
        F (ap ((List.range n).foldl (fun r f => if (!P f) = true then r.set! (F f) (UInt32.ofNat f)
          else r) (Array.replicate N v)) y) = y)
  | 0, _, _ => ⟨by simp, fun y hy => Or.inl ⟨by
      rw [List.range_zero, List.foldl_nil, getElem!_pos _ y (by simpa using hy)]
      simp, fun f hf => absurd hf (Nat.not_lt_zero _)⟩⟩
  | n + 1, hn, hF => by
    obtain ⟨h1, h2⟩ := setFold_spec P F v N n (by omega) fun f hf => hF f (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun r f => if (!P f) = true then r.set! (F f) (UInt32.ofNat f)
      else r) (Array.replicate N v) = r at h1 h2
    by_cases hp : P n = false
    · have hc : (!P n) = true := by rw [hp]; rfl
      rw [if_pos hc]
      have hFn := hF n (by omega) hp
      refine ⟨by rw [Array.size_set!, h1], fun y hy => ?_⟩
      by_cases e : F n = y
      · subst e
        right
        rw [ap_set!_self (by rw [h1]; exact hFn), toNat_ofNat' (by omega)]
        exact ⟨by omega, hp, rfl⟩
      · rw [Array.getElem!_set!_ne _ _ _ _ e, ap_set!_ne e]
        rcases h2 y hy with ⟨g1, g2⟩ | ⟨g1, g2, g3⟩
        · refine Or.inl ⟨g1, fun f hf hpf => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hf with hf | hf
          · exact g2 f hf hpf
          · rw [hf]; exact e
        · exact Or.inr ⟨by omega, g2, g3⟩
    · have hc : ¬ (!P n) = true := by
        cases h : P n
        · exact absurd h hp
        · simp
      rw [if_neg hc]
      refine ⟨h1, fun y hy => ?_⟩
      rcases h2 y hy with ⟨g1, g2⟩ | ⟨g1, g2, g3⟩
      · refine Or.inl ⟨g1, fun f hf hpf => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hf with hf | hf
        · exact g2 f hf hpf
        · subst hf; exact absurd hpf hp
      · exact Or.inr ⟨by omega, g2, g3⟩

theorem mkRowInv_eq (O : WOrbit) (o : TrOrb) (D bi : Table) (tB : PBits) :
    mkRowInv O o D bi tB = (List.range 31671).foldl (fun r f => if (!pBit tB f) = true then
      r.set! (trAct O o D bi f 0) (UInt32.ofNat f) else r) (Array.replicate 137632 none32) := by
  unfold mkRowInv
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', bind_pure]
  exact forIn_yield _ _ (fun f r => by split <;> rfl) _ _

theorem mkRowInv_spec (O : WOrbit) (o : TrOrb) (D bi : Table) (tB : PBits)
    (hF : ∀ f < 31671, pBit tB f = false → trAct O o D bi f 0 < 137632) :
    (mkRowInv O o D bi tB).size = 137632 ∧ ∀ m < 137632,
      ((mkRowInv O o D bi tB)[m]! = none32 ∧
        ∀ f < 31671, pBit tB f = false → trAct O o D bi f 0 ≠ m) ∨
      (ap (mkRowInv O o D bi tB) m < 31671 ∧ pBit tB (ap (mkRowInv O o D bi tB) m) = false ∧
        trAct O o D bi (ap (mkRowInv O o D bi tB) m) 0 = m) := by
  rw [mkRowInv_eq]
  exact setFold_spec (pBit tB) (fun f => trAct O o D bi f 0) (none32 ()) 137632 31671 (by omega) hF

theorem nbrWit_eq (O : WOrbit) (o : TrOrb) (D bi : Table) (m : Nat) :
    nbrWit O o D bi m = (List.range 31671).foldl (fun r h => if (!pBit o.sets[m]! h) = true then
      r.set! (trAct O o D bi h m) (UInt32.ofNat h) else r)
        (Array.replicate 137632 (UInt32.ofNat 31671)) := by
  unfold nbrWit
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', bind_pure]
  exact forIn_yield _ _ (fun f r => by split <;> rfl) _ _

theorem nbrWit_spec (O : WOrbit) (o : TrOrb) (D bi : Table) (m : Nat)
    (hF : ∀ h < 31671, pBit o.sets[m]! h = false → trAct O o D bi h m < 137632) :
    (nbrWit O o D bi m).size = 137632 ∧ ∀ y < 137632,
      (ap (nbrWit O o D bi m) y = 31671 ∧
        ∀ h < 31671, pBit o.sets[m]! h = false → trAct O o D bi h m ≠ y) ∨
      (ap (nbrWit O o D bi m) y < 31671 ∧ pBit o.sets[m]! (ap (nbrWit O o D bi m) y) = false ∧
        trAct O o D bi (ap (nbrWit O o D bi m) y) m = y) := by
  rw [nbrWit_eq]
  obtain ⟨h1, h2⟩ := setFold_spec (pBit o.sets[m]!) (fun h => trAct O o D bi h m)
    (UInt32.ofNat 31671) 137632 31671 (by omega) hF
  refine ⟨h1, fun y hy => ?_⟩
  rcases h2 y hy with ⟨g1, g2⟩ | g
  · left
    refine ⟨?_, g2⟩
    unfold ap
    rw [g1]
    rfl
  · exact Or.inr g

theorem posFold_spec {α : Type} [Inhabited α] (ord : Array Nat) (f : Nat → α) (v : α) (N : Nat)
    (hlt : ∀ i < ord.size, ord[i]! < N)
    (hd : ∀ i < ord.size, ∀ j < ord.size, ord[i]! = ord[j]! → i = j) :
    ∀ n ≤ ord.size,
      ((List.range n).foldl (fun p i => p.set! ord[i]! (f i)) (Array.replicate N v)).size = N ∧
      (∀ i < n, ((List.range n).foldl (fun p i => p.set! ord[i]! (f i)) (Array.replicate N v))[ord[i]!]! =
        f i) ∧
      ∀ y < N, (∀ i < n, ord[i]! ≠ y) →
        ((List.range n).foldl (fun p i => p.set! ord[i]! (f i)) (Array.replicate N v))[y]! = v
  | 0, _ => ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero _), fun y hy _ => by
      rw [List.range_zero, List.foldl_nil, getElem!_pos _ y (by simpa using hy)]
      simp⟩
  | n + 1, hn => by
    obtain ⟨h1, h2, h3⟩ := posFold_spec ord f v N hlt hd n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun p i => p.set! ord[i]! (f i)) (Array.replicate N v) = p
      at h1 h2 h3
    have hon := hlt n (by omega)
    refine ⟨by rw [Array.size_set!, h1], fun i hi => ?_, fun y hy hne => ?_⟩
    · rw [get!_set! _ (by rw [h1]; exact hon) (by rw [h1]; exact hlt i (by omega))]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · have : ord[n]! ≠ ord[i]! := fun e => by
          have := hd n (by omega) i (by omega) e
          omega
        rw [if_neg this, h2 i hi]
      · rw [hi, if_pos rfl]
    · rw [Array.getElem!_set!_ne _ _ _ _ (hne n (by omega))]
      exact h3 y hy fun i hi => hne i (by omega)

@[expose] def muPosOf (ord : Array Nat) : Table := Id.run do
  let mut p : Table := Array.replicate 137632 none32
  for i in [0:ord.size] do
    p := p.set! ord[i]! (UInt32.ofNat i)
  return p

theorem trCompute_muPos (O : WOrbit) (D bi : Table) (z : PBits) :
    (trCompute O D bi z).muPos = muPosOf (trCompute O D bi z).mOrd := rfl

theorem muPosOf_eq (ord : Array Nat) : muPosOf ord =
    (List.range ord.size).foldl (fun p i => p.set! ord[i]! (UInt32.ofNat i))
      (Array.replicate 137632 none32) := by
  unfold muPosOf
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', bind_pure]
  exact forIn_yield _ _ (fun f r => rfl) _ _

theorem muPosOf_spec {ord : Array Nat} (hlt : ∀ i < ord.size, ord[i]! < 137632)
    (hd : ∀ i < ord.size, ∀ j < ord.size, ord[i]! = ord[j]! → i = j) (h32 : ord.size < 2 ^ 32) :
    (muPosOf ord).size = 137632 ∧ (∀ i < ord.size, ap (muPosOf ord) ord[i]! = i) ∧
      ∀ y < 137632, (∀ i < ord.size, ord[i]! ≠ y) → (muPosOf ord)[y]! = none32 := by
  rw [muPosOf_eq]
  obtain ⟨h1, h2, h3⟩ := posFold_spec ord (fun i => UInt32.ofNat i) (none32 ()) 137632 hlt hd
    ord.size (Nat.le_refl _)
  refine ⟨h1, fun i hi => ?_, h3⟩
  unfold ap
  rw [h2 i hi, toNat_ofNat' (by omega)]

@[expose] def muStep (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 h : Nat)
    (s : Array Nat × Array Nat × Array Bool) : Array Nat × Array Nat × Array Bool :=
  if (!pBit o.sets[v0]! h) = true then
    if (rowInv[trAct O o D bi h v0]! != none32 && !s.2.2[trAct O o D bi h v0]!) = true then
      (s.1.push (trAct O o D bi h v0), s.2.1.push h, s.2.2.set! (trAct O o D bi h v0) true)
    else s
  else s

theorem mkMu_eq (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 : Nat) :
    mkMu O o D bi rowInv v0 = (fun s : Array Nat × Array Nat × Array Bool => (s.1, s.2.1))
      ((List.range 31671).foldl (fun s h => muStep O o D bi rowInv v0 h s)
        (#[], #[], Array.replicate 137632 false)) := by
  unfold mkMu
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  rw [forIn_yield _ (fun h s => muStep O o D bi rowInv v0 h s) (fun h s => by
    unfold muStep
    split
    · split <;> rfl
    · rfl)]
  rfl

@[expose] def MInv (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 n : Nat)
    (s : Array Nat × Array Nat × Array Bool) : Prop :=
  s.2.1.size = s.1.size ∧ s.2.2.size = 137632 ∧
    (∀ i < s.1.size, s.2.1[i]! < n ∧ pBit o.sets[v0]! s.2.1[i]! = false ∧
      trAct O o D bi s.2.1[i]! v0 = s.1[i]! ∧ rowInv[s.1[i]!]! ≠ none32 ∧ s.1[i]! < 137632) ∧
    (∀ m < 137632, s.2.2[m]! = true ↔ ∃ i < s.1.size, s.1[i]! = m) ∧
    (∀ i < s.1.size, ∀ j < s.1.size, s.1[i]! = s.1[j]! → i = j) ∧
    ∀ h < n, pBit o.sets[v0]! h = false → rowInv[trAct O o D bi h v0]! ≠ none32 →
      ∃ i < s.1.size, s.1[i]! = trAct O o D bi h v0

theorem mkMu_inv (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 : Nat)
    (hF : ∀ h < 31671, pBit o.sets[v0]! h = false → trAct O o D bi h v0 < 137632) :
    ∀ n ≤ 31671, MInv O o D bi rowInv v0 n
      ((List.range n).foldl (fun s h => muStep O o D bi rowInv v0 h s)
        (#[], #[], Array.replicate 137632 false))
  | 0, _ => ⟨rfl, by simp, fun i hi => absurd hi (Nat.not_lt_zero _), fun m hm => by
      constructor
      · intro h
        rw [List.range_zero, List.foldl_nil, getElem!_pos _ m (by simpa using hm)] at h
        simp at h
      · rintro ⟨i, hi, _⟩
        exact absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _), fun h hh => absurd hh (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mkMu_inv O o D bi rowInv v0 hF n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun s h => muStep O o D bi rowInv v0 h s)
      (#[], #[], Array.replicate 137632 false) = s at h1 h2 h3 h4 h5 h6
    obtain ⟨ms, hs, seen⟩ := s
    dsimp only at h1 h2 h3 h4 h5 h6
    unfold muStep
    dsimp only
    by_cases hV : (!pBit o.sets[v0]! n) = true
    · rw [if_pos hV]
      have hV' : pBit o.sets[v0]! n = false := by simpa using hV
      have hm := hF n (by omega) hV'
      by_cases hc : (rowInv[trAct O o D bi n v0]! != none32 && !seen[trAct O o D bi n v0]!) = true
      · rw [if_pos hc]
        rw [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at hc
        obtain ⟨hr, hns⟩ := hc
        have hnew : ∀ i < ms.size, ms[i]! ≠ trAct O o D bi n v0 := by
          intro i hi e
          have := (h4 _ hm).2 ⟨i, hi, e⟩
          rw [hns] at this
          exact absurd this (by simp)
        have hpush : ∀ {α : Type} [Inhabited α] (a : Array α) (x : α) (k : Nat), k < a.size + 1 →
            (a.push x)[k]! = if k < a.size then a[k]! else x := by
          intro α _ a x k hk
          by_cases hk' : k < a.size
          · rw [if_pos hk', get!_push_lt _ _ hk']
          · rw [if_neg hk', get!_push_of (by omega)]
        refine ⟨by simp [h1], by rw [Array.size_set!, h2], fun i hi => ?_, fun m hm' => ?_,
          fun i hi j hj e => ?_, fun h hh hVh hrh => ?_⟩
        · rw [Array.size_push] at hi
          rw [hpush _ _ i (by rw [h1]; exact hi), hpush _ _ i hi, h1]
          by_cases hi' : i < ms.size
          · rw [if_pos hi', if_pos hi']
            obtain ⟨a1, a2, a3, a4, a5⟩ := h3 i hi'
            exact ⟨by omega, a2, a3, a4, a5⟩
          · rw [if_neg hi', if_neg hi']
            exact ⟨by omega, hV', rfl, hr, hm⟩
        · rw [get!_set! _ (by rw [h2]; exact hm) (by rw [h2]; exact hm'), Array.size_push]
          by_cases e : trAct O o D bi n v0 = m
          · rw [if_pos e]
            exact ⟨fun _ => ⟨ms.size, by omega, by rw [get!_push_eq, e]⟩, fun _ => rfl⟩
          · rw [if_neg e, h4 m hm']
            constructor
            · rintro ⟨i, hi, e'⟩
              exact ⟨i, by omega, by rw [get!_push_lt _ _ hi, e']⟩
            · rintro ⟨i, hi, e'⟩
              rw [hpush _ _ i hi] at e'
              split at e'
              · exact ⟨i, by assumption, e'⟩
              · exact absurd e' e
        · rw [Array.size_push] at hi hj
          rw [hpush _ _ i hi, hpush _ _ j hj] at e
          by_cases hi' : i < ms.size <;> by_cases hj' : j < ms.size
          · rw [if_pos hi', if_pos hj'] at e
            exact h5 i hi' j hj' e
          · rw [if_pos hi', if_neg hj'] at e
            exact absurd e (hnew i hi')
          · rw [if_neg hi', if_pos hj'] at e
            exact absurd e.symm (hnew j hj')
          · omega
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | hh
          · obtain ⟨i, hi, e⟩ := h6 h hh hVh hrh
            exact ⟨i, by simp; omega, by rw [get!_push_lt _ _ hi, e]⟩
          · subst hh
            exact ⟨ms.size, by simp, get!_push_eq _ _⟩
      · rw [if_neg hc]
        unfold MInv
        dsimp only
        refine ⟨h1, h2, fun i hi => ?_, h4, h5, fun h hh hVh hrh => ?_⟩
        · obtain ⟨a1, a2, a3, a4, a5⟩ := h3 i hi
          exact ⟨by omega, a2, a3, a4, a5⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | hh
          · exact h6 h hh hVh hrh
          · subst hh
            rw [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at hc
            have hs : seen[trAct O o D bi h v0]! = true := by
              cases e : seen[trAct O o D bi h v0]!
              · exact absurd ⟨hrh, e⟩ hc
              · rfl
            exact (h4 _ hm).1 hs
    · rw [if_neg hV]
      unfold MInv
      dsimp only
      refine ⟨h1, h2, fun i hi => ?_, h4, h5, fun h hh hVh hrh => ?_⟩
      · obtain ⟨a1, a2, a3, a4, a5⟩ := h3 i hi
        exact ⟨by omega, a2, a3, a4, a5⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | hh
        · exact h6 h hh hVh hrh
        · subst hh
          rw [hVh] at hV
          exact absurd rfl hV

theorem mkMu_spec (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 : Nat)
    (hF : ∀ h < 31671, pBit o.sets[v0]! h = false → trAct O o D bi h v0 < 137632) :
    let mu := mkMu O o D bi rowInv v0
    mu.2.size = mu.1.size ∧
      (∀ i < mu.1.size, mu.2[i]! < 31671 ∧ pBit o.sets[v0]! mu.2[i]! = false ∧
        trAct O o D bi mu.2[i]! v0 = mu.1[i]! ∧ rowInv[mu.1[i]!]! ≠ none32) ∧
      (∀ i < mu.1.size, ∀ j < mu.1.size, mu.1[i]! = mu.1[j]! → i = j) ∧
      ∀ h < 31671, pBit o.sets[v0]! h = false → rowInv[trAct O o D bi h v0]! ≠ none32 →
        ∃ i < mu.1.size, mu.1[i]! = trAct O o D bi h v0 := by
  rw [mkMu_eq]
  have H := mkMu_inv O o D bi rowInv v0 hF 31671 (Nat.le_refl _)
  generalize (List.range 31671).foldl (fun s h => muStep O o D bi rowInv v0 h s)
    (#[], #[], Array.replicate 137632 false) = s at H ⊢
  obtain ⟨h1, -, h3, -, h5, h6⟩ := H
  exact ⟨h1, fun i hi => ⟨(h3 i hi).1, (h3 i hi).2.1, (h3 i hi).2.2.1, (h3 i hi).2.2.2.1⟩, h5, h6⟩

abbrev TSt5 := Array Nat × Array Nat × Array Nat × Array Nat × Array Bool

abbrev TSt6 := Array Nat × Array Nat × Array Nat × Array Nat × Array Bool × Array (Nat × Table)

@[expose] def mtStep (W : Table) (hOf : Array Nat) (h y : Nat) (t : TSt5) : TSt5 :=
  if (!t.2.2.2.2[y]! && decide (ap W y < 31671)) = true then
    (t.1.push y, t.2.1.push h, t.2.2.1.push (ap W y), t.2.2.2.1.push hOf[y]!, t.2.2.2.2.set! y true)
  else t

@[expose] def mtBody (O : WOrbit) (o : TrOrb) (D bi : Table) (ms hOf : Array Nat) (h : Nat)
    (s : TSt6) : Id (ForInStep TSt6) :=
  if (decide (s.1.size < ms.size) && decide (h < s.1.size)) = true then do
    let r ← forIn ms ((s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1) : TSt5) fun y t =>
      if (!t.2.2.2.2[y]! && decide (ap (nbrWit O o D bi s.1[h]!) y < 31671)) = true then
        pure (ForInStep.yield (t.1.push y, t.2.1.push h, t.2.2.1.push (ap (nbrWit O o D bi s.1[h]!) y),
          t.2.2.2.1.push hOf[y]!, t.2.2.2.2.set! y true))
      else pure (ForInStep.yield (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2))
    pure (ForInStep.yield (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2,
      s.2.2.2.2.2.push (s.1[h]!, nbrWit O o D bi s.1[h]!)))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

@[expose] def hOfOf (ms hs : Array Nat) : Array Nat :=
  (List.range ms.size).foldl (fun a i => a.set! ms[i]! hs[i]!) (Array.replicate 137632 31671)

theorem mkMuTree_eq (O : WOrbit) (o : TrOrb) (D bi : Table) (ms hs : Array Nat) :
    mkMuTree O o D bi ms hs = (fun s : TSt6 => (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.2))
      (forIn (m := Id) [0:ms.size] ((#[ms[0]!], #[0], #[0], #[hs[0]!],
        (Array.replicate 137632 false).set! ms[0]! true, #[]) : TSt6)
        (mtBody O o D bi ms (hOfOf ms hs))) := by
  unfold mkMuTree
  simp only [Id.run]
  have hof : (forIn (m := Id) [:ms.size] (Array.replicate 137632 31671) fun i (s : Array Nat) =>
      pure (ForInStep.yield (s.set! ms[i]! hs[i]!))) = hOfOf ms hs := by
    unfold hOfOf
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
    exact forIn_yield _ _ (fun f r => rfl) _ _
  rw [hof]
  rfl

theorem mtInner (W : Table) (hOf : Array Nat) (h : Nat) (ms : Array Nat) (t : TSt5) :
    (forIn (m := Id) ms t fun y t =>
      if (!t.2.2.2.2[y]! && decide (ap W y < 31671)) = true then
        pure (ForInStep.yield (t.1.push y, t.2.1.push h, t.2.2.1.push (ap W y),
          t.2.2.2.1.push hOf[y]!, t.2.2.2.2.set! y true))
      else pure (ForInStep.yield (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2))) =
    ms.toList.foldl (fun t y => mtStep W hOf h y t) t := by
  rw [← Array.forIn_toList]
  exact forIn_yield _ _ (fun y t => by unfold mtStep; split <;> rfl) _ _

structure MT (O : WOrbit) (o : TrOrb) (D bi : Table) (ms hs : Array Nat) (ord par wit hw : Array Nat)
    (seen : Array Bool) : Prop where
  par_size : par.size = ord.size
  wit_size : wit.size = ord.size
  hw_size : hw.size = ord.size
  seen_size : seen.size = 137632
  pos : 0 < ord.size
  root : ord[0]! = ms[0]!
  mem : ∀ k < ord.size, ∃ i < ms.size, ms[i]! = ord[k]! ∧ hs[i]! = hw[k]!
  seen : ∀ m < 137632, seen[m]! = true ↔ ∃ k < ord.size, ord[k]! = m
  inj : ∀ i < ord.size, ∀ j < ord.size, ord[i]! = ord[j]! → i = j
  par : ∀ k, 0 < k → k < ord.size → par[k]! < k ∧
    ap (nbrWit O o D bi ord[par[k]!]!) ord[k]! < 31671 ∧ wit[k]! = ap (nbrWit O o D bi ord[par[k]!]!) ord[k]!

theorem MT.mem' {O : WOrbit} {o : TrOrb} {D bi : Table} {ms hs ord par wit hw : Array Nat}
    {seen : Array Bool} (H : MT O o D bi ms hs ord par wit hw seen) :
    ∀ k < ord.size, ∃ i < ms.size, ms[i]! = ord[k]! := fun k hk => by
  obtain ⟨i, hi, e, -⟩ := H.mem k hk
  exact ⟨i, hi, e⟩

theorem push_get {α : Type} [Inhabited α] (a : Array α) (x : α) {k : Nat} (hk : k < a.size + 1) :
    (a.push x)[k]! = if k < a.size then a[k]! else x := by
  by_cases hk' : k < a.size
  · rw [if_pos hk', get!_push_lt _ _ hk']
  · rw [if_neg hk', get!_push_of (by omega)]

theorem mtStep_inv {O : WOrbit} {o : TrOrb} {D bi : Table} {ms hs hOf : Array Nat}
    (hlt : ∀ i < ms.size, ms[i]! < 137632)
    (hOfs : ∀ i < ms.size, hOf[ms[i]!]! = hs[i]!) {t : TSt5}
    (H : MT O o D bi ms hs t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) {h y : Nat} (hh : h < t.1.size)
    {i0 : Nat} (hi0 : i0 < ms.size) (hy : ms[i0]! = y) :
    MT O o D bi ms hs (mtStep (nbrWit O o D bi t.1[h]!) hOf h y t).1
      (mtStep (nbrWit O o D bi t.1[h]!) hOf h y t).2.1 (mtStep (nbrWit O o D bi t.1[h]!) hOf h y t).2.2.1
      (mtStep (nbrWit O o D bi t.1[h]!) hOf h y t).2.2.2.1
      (mtStep (nbrWit O o D bi t.1[h]!) hOf h y t).2.2.2.2 ∧
    t.1.size ≤ (mtStep (nbrWit O o D bi t.1[h]!) hOf h y t).1.size ∧
    (∀ k < t.1.size, (mtStep (nbrWit O o D bi t.1[h]!) hOf h y t).1[k]! = t.1[k]!) ∧
    (ap (nbrWit O o D bi t.1[h]!) y < 31671 →
      ∃ j < (mtStep (nbrWit O o D bi t.1[h]!) hOf h y t).1.size,
        (mtStep (nbrWit O o D bi t.1[h]!) hOf h y t).1[j]! = y) := by
  obtain ⟨ord, par, wit, hw, seen⟩ := t
  dsimp only at H hh ⊢
  have hy137 : y < 137632 := by rw [← hy]; exact hlt i0 hi0
  unfold mtStep
  dsimp only
  by_cases hc : (!seen[y]! && decide (ap (nbrWit O o D bi ord[h]!) y < 31671)) = true
  · rw [if_pos hc]
    dsimp only
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨hns, hadj⟩ := hc
    have hnew : ∀ k < ord.size, ord[k]! ≠ y := by
      intro k hk e
      have := (H.seen y hy137).2 ⟨k, hk, e⟩
      rw [hns] at this
      exact absurd this (by simp)
    refine ⟨⟨by simp [H.par_size], by simp [H.wit_size], by simp [H.hw_size],
      by rw [Array.size_set!, H.seen_size], by simp, by rw [get!_push_lt _ _ H.pos]; exact H.root,
      fun k hk => ?_, fun m hm => ?_, fun i hi j hj e => ?_, fun k hk0 hk => ?_⟩,
      by simp, fun k hk => get!_push_lt _ _ hk, fun _ => ⟨ord.size, by simp, get!_push_eq _ _⟩⟩
    · rw [Array.size_push] at hk
      rw [push_get _ _ hk, push_get _ _ (by rw [H.hw_size]; exact hk), H.hw_size]
      by_cases hk' : k < ord.size
      · rw [if_pos hk', if_pos hk']
        exact H.mem k hk'
      · rw [if_neg hk', if_neg hk']
        exact ⟨i0, hi0, hy, by rw [← hy, hOfs i0 hi0]⟩
    · rw [get!_set! _ (by rw [H.seen_size]; exact hy137) (by rw [H.seen_size]; exact hm),
        Array.size_push]
      by_cases e : y = m
      · rw [if_pos e]
        exact ⟨fun _ => ⟨ord.size, by omega, by rw [get!_push_eq, e]⟩, fun _ => rfl⟩
      · rw [if_neg e, H.seen m hm]
        constructor
        · rintro ⟨k, hk, e'⟩
          exact ⟨k, by omega, by rw [get!_push_lt _ _ hk, e']⟩
        · rintro ⟨k, hk, e'⟩
          rw [push_get _ _ hk] at e'
          split at e'
          · exact ⟨k, by assumption, e'⟩
          · exact absurd e' e
    · rw [Array.size_push] at hi hj
      rw [push_get _ _ hi, push_get _ _ hj] at e
      by_cases hi' : i < ord.size <;> by_cases hj' : j < ord.size
      · rw [if_pos hi', if_pos hj'] at e
        exact H.inj i hi' j hj' e
      · rw [if_pos hi', if_neg hj'] at e
        exact absurd e (hnew i hi')
      · rw [if_neg hi', if_pos hj'] at e
        exact absurd e.symm (hnew j hj')
      · omega
    · rw [Array.size_push] at hk
      rcases Nat.lt_or_ge k ord.size with hk' | hk'
      · obtain ⟨p1, p2, p3⟩ := H.par k hk0 hk'
        have hpk : par[k]! < ord.size := by omega
        rw [get!_push_lt par _ (by rw [H.par_size]; exact hk'), get!_push_lt ord y hk',
          get!_push_lt wit _ (by rw [H.wit_size]; exact hk'), get!_push_lt ord y hpk]
        exact ⟨p1, p2, p3⟩
      · have ek : k = ord.size := by omega
        subst ek
        rw [get!_push_of H.par_size, get!_push_eq, get!_push_lt _ _ hh,
          get!_push_of H.wit_size]
        exact ⟨hh, hadj, rfl⟩
  · rw [if_neg hc]
    dsimp only
    refine ⟨H, Nat.le_refl _, fun _ _ => rfl, fun hadj => ?_⟩
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    cases e : seen[y]!
    · exact absurd ⟨e, hadj⟩ hc
    · exact (H.seen y hy137).1 e

theorem mem_get! {ms : Array Nat} {y : Nat} (hy : y ∈ ms) : ∃ i < ms.size, ms[i]! = y := by
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hy
  exact ⟨i, hi, by rw [getElem!_pos ms i hi, e]⟩

theorem mtFold_inv {O : WOrbit} {o : TrOrb} {D bi : Table} {ms hs hOf : Array Nat}
    (hlt : ∀ i < ms.size, ms[i]! < 137632) (hOfs : ∀ i < ms.size, hOf[ms[i]!]! = hs[i]!)
    {ord0 : Array Nat} {h : Nat} (hh : h < ord0.size) :
    ∀ (l pre : List Nat) (t : TSt5), (∀ y ∈ l, y ∈ ms) →
      MT O o D bi ms hs t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 → ord0.size ≤ t.1.size →
      (∀ k < ord0.size, t.1[k]! = ord0[k]!) →
      (∀ y ∈ pre, ap (nbrWit O o D bi ord0[h]!) y < 31671 → ∃ j < t.1.size, t.1[j]! = y) →
      let r := l.foldl (fun t y => mtStep (nbrWit O o D bi ord0[h]!) hOf h y t) t
      MT O o D bi ms hs r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∧ ord0.size ≤ r.1.size ∧
        (∀ k < ord0.size, r.1[k]! = ord0[k]!) ∧
        (∀ y ∈ pre ++ l, ap (nbrWit O o D bi ord0[h]!) y < 31671 → ∃ j < r.1.size, r.1[j]! = y)
  | [], pre, t, _, H, h1, h2, h3 => by
    rw [List.append_nil]
    exact ⟨H, h1, h2, h3⟩
  | y :: l, pre, t, hl, H, h1, h2, h3 => by
    intro r
    have ex : ord0[h]! = t.1[h]! := (h2 h hh).symm
    obtain ⟨i0, hi0, hy⟩ := mem_get! (hl y List.mem_cons_self)
    obtain ⟨g1, g2, g3, g4⟩ := mtStep_inv (O := O) (o := o) (D := D) (bi := bi) (hOf := hOf) hlt hOfs H
      (h := h) (by omega) hi0 hy
    rw [← ex] at g1 g2 g3 g4
    have := mtFold_inv hlt hOfs hh l (pre ++ [y]) _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) g1
      (by omega) (fun k hk => by rw [g3 k (by omega), h2 k hk]) (fun x hx ha => by
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨j, hj, e⟩ := h3 x hx ha
          exact ⟨j, by omega, by rw [g3 j hj, e]⟩
        · have e : x = y := by simpa using hx
          subst e
          exact g4 ha)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

theorem sub_card {ord ms : Array Nat} (hmem : ∀ k < ord.size, ∃ i < ms.size, ms[i]! = ord[k]!)
    (hinj : ∀ i < ord.size, ∀ j < ord.size, ord[i]! = ord[j]! → i = j)
    (hd : ∀ i < ms.size, ∀ j < ms.size, ms[i]! = ms[j]! → i = j) :
    ord.size ≤ ms.size ∧ (ord.size = ms.size → ∀ i < ms.size, ∃ k < ord.size, ord[k]! = ms[i]!) := by
  have hsub : (Finset.range ord.size).image (fun k => ord[k]!) ⊆
      (Finset.range ms.size).image (fun i => ms[i]!) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, rfl⟩ := hx
    exact hmem k hk
  have c1 : ((Finset.range ord.size).image (fun k => ord[k]!)).card = ord.size := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    exact hinj a (by simpa using ha) b (by simpa using hb) e
  have c2 : ((Finset.range ms.size).image (fun i => ms[i]!)).card = ms.size := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    exact hd a (by simpa using ha) b (by simpa using hb) e
  have hle := Finset.card_le_card hsub
  rw [c1, c2] at hle
  refine ⟨hle, fun he i hi => ?_⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [c1, c2, he])
  have : ms[i]! ∈ (Finset.range ms.size).image (fun i => ms[i]!) :=
    Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  rw [← heq] at this
  simpa using this

@[expose] def OInvT (O : WOrbit) (o : TrOrb) (D bi : Table) (ms hs : Array Nat) (q : Nat) (s : TSt6) :
    Prop :=
  MT O o D bi ms hs s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 ∧ q ≤ s.1.size ∧
    s.2.2.2.2.2.size = q ∧ (∀ i < q, s.2.2.2.2.2[i]! = (s.1[i]!, nbrWit O o D bi s.1[i]!)) ∧
    (∀ k < q, ∀ i < ms.size, ap (nbrWit O o D bi s.1[k]!) ms[i]! < 31671 →
      ∃ j < s.1.size, s.1[j]! = ms[i]!) ∧ (q = 0 → s.1.size = 1)

@[expose] def OEndT (O : WOrbit) (o : TrOrb) (D bi : Table) (ms hs : Array Nat) (s : TSt6) : Prop :=
  MT O o D bi ms hs s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 ∧ s.2.2.2.2.2.size ≤ s.1.size ∧
    (∀ i < s.2.2.2.2.2.size, s.2.2.2.2.2[i]! = (s.1[i]!, nbrWit O o D bi s.1[i]!)) ∧
    (1 < ms.size → 0 < s.2.2.2.2.2.size) ∧
    ((∀ i < ms.size, ∃ k < s.1.size, s.1[k]! = ms[i]!) ∨
      ∀ k < s.1.size, ∀ i < ms.size, ap (nbrWit O o D bi s.1[k]!) ms[i]! < 31671 →
        ∃ j < s.1.size, s.1[j]! = ms[i]!)

theorem mkMuTree_end (O : WOrbit) (o : TrOrb) (D bi : Table) {ms hs : Array Nat}
    (hms : 0 < ms.size) (hsz : hs.size = ms.size) (hlt : ∀ i < ms.size, ms[i]! < 137632)
    (hd : ∀ i < ms.size, ∀ j < ms.size, ms[i]! = ms[j]! → i = j) :
    OEndT O o D bi ms hs (forIn (m := Id) [0:ms.size] ((#[ms[0]!], #[0], #[0], #[hs[0]!],
        (Array.replicate 137632 false).set! ms[0]! true, #[]) : TSt6)
        (mtBody O o D bi ms (hOfOf ms hs))) := by
  have hOfs : ∀ i < ms.size, (hOfOf ms hs)[ms[i]!]! = hs[i]! := by
    intro i hi
    unfold hOfOf
    exact (posFold_spec ms (fun i => hs[i]!) 31671 137632 hlt hd ms.size (Nat.le_refl _)).2.1 i hi
  have hm0 := hlt 0 hms
  refine range_loop (fun q s => OInvT O o D bi ms hs q s) (fun s => OEndT O o D bi ms hs s) _ ms.size _
    ?_ ?_ ?_
  · rintro q ⟨ord, par, wit, hw, seen, nbrs⟩ hq ⟨H, hqs, hn1, hn2, hcl, hq0⟩
    dsimp only at H hqs hn1 hn2 hcl hq0
    unfold mtBody
    dsimp only
    by_cases hc : (decide (ord.size < ms.size) && decide (q < ord.size)) = true
    · rw [if_pos hc]
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
      change OInvT O o D bi ms hs (q + 1) _
      rw [mtInner]
      have := mtFold_inv (O := O) (o := o) (D := D) (bi := bi) hlt hOfs (ord0 := ord) (h := q) hc.2
        ms.toList [] (ord, par, wit, hw, seen) (fun y hy => Array.mem_toList_iff.1 hy) H
        (Nat.le_refl _) (fun _ _ => rfl) (fun y hy => absurd hy List.not_mem_nil)
      generalize ms.toList.foldl (fun t y => mtStep (nbrWit O o D bi ord[q]!) (hOfOf ms hs) q y t)
        (ord, par, wit, hw, seen) = r at this
      obtain ⟨r1, r2, r3, r4⟩ := this
      unfold OInvT
      dsimp only
      refine ⟨r1, by omega, by rw [Array.size_push, hn1], fun i hi => ?_, fun k hk i hi ha => ?_,
        fun h0 => absurd h0 (by omega)⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · rw [get!_push_lt _ _ (by omega), hn2 i hi, r3 i (by omega)]
        · subst hi
          rw [get!_push_of hn1, r3 i (by omega)]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
        · rw [r3 k (by omega)] at ha
          obtain ⟨j, hj, e⟩ := hcl k hk i hi ha
          exact ⟨j, by omega, by rw [r3 j hj, e]⟩
        · subst hk
          rw [r3 k (by omega)] at ha
          have hmi : ms[i]! ∈ ms := by
            rw [getElem!_pos ms i hi]
            exact Array.getElem_mem hi
          exact r4 _ (List.mem_append_right _ (Array.mem_toList_iff.2 hmi)) ha
    · rw [if_neg hc]
      change OEndT O o D bi ms hs (ord, par, wit, hw, seen, nbrs)
      unfold OEndT
      dsimp only
      have hsc := sub_card H.mem' H.inj hd
      refine ⟨H, by omega, fun i hi => hn2 i (by omega), fun h1 => ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos q with h0 | h0
        · have := hq0 h0
          rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
          exact absurd ⟨by omega, by omega⟩ hc
        · omega
      · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
        by_cases h1 : ord.size < ms.size
        · right
          intro k hk i hi ha
          exact hcl k (by omega) i hi ha
        · left
          exact hsc.2 (by omega)
  · rintro ⟨ord, par, wit, hw, seen, nbrs⟩ ⟨H, hqs, hn1, hn2, hcl, hq0⟩
    dsimp only at H hqs hn1 hn2 hcl hq0
    unfold OEndT
    dsimp only
    have hsc := sub_card H.mem' H.inj hd
    exact ⟨H, by omega, fun i hi => hn2 i (by omega), fun _ => by omega, Or.inl (hsc.2 (by omega))⟩
  · unfold OInvT
    dsimp only
    refine ⟨⟨rfl, rfl, rfl, by simp, by simp, rfl, fun k hk => ?_, fun m hm => ?_,
      fun i hi j hj _ => ?_, fun k hk0 hk => ?_⟩, by simp, rfl,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun k hk => absurd hk (Nat.not_lt_zero _),
      fun _ => rfl⟩
    · have hk' : k < 1 := hk
      have e : k = 0 := by omega
      subst e
      exact ⟨0, hms, rfl, rfl⟩
    · rw [get!_set! _ (by simp; omega) (by simp; omega)]
      by_cases e : ms[0]! = m
      · rw [if_pos e]
        exact ⟨fun _ => ⟨0, by simp, e⟩, fun _ => rfl⟩
      · rw [if_neg e, getElem!_pos _ m (by simp; omega)]
        simp only [Array.getElem_replicate, Bool.false_eq_true, false_iff]
        rintro ⟨k, hk, e'⟩
        have hk' : k < 1 := hk
        have e0 : k = 0 := by omega
        subst e0
        exact e e'
    · have hi' : i < 1 := hi
      have hj' : j < 1 := hj
      omega
    · have hk' : k < 1 := hk
      omega

theorem mkMuTree_spec (O : WOrbit) (o : TrOrb) (D bi : Table) {ms hs : Array Nat}
    (hms : 0 < ms.size) (hsz : hs.size = ms.size) (hlt : ∀ i < ms.size, ms[i]! < 137632)
    (hd : ∀ i < ms.size, ∀ j < ms.size, ms[i]! = ms[j]! → i = j)
    (hF : ∀ i < ms.size, ∀ h < 31671, pBit o.sets[ms[i]!]! h = false →
      trAct O o D bi h ms[i]! < 137632) :
    let mt := mkMuTree O o D bi ms hs
    mt.2.1.size = mt.1.size ∧ mt.2.2.1.size = mt.1.size ∧ mt.2.2.2.1.size = mt.1.size ∧
      0 < mt.1.size ∧ mt.1[0]! = ms[0]! ∧
      (∀ k < mt.1.size, ∃ i < ms.size, ms[i]! = mt.1[k]! ∧ hs[i]! = mt.2.2.2.1[k]!) ∧
      (∀ i < mt.1.size, ∀ j < mt.1.size, mt.1[i]! = mt.1[j]! → i = j) ∧
      (∀ k, 0 < k → k < mt.1.size → mt.2.1[k]! < k ∧ mt.2.2.1[k]! < 31671 ∧
        pBit o.sets[mt.1[mt.2.1[k]!]!]! mt.2.2.1[k]! = false ∧
        trAct O o D bi mt.2.2.1[k]! mt.1[mt.2.1[k]!]! = mt.1[k]!) ∧
      mt.2.2.2.2.size ≤ mt.1.size ∧
      (∀ i < mt.2.2.2.2.size, mt.2.2.2.2[i]! = (mt.1[i]!, nbrWit O o D bi mt.1[i]!)) ∧
      (1 < ms.size → 0 < mt.2.2.2.2.size) ∧
      ((∀ i < ms.size, ∃ k < mt.1.size, mt.1[k]! = ms[i]!) ∨
        ∀ k < mt.1.size, ∀ i < ms.size, ∀ h < 31671, pBit o.sets[mt.1[k]!]! h = false →
          trAct O o D bi h mt.1[k]! = ms[i]! → ∃ j < mt.1.size, mt.1[j]! = ms[i]!) := by
  rw [mkMuTree_eq]
  have E := mkMuTree_end O o D bi hms hsz hlt hd
  generalize forIn (m := Id) [0:ms.size] ((#[ms[0]!], #[0], #[0], #[hs[0]!],
    (Array.replicate 137632 false).set! ms[0]! true, #[]) : TSt6)
    (mtBody O o D bi ms (hOfOf ms hs)) = s at E ⊢
  obtain ⟨ord, par, wit, hw, seen, nbrs⟩ := s
  obtain ⟨H, e1, e2, e3, e4⟩ := E
  dsimp only at H e1 e2 e3 e4 ⊢
  have hF' : ∀ k < ord.size, ∀ h < 31671, pBit o.sets[ord[k]!]! h = false →
      trAct O o D bi h ord[k]! < 137632 := by
    intro k hk
    obtain ⟨i, hi, e⟩ := H.mem' k hk
    rw [← e]
    exact hF i hi
  have hordlt : ∀ k < ord.size, ord[k]! < 137632 := by
    intro k hk
    obtain ⟨i, hi, e⟩ := H.mem' k hk
    rw [← e]
    exact hlt i hi
  refine ⟨H.par_size, H.wit_size, H.hw_size, H.pos, H.root, H.mem, H.inj, fun k hk0 hk => ?_, e1, e2,
    e3, ?_⟩
  · obtain ⟨p1, p2, p3⟩ := H.par k hk0 hk
    rcases (nbrWit_spec O o D bi ord[par[k]!]! (hF' _ (by omega))).2 _ (hordlt k hk) with
      ⟨g1, -⟩ | ⟨g1, g2, g3⟩
    · omega
    · rw [p3]
      exact ⟨p1, g1, g2, g3⟩
  · rcases e4 with e4 | e4
    · exact Or.inl e4
    · right
      intro k hk i hi h hh hV he
      apply e4 k hk i hi
      rcases (nbrWit_spec O o D bi ord[k]! (hF' k hk)).2 _ (hlt i hi) with ⟨-, g2⟩ | ⟨g1, -, -⟩
      · exact absurd he (g2 h hh hV)
      · exact g1

abbrev ESt := Array Nat × Array Nat × Array (Nat × Table) × Array Nat × Nat

abbrev RSt := Array Nat × Array Nat × Array Nat

@[expose] def edBody (O : WOrbit) (o : TrOrb) (D bi : Table) (v0 : Nat) (ord pos : Array Nat)
    (_x : Nat) (s : ESt) : Id (ForInStep ESt) :=
  if s.2.2.2.1.isEmpty = true then pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))
  else do
    let r ← forIn s.2.2.2.1 ((s.1, s.2.1, #[]) : RSt) fun h t =>
      match Array.find? (fun p => decide (ap p.2 (trAct O o D bi h v0) < 31671)) s.2.2.1 with
      | some p => pure (ForInStep.yield (t.1.set! h pos[p.1]!, t.2.1.set! h (ap p.2 (trAct O o D bi h v0)),
          t.2.2))
      | none => pure (ForInStep.yield (t.1, t.2.1, t.2.2.push h))
    if (!r.2.2.isEmpty && decide (s.2.2.2.2 < ord.size)) = true then
      pure (ForInStep.yield (r.1, r.2.1, s.2.2.1.push (ord[s.2.2.2.2]!, nbrWit O o D bi ord[s.2.2.2.2]!),
        r.2.2, s.2.2.2.2 + 1))
    else pure (ForInStep.yield (r.1, r.2.1, s.2.2.1, r.2.2, s.2.2.2.2))

@[expose] def posOf (ord : Array Nat) : Array Nat :=
  (List.range ord.size).foldl (fun p i => p.set! ord[i]! i) (Array.replicate 137632 0)

@[expose] def todoOf (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 : Nat) : Array Nat :=
  (List.range 31671).foldl (fun t h => if (!pBit o.sets[v0]! h) = true then
    (if trIsFar rowInv (trAct O o D bi h v0) = true then t.push h else t) else t) #[]

theorem mkEd_eq (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 : Nat) (ord : Array Nat)
    (nbrs0 : Array (Nat × Table)) : mkEd O o D bi rowInv v0 ord nbrs0 =
      (fun s : ESt => (s.1, s.2.1)) (forIn (m := Id) [0:ord.size]
        ((Array.replicate 31671 0, Array.replicate 31671 31671, nbrs0, todoOf O o D bi rowInv v0,
          nbrs0.size) : ESt) (edBody O o D bi v0 ord (posOf ord))) := by
  unfold mkEd
  simp only [Id.run]
  have hpos : (forIn (m := Id) [:ord.size] (Array.replicate 137632 0) fun i (s : Array Nat) =>
      pure (ForInStep.yield (s.set! ord[i]! i))) = posOf ord := by
    unfold posOf
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
    exact forIn_yield _ _ (fun f r => rfl) _ _
  have htodo : (forIn (m := Id) [:31671] (#[] : Array Nat) fun h (s : Array Nat) =>
      if (!pBit o.sets[v0]! h) = true then
        if trIsFar rowInv (trAct O o D bi h v0) = true then pure (ForInStep.yield (s.push h))
        else pure (ForInStep.yield s)
      else pure (ForInStep.yield s)) = todoOf O o D bi rowInv v0 := by
    unfold todoOf
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
    exact forIn_yield _ _ (fun f r => by split; split <;> rfl; rfl) _ _
  rw [hpos, htodo]
  rfl

theorem todoOf_spec (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 : Nat) :
    (∀ h ∈ todoOf O o D bi rowInv v0, h < 31671 ∧ pBit o.sets[v0]! h = false ∧
      trIsFar rowInv (trAct O o D bi h v0) = true) ∧
    ∀ h < 31671, pBit o.sets[v0]! h = false → trIsFar rowInv (trAct O o D bi h v0) = true →
      h ∈ todoOf O o D bi rowInv v0 := by
  unfold todoOf
  have key : ∀ n, (∀ h ∈ (List.range n).foldl (fun t h => if (!pBit o.sets[v0]! h) = true then
      (if trIsFar rowInv (trAct O o D bi h v0) = true then t.push h else t) else t) #[],
        h < n ∧ pBit o.sets[v0]! h = false ∧ trIsFar rowInv (trAct O o D bi h v0) = true) ∧
      ∀ h < n, pBit o.sets[v0]! h = false → trIsFar rowInv (trAct O o D bi h v0) = true →
        h ∈ (List.range n).foldl (fun t h => if (!pBit o.sets[v0]! h) = true then
          (if trIsFar rowInv (trAct O o D bi h v0) = true then t.push h else t) else t) #[] := by
    intro n
    induction n with
    | zero => exact ⟨fun h hh => by simp at hh, fun h hh => absurd hh (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨i1, i2⟩ := ih
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range n).foldl (fun t h => if (!pBit o.sets[v0]! h) = true then
        (if trIsFar rowInv (trAct O o D bi h v0) = true then t.push h else t) else t) #[] = t at i1 i2
      by_cases c1 : (!pBit o.sets[v0]! n) = true
      · rw [if_pos c1]
        have c1' : pBit o.sets[v0]! n = false := by simpa using c1
        by_cases c2 : trIsFar rowInv (trAct O o D bi n v0) = true
        · rw [if_pos c2]
          refine ⟨fun h hh => ?_, fun h hh hV hf => ?_⟩
          · rcases Array.mem_push.1 hh with hh | hh
            · obtain ⟨a, b, c⟩ := i1 h hh
              exact ⟨by omega, b, c⟩
            · subst hh
              exact ⟨by omega, c1', c2⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | hh
            · exact Array.mem_push.2 (Or.inl (i2 h hh hV hf))
            · exact Array.mem_push.2 (Or.inr hh)
        · rw [if_neg c2]
          refine ⟨fun h hh => ?_, fun h hh hV hf => ?_⟩
          · obtain ⟨a, b, c⟩ := i1 h hh
            exact ⟨by omega, b, c⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | hh
            · exact i2 h hh hV hf
            · subst hh
              exact absurd hf c2
      · rw [if_neg c1]
        refine ⟨fun h hh => ?_, fun h hh hV hf => ?_⟩
        · obtain ⟨a, b, c⟩ := i1 h hh
          exact ⟨by omega, b, c⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | hh
          · exact i2 h hh hV hf
          · subst hh
            rw [hV] at c1
            exact absurd rfl c1
  exact key 31671

@[expose] def EdGood (O : WOrbit) (o : TrOrb) (D bi : Table) (v0 : Nat) (ord ex ek : Array Nat)
    (h : Nat) : Prop :=
  ex[h]! < ord.size ∧ ek[h]! < 31671 ∧ pBit o.sets[ord[ex[h]!]!]! ek[h]! = false ∧
    trAct O o D bi ek[h]! ord[ex[h]!]! = trAct O o D bi h v0

@[expose] def edStep (O : WOrbit) (o : TrOrb) (D bi : Table) (v0 : Nat) (pos : Array Nat)
    (nbrs : Array (Nat × Table)) (h : Nat) (t : RSt) : RSt :=
  match Array.find? (fun p => decide (ap p.2 (trAct O o D bi h v0) < 31671)) nbrs with
  | some p => (t.1.set! h pos[p.1]!, t.2.1.set! h (ap p.2 (trAct O o D bi h v0)), t.2.2)
  | none => (t.1, t.2.1, t.2.2.push h)

theorem edInner (O : WOrbit) (o : TrOrb) (D bi : Table) (v0 : Nat) (pos : Array Nat)
    (nbrs : Array (Nat × Table)) (todo : Array Nat) (t : RSt) :
    (forIn (m := Id) todo t fun h t =>
      match Array.find? (fun p => decide (ap p.2 (trAct O o D bi h v0) < 31671)) nbrs with
      | some p => pure (ForInStep.yield (t.1.set! h pos[p.1]!, t.2.1.set! h (ap p.2 (trAct O o D bi h v0)),
          t.2.2))
      | none => pure (ForInStep.yield (t.1, t.2.1, t.2.2.push h))) =
    todo.toList.foldl (fun t h => edStep O o D bi v0 pos nbrs h t) t := by
  rw [← Array.forIn_toList]
  exact forIn_yield _ _ (fun h t => by unfold edStep; split <;> rfl) _ _

theorem edFold_inv {O : WOrbit} {o : TrOrb} {D bi : Table} {v0 : Nat} {ord pos : Array Nat}
    {nbrs : Array (Nat × Table)} (hlt : ∀ i < ord.size, ord[i]! < 137632)
    (hpos : ∀ i < ord.size, pos[ord[i]!]! = i) (hnb : nbrs.size ≤ ord.size)
    (hnbs : ∀ i < nbrs.size, nbrs[i]! = (ord[i]!, nbrWit O o D bi ord[i]!))
    (hF : ∀ i < ord.size, ∀ h < 31671, pBit o.sets[ord[i]!]! h = false →
      trAct O o D bi h ord[i]! < 137632)
    (hw : ∀ h < 31671, pBit o.sets[v0]! h = false → trAct O o D bi h v0 < 137632) :
    ∀ (l pre : List Nat) (t : RSt), (∀ h ∈ l, h < 31671 ∧ pBit o.sets[v0]! h = false) →
      t.1.size = 31671 → t.2.1.size = 31671 →
      (∀ h ∈ t.2.2, h ∈ pre ∧ ∀ i < nbrs.size, ¬ ap nbrs[i]!.2 (trAct O o D bi h v0) < 31671) →
      (∀ h ∈ pre, EdGood O o D bi v0 ord t.1 t.2.1 h ∨ h ∈ t.2.2) →
      let r := l.foldl (fun t h => edStep O o D bi v0 pos nbrs h t) t
      r.1.size = 31671 ∧ r.2.1.size = 31671 ∧
        (∀ h, EdGood O o D bi v0 ord t.1 t.2.1 h → EdGood O o D bi v0 ord r.1 r.2.1 h) ∧
        (∀ h ∈ r.2.2, h ∈ pre ++ l ∧ ∀ i < nbrs.size, ¬ ap nbrs[i]!.2 (trAct O o D bi h v0) < 31671) ∧
        (∀ h ∈ pre ++ l, EdGood O o D bi v0 ord r.1 r.2.1 h ∨ h ∈ r.2.2)
  | [], pre, t, _, s1, s2, hr, hg => by
    rw [List.append_nil]
    exact ⟨s1, s2, fun _ h => h, hr, hg⟩
  | h :: l, pre, ⟨ex, ek, rest⟩, hl, s1, s2, hr, hg => by
    intro r
    obtain ⟨hh, hV⟩ := hl h List.mem_cons_self
    have hl' : ∀ x ∈ l, x < 31671 ∧ pBit o.sets[v0]! x = false := fun x hx =>
      hl x (List.mem_cons_of_mem _ hx)
    dsimp only at s1 s2 hr hg
    have e : r = l.foldl (fun t h => edStep O o D bi v0 pos nbrs h t)
        (edStep O o D bi v0 pos nbrs h (ex, ek, rest)) := rfl
    rw [e]
    cases hf : Array.find? (fun p => decide (ap p.2 (trAct O o D bi h v0) < 31671)) nbrs with
    | some p =>
      have es : edStep O o D bi v0 pos nbrs h (ex, ek, rest) =
          (ex.set! h pos[p.1]!, ek.set! h (ap p.2 (trAct O o D bi h v0)), rest) := by
        unfold edStep
        rw [hf]
      rw [es]
      have hp : ap p.2 (trAct O o D bi h v0) < 31671 := by
        have := Array.find?_some hf
        simpa using this
      obtain ⟨i, hi, ei⟩ := Array.mem_iff_getElem.1 (Array.mem_of_find?_eq_some hf)
      have epi : p = (ord[i]!, nbrWit O o D bi ord[i]!) := by
        rw [← ei, ← getElem!_pos nbrs i hi]
        exact hnbs i hi
      subst epi
      dsimp only at hp
      have hio : i < ord.size := by omega
      have hgood : EdGood O o D bi v0 ord (ex.set! h pos[ord[i]!]!)
          (ek.set! h (ap (nbrWit O o D bi ord[i]!) (trAct O o D bi h v0))) h := by
        unfold EdGood
        rw [get!_set! _ (by omega) (by omega), if_pos rfl, get!_set! _ (by omega) (by omega),
          if_pos rfl, hpos i hio]
        rcases (nbrWit_spec O o D bi ord[i]! (hF i hio)).2 _ (hw h hh hV) with ⟨g1, -⟩ | ⟨g1, g2, g3⟩
        · omega
        · exact ⟨hio, g1, g2, g3⟩
      have hpres : ∀ x, EdGood O o D bi v0 ord ex ek x → EdGood O o D bi v0 ord (ex.set! h pos[ord[i]!]!)
          (ek.set! h (ap (nbrWit O o D bi ord[i]!) (trAct O o D bi h v0))) x := by
        intro x hx
        by_cases e : h = x
        · subst e
          exact hgood
        · unfold EdGood at hx ⊢
          rw [Array.getElem!_set!_ne _ _ _ _ e, Array.getElem!_set!_ne _ _ _ _ e]
          exact hx
      obtain ⟨a1, a2, a3, a4, a5⟩ := edFold_inv hlt hpos hnb hnbs hF hw l (pre ++ [h])
        (ex.set! h pos[ord[i]!]!, ek.set! h (ap (nbrWit O o D bi ord[i]!) (trAct O o D bi h v0)), rest)
        hl' (by simp [s1]) (by simp [s2]) (fun x hx => by
          obtain ⟨b1, b2⟩ := hr x hx
          exact ⟨List.mem_append_left _ b1, b2⟩)
        (fun x hx => by
          rcases List.mem_append.1 hx with hx | hx
          · rcases hg x hx with g | g
            · exact Or.inl (hpres x g)
            · exact Or.inr g
          · have e : x = h := by simpa using hx
            subst e
            exact Or.inl hgood)
      rw [List.append_assoc, List.singleton_append] at a4 a5
      exact ⟨a1, a2, fun x hx => a3 x (hpres x hx), a4, a5⟩
    | none =>
      have es : edStep O o D bi v0 pos nbrs h (ex, ek, rest) = (ex, ek, rest.push h) := by
        unfold edStep
        rw [hf]
      rw [es]
      have hna : ∀ i < nbrs.size, ¬ ap nbrs[i]!.2 (trAct O o D bi h v0) < 31671 := by
        intro i hi ha
        have := Array.find?_eq_none.1 hf nbrs[i] (Array.getElem_mem hi)
        rw [← getElem!_pos nbrs i hi] at this
        exact this (decide_eq_true ha)
      obtain ⟨a1, a2, a3, a4, a5⟩ := edFold_inv hlt hpos hnb hnbs hF hw l (pre ++ [h])
        (ex, ek, rest.push h) hl' s1 s2 (fun x hx => by
          rcases Array.mem_push.1 hx with hx | hx
          · obtain ⟨b1, b2⟩ := hr x hx
            exact ⟨List.mem_append_left _ b1, b2⟩
          · subst hx
            exact ⟨by simp, hna⟩)
        (fun x hx => by
          rcases List.mem_append.1 hx with hx | hx
          · rcases hg x hx with g | g
            · exact Or.inl g
            · exact Or.inr (Array.mem_push.2 (Or.inl g))
          · have e : x = h := by simpa using hx
            subst e
            exact Or.inr (Array.mem_push.2 (Or.inr rfl)))
      rw [List.append_assoc, List.singleton_append] at a4 a5
      exact ⟨a1, a2, a3, a4, a5⟩

theorem not_mem_of_isEmpty {xs : Array Nat} (h : xs.isEmpty = true) {x : Nat} : x ∉ xs := by
  rw [Array.empty_of_isEmpty h]
  simp

theorem isEmpty_of_forall {xs : Array Nat} (h : ∀ x ∈ xs, False) : xs.isEmpty = true := by
  cases e : xs.isEmpty
  · obtain ⟨x, hx⟩ := Array.isEmpty_eq_false_iff_exists_mem.1 e
    exact (h x hx).elim
  · rfl

@[expose] def RInv (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 n0 : Nat) (ord : Array Nat)
    (r : Nat) (s : ESt) : Prop :=
  s.1.size = 31671 ∧ s.2.1.size = 31671 ∧ s.2.2.1.size ≤ ord.size ∧
    (∀ i < s.2.2.1.size, s.2.2.1[i]! = (ord[i]!, nbrWit O o D bi ord[i]!)) ∧
    s.2.2.2.2 = s.2.2.1.size ∧
    (∀ h ∈ s.2.2.2.1, h < 31671 ∧ pBit o.sets[v0]! h = false ∧
      trIsFar rowInv (trAct O o D bi h v0) = true) ∧
    (∀ h < 31671, pBit o.sets[v0]! h = false → trIsFar rowInv (trAct O o D bi h v0) = true →
      EdGood O o D bi v0 ord s.1 s.2.1 h ∨ h ∈ s.2.2.2.1) ∧
    (s.2.2.2.1.isEmpty = false → min ord.size (n0 + r) ≤ s.2.2.1.size) ∧
    (ord.size ≤ r → s.2.2.2.1.isEmpty = true)

theorem mkEd_spec (O : WOrbit) (o : TrOrb) (D bi rowInv : Table) (v0 : Nat) {ord : Array Nat}
    {nbrs0 : Array (Nat × Table)} (hlt : ∀ i < ord.size, ord[i]! < 137632)
    (hd : ∀ i < ord.size, ∀ j < ord.size, ord[i]! = ord[j]! → i = j)
    (hnb : nbrs0.size ≤ ord.size) (hnb0 : 0 < nbrs0.size)
    (hnbs : ∀ i < nbrs0.size, nbrs0[i]! = (ord[i]!, nbrWit O o D bi ord[i]!))
    (hF : ∀ i < ord.size, ∀ h < 31671, pBit o.sets[ord[i]!]! h = false →
      trAct O o D bi h ord[i]! < 137632)
    (hw : ∀ h < 31671, pBit o.sets[v0]! h = false → trAct O o D bi h v0 < 137632)
    (hed : ∀ h < 31671, pBit o.sets[v0]! h = false → trIsFar rowInv (trAct O o D bi h v0) = true →
      ∃ i < ord.size, ∃ g < 31671, pBit o.sets[ord[i]!]! g = false ∧
        trAct O o D bi g ord[i]! = trAct O o D bi h v0) :
    let ed := mkEd O o D bi rowInv v0 ord nbrs0
    ∀ h < 31671, pBit o.sets[v0]! h = false → trIsFar rowInv (trAct O o D bi h v0) = true →
      ed.1[h]! < ord.size ∧ ed.2[h]! < 31671 ∧ pBit o.sets[ord[ed.1[h]!]!]! ed.2[h]! = false ∧
        trAct O o D bi ed.2[h]! ord[ed.1[h]!]! = trAct O o D bi h v0 := by
  rw [mkEd_eq]
  have hpos : ∀ i < ord.size, (posOf ord)[ord[i]!]! = i := fun i hi =>
    (posFold_spec ord (fun i => i) 0 137632 hlt hd ord.size (Nat.le_refl _)).2.1 i hi
  obtain ⟨t1, t2⟩ := todoOf_spec O o D bi rowInv v0
  have hadj : ∀ (nbrs : Array (Nat × Table)), nbrs.size = ord.size →
      (∀ i < nbrs.size, nbrs[i]! = (ord[i]!, nbrWit O o D bi ord[i]!)) → ∀ h < 31671,
      pBit o.sets[v0]! h = false → trIsFar rowInv (trAct O o D bi h v0) = true →
      (∀ i < nbrs.size, ¬ ap nbrs[i]!.2 (trAct O o D bi h v0) < 31671) → False := by
    intro nbrs hs hn h hh hV hf hna
    obtain ⟨i, hi, g, hg, hV', e⟩ := hed h hh hV hf
    apply hna i (by omega)
    rw [hn i (by omega)]
    rcases (nbrWit_spec O o D bi ord[i]! (hF i hi)).2 _ (hw h hh hV) with ⟨-, g2⟩ | ⟨g1, -, -⟩
    · exact absurd e (g2 g hg hV')
    · exact g1
  suffices H : RInv O o D bi rowInv v0 nbrs0.size ord ord.size (forIn (m := Id) [0:ord.size]
      ((Array.replicate 31671 0, Array.replicate 31671 31671, nbrs0, todoOf O o D bi rowInv v0,
        nbrs0.size) : ESt) (edBody O o D bi v0 ord (posOf ord))) ∨
      (∀ h < 31671, pBit o.sets[v0]! h = false → trIsFar rowInv (trAct O o D bi h v0) = true →
        EdGood O o D bi v0 ord (forIn (m := Id) [0:ord.size]
      ((Array.replicate 31671 0, Array.replicate 31671 31671, nbrs0, todoOf O o D bi rowInv v0,
        nbrs0.size) : ESt) (edBody O o D bi v0 ord (posOf ord))).1 (forIn (m := Id) [0:ord.size]
      ((Array.replicate 31671 0, Array.replicate 31671 31671, nbrs0, todoOf O o D bi rowInv v0,
        nbrs0.size) : ESt) (edBody O o D bi v0 ord (posOf ord))).2.1 h) by
    intro ed h hh hV hf
    rcases H with H | H
    · obtain ⟨-, -, -, -, -, -, h7, -, h9⟩ := H
      rcases h7 h hh hV hf with g | g
      · exact g
      · exact absurd g (not_mem_of_isEmpty (h9 (Nat.le_refl _)))
    · exact H h hh hV hf
  refine range_loop (fun r s => RInv O o D bi rowInv v0 nbrs0.size ord r s)
    (fun s => RInv O o D bi rowInv v0 nbrs0.size ord ord.size s ∨
      ∀ h < 31671, pBit o.sets[v0]! h = false → trIsFar rowInv (trAct O o D bi h v0) = true →
        EdGood O o D bi v0 ord s.1 s.2.1 h) _ ord.size _ ?_ (fun s hs => Or.inl hs) ?_
  · rintro r ⟨ex, ek, nbrs, todo, next⟩ hr ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩
    dsimp only at s1 s2 s3 s4 s5 s6 s7 s8 s9
    unfold edBody
    dsimp only
    by_cases he : todo.isEmpty = true
    · rw [if_pos he]
      right
      intro h hh hV hf
      rcases s7 h hh hV hf with g | g
      · exact g
      · exact absurd g (not_mem_of_isEmpty he)
    · rw [if_neg he]
      have he' : todo.isEmpty = false := by simpa using he
      rw [edInner]
      obtain ⟨a1, a2, a3, a4, a5⟩ := edFold_inv (O := O) (o := o) (D := D) (bi := bi) (v0 := v0)
        (pos := posOf ord) hlt hpos s3 s4 hF hw todo.toList [] (ex, ek, #[])
        (fun h hh => by
          obtain ⟨b1, b2, -⟩ := s6 h (Array.mem_toList_iff.1 hh)
          exact ⟨b1, b2⟩) s1 s2 (fun h hh => by simp at hh)
        (fun h hh => by simp at hh)
      generalize todo.toList.foldl (fun t h => edStep O o D bi v0 (posOf ord) nbrs h t)
        (ex, ek, #[]) = q at a1 a2 a3 a4 a5
      obtain ⟨ex', ek', rest⟩ := q
      dsimp only at a1 a2 a3 a4 a5 ⊢
      change LStep _ _ (if (!rest.isEmpty && decide (next < ord.size)) = true then
        (pure (ForInStep.yield ((ex', ek', nbrs.push (ord[next]!, nbrWit O o D bi ord[next]!), rest,
          next + 1) : ESt)) : Id (ForInStep ESt))
        else (pure (ForInStep.yield ((ex', ek', nbrs, rest, next) : ESt)) : Id (ForInStep ESt)))
      have hrest : ∀ h ∈ rest, h ∈ todo := fun h hh => by
        have := (a4 h hh).1
        simpa using this
      have h8 : rest.isEmpty = false → min ord.size (nbrs0.size + r) ≤ nbrs.size := fun hne =>
        s8 he'
      have h9 : ord.size ≤ r + 1 → rest.isEmpty = true := by
        intro hle
        refine isEmpty_of_forall fun h hh => ?_
        have hne : rest.isEmpty = false := Array.isEmpty_eq_false_iff_exists_mem.2 ⟨h, hh⟩
        have := h8 hne
        obtain ⟨b1, b2, b3⟩ := s6 h (hrest h hh)
        exact hadj nbrs (by omega) s4 h b1 b2 b3 (a4 h hh).2
      have h7 : ∀ h < 31671, pBit o.sets[v0]! h = false → trIsFar rowInv (trAct O o D bi h v0) = true →
          EdGood O o D bi v0 ord ex' ek' h ∨ h ∈ rest := by
        intro h hh hV hf
        rcases s7 h hh hV hf with g | g
        · exact Or.inl (a3 h g)
        · exact a5 h (by simpa using g)
      by_cases hc : (!rest.isEmpty && decide (next < ord.size)) = true
      · rw [if_pos hc]
        rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
        refine ⟨a1, a2, by simp; omega, fun i hi => ?_, by simp [s5], fun h hh => s6 h (hrest h hh),
          h7, fun _ => by have := s8 he'; simp; omega, h9⟩
        rw [Array.size_push] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · rw [get!_push_lt _ _ hi, s4 i hi]
        · rw [hi, get!_push_eq, s5]
      · rw [if_neg hc]
        rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
        refine ⟨a1, a2, s3, s4, s5, fun h hh => s6 h (hrest h hh), h7, fun hne => ?_, h9⟩
        change min ord.size (nbrs0.size + (r + 1)) ≤ nbrs.size
        have := h8 hne
        have : ¬ next < ord.size := fun h => hc ⟨hne, h⟩
        omega
  · unfold RInv
    dsimp only
    refine ⟨by simp, by simp, hnb, hnbs, rfl, t1, fun h hh hV hf => Or.inr (t2 h hh hV hf),
      fun _ => by omega, fun hle => isEmpty_of_forall fun h hh => ?_⟩
    obtain ⟨b1, b2, b3⟩ := t1 h hh
    obtain ⟨i, hi, -⟩ := hed h b1 b2 b3
    omega

end CFSG.KS.Fi23Tr

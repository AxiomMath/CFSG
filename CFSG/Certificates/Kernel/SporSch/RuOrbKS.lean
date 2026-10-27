module

public import Certificates.Data.Kernel.SporSch.RuOrbK
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.RuArrays
import CFSG.Certificates.Kernel.Spor.BfsReplay

public section

namespace CFSG.KS.SporSch.RuOrbKS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

private theorem strictB_eqR (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem bIf_casesR {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

private theorem blt_falseR {a b : Nat} (h : Nat.blt a b = false) : b ≤ a :=
  Nat.not_lt.1 fun hlt => by
    rw [Nat.blt_eq.mpr hlt] at h
    exact Bool.noConfusion h

private theorem unpack_getR {n w P i : Nat} (hi : i < n) :
    (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

private theorem unpack_sizeR (n w P : Nat) : (unpack n w P).size = n := by
  rw [unpack, Array.size_ofFn]

private theorem replicate_getR {α : Type} [Inhabited α] {n y : Nat} {v : α} (hy : y < n) :
    (Array.replicate n v)[y]! = v := by
  rw [getElem!_pos _ y (by simpa using hy), Array.getElem_replicate]

private theorem size_setR {α : Type} {a : Array α} {i : Nat} {v : α} :
    (a.set! i v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

private theorem set_getR {α : Type} [Inhabited α] {a : Array α} {i j : Nat} {v : α}
    (hi : i < a.size) : (a.set! i v)[j]! = if j = i then v else a[j]! := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set! i v).size := by rw [size_setR]; exact hj
    rw [getElem!_pos _ j hj', getElem!_pos a j hj]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [if_neg (Ne.symm hij), if_neg hij]
  · have hj' : ¬ j < (a.set! i v).size := by rw [size_setR]; exact hj
    have hij : j ≠ i := by omega
    rw [getElem!_neg _ j hj', getElem!_neg a j hj, if_neg hij]

private theorem push_atR {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat}
    (h : i = a.size) : (a.push x)[i]! = x := by
  subst h
  exact BfsReplay.push_eq

private theorem forIn_rngR {β : Type} (k : Nat) (init : β) (f : Nat → β → Id (ForInStep β)) :
    forIn (m := Id) [0:k] init f = forIn (List.range' 0 k) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hl : List.range' [0:k].start [0:k].size [0:k].step = List.range' 0 k := by
    simp [Std.Legacy.Range.size]
  rw [hl]

private theorem foldl_rangeR {β : Type} (P : Nat → β → Prop) (f : β → Nat → β) (b : β)
    (h0 : P 0 b) : ∀ m, (∀ k < m, ∀ r, P k r → P (k + 1) (f r k)) →
      P m ((List.range m).foldl f b)
  | 0, _ => by simpa using h0
  | m + 1, hs => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact hs m (Nat.lt_succ_self m) _
      (foldl_rangeR P f b h0 m fun k hk r hr => hs k (Nat.lt_succ_of_lt hk) r hr)

private theorem getD_rangeR {α : Type} {m k : Nat} (hk : k < m) (g : Nat → α) (d : α) :
    ((List.range m).map g).getD k d = g k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem ruLabTab_of_labK {n w K : Nat} {L SZ POS : Nat → Nat} {LAB : Nat}
    {Ls pos : List (Array Nat)}
    (hLs : Ls = (List.range K).map fun k => unpack (SZ k) w (L k))
    (hpos : pos = (List.range K).map fun k => unpack n w (POS k))
    (h : labK n w K L SZ POS LAB = true) :
    ruLabTab n Ls = unpack n w LAB ∧ labListsOK n Ls (unpack n w LAB) pos = true := by
  unfold labK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have H1 : ∀ k < K, ∀ i < SZ k, pg w (mask w) (L k) i < n ∧
      pg w (mask w) LAB (pg w (mask w) (L k) i) = k := by
    intro k hk i hi
    have e := allN_spec (allN_spec h1 k hk) i hi
    simp only [strictB_eqR] at e
    obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 e
    exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2⟩
  have H2 : ∀ x < n, pg w (mask w) LAB x < K ∧
      pg w (mask w) (POS (pg w (mask w) LAB x)) x < SZ (pg w (mask w) LAB x) ∧
      pg w (mask w) (L (pg w (mask w) LAB x)) (pg w (mask w) (POS (pg w (mask w) LAB x)) x) =
        x := by
    intro x hx
    have e := allN_spec h2 x hx
    simp only [strictB_eqR] at e
    obtain ⟨e1, e⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e2, e3⟩ := (bAnd_iff _ _).1 e
    exact ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, Nat.eq_of_beq_eq_true e3⟩
  have hlen : Ls.length = K := by rw [hLs, List.length_map, List.length_range]
  have hget : ∀ k < K, Ls.getD k #[] = unpack (SZ k) w (L k) := fun k hk => by
    rw [hLs]
    exact getD_rangeR hk _ _
  have hpget : ∀ k < K, pos.getD k #[] = unpack n w (POS k) := fun k hk => by
    rw [hpos]
    exact getD_rangeR hk _ _
  refine ⟨?_, ?_⟩
  ·
    have key := foldl_rangeR (fun k (r : Array Nat) => r.size = n ∧ ∀ y < n,
        r[y]! = if pg w (mask w) LAB y < k then pg w (mask w) LAB y else 0)
      (fun r k => (List.range (Ls.getD k #[]).size).foldl
        (fun r i => r.set! (Ls.getD k #[])[i]! k) r) (Array.replicate n 0)
      ⟨by simp, fun y hy => by rw [replicate_getR hy, if_neg (Nat.not_lt_zero _)]⟩ K
      (fun k hk r ⟨hr1, hr2⟩ => by
        rw [hget k hk, unpack_sizeR]
        obtain ⟨i1, i2⟩ := foldl_rangeR (fun i (r' : Array Nat) => r'.size = n ∧ ∀ y < n,
            (pg w (mask w) LAB y ≠ k → r'[y]! = r[y]!) ∧
            (∀ i' < i, pg w (mask w) (L k) i' = y → r'[y]! = k))
          (fun r i => r.set! (unpack (SZ k) w (L k))[i]! k) r
          ⟨hr1, fun y _ => ⟨fun _ => rfl, fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩⟩ (SZ k)
          (fun i hi r' ⟨h1', h2'⟩ => by
            obtain ⟨hxn, hxl⟩ := H1 k hk i hi
            rw [unpack_getR hi]
            refine ⟨by rw [size_setR, h1'], fun y hy => ⟨fun hyk => ?_, fun i' hi' hiy => ?_⟩⟩
            · have hyx : y ≠ pg w (mask w) (L k) i := fun e => hyk (by rw [e]; exact hxl)
              rw [set_getR (by rw [h1']; exact hxn), if_neg hyx]
              exact (h2' y hy).1 hyk
            · rw [set_getR (by rw [h1']; exact hxn)]
              by_cases hyx : y = pg w (mask w) (L k) i
              · rw [if_pos hyx]
              · rw [if_neg hyx]
                rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h3 | h3
                · exact (h2' y hy).2 i' h3 hiy
                · exact absurd (by rw [← hiy, h3]) hyx)
        refine ⟨i1, fun y hy => ?_⟩
        obtain ⟨hc, hp, hq⟩ := H2 y hy
        by_cases hyk : pg w (mask w) LAB y = k
        · rw [(i2 y hy).2 _ (by rw [← hyk]; exact hp) (by rw [← hyk]; exact hq),
            if_pos (by omega), hyk]
        · rw [(i2 y hy).1 hyk, hr2 y hy]
          by_cases hlt : pg w (mask w) LAB y < k
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)])
    obtain ⟨k1, k2⟩ := key
    unfold ruLabTab
    rw [hlen]
    refine Array.ext (by rw [k1, unpack_sizeR]) fun y hy1 hy2 => ?_
    have hy : y < n := by rwa [k1] at hy1
    rw [← getElem!_pos _ y hy1, ← getElem!_pos _ y hy2, k2 y hy, if_pos (H2 y hy).1,
      unpack_getR hy]
  · unfold labListsOK
    rw [Bool.and_eq_true, allLt_iff, allLt_iff, hlen]
    refine ⟨fun k hk => ?_, fun x hx => ?_⟩
    · rw [hget k hk, unpack_sizeR, allLt_iff]
      intro i hi
      obtain ⟨hxn, hxl⟩ := H1 k hk i hi
      rw [unpack_getR hi, unpack_getR hxn, hxl]
      simp [hxn]
    · obtain ⟨hc, hp, hq⟩ := H2 x hx
      rw [unpack_getR hx, hpget _ hc, hget _ hc, unpack_getR hx, unpack_sizeR, unpack_getR hp, hq]
      simp [hc, hp]

private theorem gens2_getR {n w G0 G1 k x : Nat} {a b : Array Nat}
    (ha : a = unpack n w G0) (hb : b = unpack n w G1) (hk : k < 2) (hx : x < n) :
    (#[a, b][k]!)[x]! = gimg w G0 G1 k x := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [show (#[a, b][0]! : Array Nat) = a by rfl, ha, unpack_getR hx]
    rfl
  · rw [show (#[a, b][1]! : Array Nat) = b by rfl, hb, unpack_getR hx]
    rfl

theorem orbitPartOK_of_checks {n w R G0 G1 LAB Q DEP PAR GL : Nat} {a b roots : Array Nat}
    (ha : a = unpack n w G0) (hb : b = unpack n w G1)
    (hr : roots.size = R ∧ ∀ t < R, roots[t]! = pg w (mask w) Q t)
    (hp : ∀ x < n, partAt n w R G0 G1 LAB Q DEP PAR GL x = true)
    (hk : ∀ k < R, rootAt n w LAB Q k = true) :
    orbitPartOK n #[a, b] (unpack n w LAB) roots (unpack n w DEP) (unpack n w PAR)
      (unpack n w GL) = true := by
  have U : ∀ P y, y < n → (unpack n w P)[y]! = pg w (mask w) P y := fun _ _ hy => unpack_getR hy
  unfold orbitPartOK
  rw [Bool.and_eq_true, allLt_iff, allLt_iff, hr.1]
  refine ⟨fun x hx => ?_, fun k hk' => ?_⟩
  · have e := hp x hx
    unfold partAt at e
    simp only [strictB_eqR] at e
    obtain ⟨e0, e⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e0a, e0b⟩ := (bAnd_iff _ _).1 e0
    obtain ⟨e1a, e1b⟩ := (bAnd_iff _ _).1 e1
    have y0 : gimg w G0 G1 0 x < n := Nat.blt_eq.mp e0a
    have y1 : gimg w G0 G1 1 x < n := Nat.blt_eq.mp e1a
    rw [Bool.and_eq_true, allLt_iff]
    refine ⟨fun k hk => ?_, ?_⟩
    · have hk2 : k < 2 := by simpa using hk
      rw [gens2_getR ha hb hk2 hx]
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [U LAB _ y0, U LAB x hx, Nat.eq_of_beq_eq_true e0b]
        simp [y0]
      · rw [U LAB _ y1, U LAB x hx, Nat.eq_of_beq_eq_true e1b]
        simp [y1]
    · rw [U DEP x hx, U LAB x hx, U PAR x hx, U GL x hx]
      rcases bIf_casesR e2 with ⟨hd, e3⟩ | ⟨hd, e3⟩
      · have hd' : pg w (mask w) DEP x = 0 := Nat.eq_of_beq_eq_true hd
        obtain ⟨e4, e5⟩ := (bAnd_iff _ _).1 e3
        have hc : pg w (mask w) LAB x < R := Nat.blt_eq.mp e4
        rw [hd', hr.2 _ hc, Nat.eq_of_beq_eq_true e5]
        simp
      · obtain ⟨f1, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f2, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f3, f4⟩ := (bAnd_iff _ _).1 e3
        have hpn : pg w (mask w) PAR x < n := Nat.blt_eq.mp f1
        have hdl : pg w (mask w) DEP (pg w (mask w) PAR x) < pg w (mask w) DEP x :=
          Nat.blt_eq.mp f2
        have hg2 : pg w (mask w) GL x < 2 := Nat.blt_eq.mp f3
        have hd' : pg w (mask w) DEP x ≠ 0 := by omega
        rw [U DEP _ hpn, gens2_getR ha hb hg2 hpn, Nat.eq_of_beq_eq_true f4]
        simp [hd', hpn, hdl, hg2]
  · have e := hk k hk'
    unfold rootAt at e
    simp only [strictB_eqR] at e
    obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 e
    have hrn : pg w (mask w) Q k < n := Nat.blt_eq.mp e1
    rw [hr.2 k hk', U LAB _ hrn, Nat.eq_of_beq_eq_true e2]
    simp [hrn]

private abbrev FSt := Array Nat × Array Nat × Array Nat × Array Bool × Array Nat

private abbrev GSt := Array Nat × Array Nat × Array Nat × Array Bool × Array Nat × Nat

private def fRoot (n r : Nat) (s : Array Bool × Array Nat) :
    Id (ForInStep (Array Bool × Array Nat)) :=
  if (decide (r < n) && !s.1[r]!) = true then pure (.yield (s.1.set! r true, s.2.push r))
  else pure (.yield (s.1, s.2))

private def fStep (n : Nat) (gens : Array (Array Nat)) (x k : Nat) (s : FSt) :
    Id (ForInStep FSt) :=
  if (decide ((gens[k]!)[x]! < n) && !s.2.2.2.1[(gens[k]!)[x]!]!) = true then
    pure (.yield (s.1.set! (gens[k]!)[x]! (s.1[x]! + 1), s.2.1.set! (gens[k]!)[x]! x,
      s.2.2.1.set! (gens[k]!)[x]! k, s.2.2.2.1.set! (gens[k]!)[x]! true,
      s.2.2.2.2.push (gens[k]!)[x]!))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

private def fRound (n : Nat) (gens : Array (Array Nat)) (_ : Nat) (s : GSt) :
    Id (ForInStep GSt) :=
  if s.2.2.2.2.2 < s.2.2.2.2.1.size then do
    let s' ← forIn [0:gens.size] (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1)
      (fStep n gens s.2.2.2.2.1[s.2.2.2.2.2]!)
    pure (.yield (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2.1, s'.2.2.2.2, s.2.2.2.2.2 + 1))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

private theorem orbitForest_eqR (n : Nat) (gens : Array (Array Nat)) (roots : Array Nat) :
    orbitForest n gens roots =
      (let s0 := (forIn roots (Array.replicate n false, (#[] : Array Nat)) (fRoot n) :
          Id (Array Bool × Array Nat))
       let s := (forIn [0:n] (Array.replicate n 0, Array.replicate n 0, Array.replicate n 0,
          s0.1, s0.2, 0) (fRound n gens) : Id GSt)
       (s.1, s.2.1, s.2.2.1)) := rfl

private def FCut (n wf R FO e c : Nat) : Prop :=
  R ≤ c ∧ c ≤ n ∧ ∀ t, R ≤ t → t < n → (pg wf (mask wf) FO t < e ↔ t < c)

private def FInv (n w Q ORD DEP PAR GL c : Nat) (s : FSt) : Prop :=
  s.1.size = n ∧ s.2.1.size = n ∧ s.2.2.1.size = n ∧ s.2.2.2.1.size = n ∧
    s.2.2.2.2.size = c ∧ (∀ i < c, s.2.2.2.2[i]! = pg w (mask w) Q i) ∧
    ∀ y < n, s.2.2.2.1[y]! = decide (pg w (mask w) ORD y < c) ∧
      s.1[y]! = (if pg w (mask w) ORD y < c then pg w (mask w) DEP y else 0) ∧
      s.2.1[y]! = (if pg w (mask w) ORD y < c then pg w (mask w) PAR y else 0) ∧
      s.2.2.1[y]! = (if pg w (mask w) ORD y < c then pg w (mask w) GL y else 0)

theorem orbitForest_of_checks {n w wf R G0 G1 Q ORD FO DEP PAR GL : Nat}
    {a b roots : Array Nat}
    (ha : a = unpack n w G0) (hb : b = unpack n w G1)
    (hr : roots.size = R ∧ ∀ t < R, roots[t]! = pg w (mask w) Q t) (hR : R ≤ n)
    (hf : ∀ t < n, forestAt n w wf R G0 G1 Q ORD FO DEP PAR GL t = true)
    (he : ∀ e < 2 * n, eventAt n w wf R G0 G1 Q ORD FO e = true) :
    orbitForest n #[a, b] roots = (unpack n w DEP, unpack n w PAR, unpack n w GL) := by
  have FA : ∀ t < n, pg w (mask w) Q t < n ∧ pg w (mask w) ORD (pg w (mask w) Q t) = t ∧
      (t < R → pg w (mask w) DEP (pg w (mask w) Q t) = 0 ∧
        pg w (mask w) PAR (pg w (mask w) Q t) = 0 ∧ pg w (mask w) GL (pg w (mask w) Q t) = 0) ∧
      (R ≤ t → pg wf (mask wf) FO t / 2 < t ∧
        gimg w G0 G1 (pg wf (mask wf) FO t % 2) (pg w (mask w) Q (pg wf (mask wf) FO t / 2)) =
          pg w (mask w) Q t ∧
        pg w (mask w) PAR (pg w (mask w) Q t) = pg w (mask w) Q (pg wf (mask wf) FO t / 2) ∧
        pg w (mask w) GL (pg w (mask w) Q t) = pg wf (mask wf) FO t % 2 ∧
        pg w (mask w) DEP (pg w (mask w) Q t) =
          pg w (mask w) DEP (pg w (mask w) Q (pg wf (mask wf) FO t / 2)) + 1 ∧
        (t + 1 < n → pg wf (mask wf) FO t < pg wf (mask wf) FO (t + 1))) := by
    intro t ht
    have e := hf t ht
    unfold forestAt at e
    simp only [strictB_eqR] at e
    obtain ⟨e1, e⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e2, e⟩ := (bAnd_iff _ _).1 e
    refine ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2, fun htR => ?_, fun htR => ?_⟩
    · rcases bIf_casesR e with ⟨_, e3⟩ | ⟨hc, _⟩
      · obtain ⟨f1, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f2, f3⟩ := (bAnd_iff _ _).1 e3
        exact ⟨Nat.eq_of_beq_eq_true f1, Nat.eq_of_beq_eq_true f2, Nat.eq_of_beq_eq_true f3⟩
      · have := blt_falseR hc
        omega
    · rcases bIf_casesR e with ⟨hc, _⟩ | ⟨_, e3⟩
      · have := Nat.blt_eq.mp hc
        omega
      · obtain ⟨f1, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f2, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f3, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f4, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f5, f6⟩ := (bAnd_iff _ _).1 e3
        refine ⟨Nat.blt_eq.mp f1, Nat.eq_of_beq_eq_true f2, Nat.eq_of_beq_eq_true f3,
          Nat.eq_of_beq_eq_true f4, Nat.eq_of_beq_eq_true f5, fun ht1 => ?_⟩
        rcases bIf_casesR f6 with ⟨_, f7⟩ | ⟨hc, _⟩
        · exact Nat.blt_eq.mp f7
        · have := blt_falseR hc
          omega
  have EA : ∀ e < 2 * n, gimg w G0 G1 (e % 2) (pg w (mask w) Q (e / 2)) < n ∧
      (pg w (mask w) ORD (gimg w G0 G1 (e % 2) (pg w (mask w) Q (e / 2))) < R ∨
        pg wf (mask wf) FO (pg w (mask w) ORD (gimg w G0 G1 (e % 2) (pg w (mask w) Q (e / 2))))
          ≤ e) := by
    intro e hE
    have h1 := he e hE
    unfold eventAt at h1
    simp only [strictB_eqR] at h1
    obtain ⟨g1, g2⟩ := (bAnd_iff _ _).1 h1
    refine ⟨Nat.blt_eq.mp g1, ?_⟩
    rcases bIf_casesR g2 with ⟨hc, _⟩ | ⟨_, g3⟩
    · exact Or.inl (Nat.blt_eq.mp hc)
    · exact Or.inr (Nat.ble_eq.mp g3)
  have QI : ∀ t1 < n, ∀ t2 < n, pg w (mask w) Q t1 = pg w (mask w) Q t2 → t1 = t2 := by
    intro t1 h1 t2 h2 e
    rw [← (FA t1 h1).2.1, ← (FA t2 h2).2.1, e]
  have QS : ∀ y < n, pg w (mask w) ORD y < n ∧ pg w (mask w) Q (pg w (mask w) ORD y) = y := by
    intro y hy
    let f : Fin n → Fin n := fun t => ⟨pg w (mask w) Q t, (FA t t.2).1⟩
    have hinj : Function.Injective f := fun t1 t2 e =>
      Fin.ext (QI t1 t1.2 t2 t2.2 (congrArg Fin.val e))
    obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
    have e : pg w (mask w) Q t = y := congrArg Fin.val ht
    refine ⟨?_, ?_⟩
    · rw [← e, (FA t t.2).2.1]
      exact t.2
    · rw [← e, (FA t t.2).2.1]
  have FM0 : ∀ d t1, R ≤ t1 → t1 + 1 + d < n →
      pg wf (mask wf) FO t1 < pg wf (mask wf) FO (t1 + 1 + d) := by
    intro d
    induction d with
    | zero =>
      intro t1 h1 h2
      exact ((FA t1 (by omega)).2.2.2 h1).2.2.2.2.2 (by omega)
    | succ d ih =>
      intro t1 h1 h2
      have h3 := ih t1 h1 (by omega)
      have h4 := ((FA (t1 + 1 + d) (by omega)).2.2.2 (by omega)).2.2.2.2.2 (by omega)
      rw [show t1 + 1 + (d + 1) = t1 + 1 + d + 1 by omega]
      omega
  have FM : ∀ t1 t2, R ≤ t1 → t1 < t2 → t2 < n →
      pg wf (mask wf) FO t1 < pg wf (mask wf) FO t2 := by
    intro t1 t2 h1 h12 h2
    have := FM0 (t2 - t1 - 1) t1 h1 (by omega)
    rwa [show t1 + 1 + (t2 - t1 - 1) = t2 by omega] at this
  have FB : ∀ t, R ≤ t → t < n → pg wf (mask wf) FO t < 2 * t := by
    intro t h1 h2
    have := ((FA t h2).2.2.2 h1).1
    omega
  have HEAD : ∀ j < n, ∀ c, FCut n wf R FO (2 * j) c → j < c := by
    intro j hj c ⟨c1, c2, c3⟩
    by_contra hle
    have hcn : c < n := by omega
    have h1 := FB c c1 hcn
    have h2 := (c3 c c1 hcn).1 (by omega)
    omega
  have STEP : ∀ j < n, ∀ k < 2, ∀ c (s : FSt), FCut n wf R FO (2 * j + k) c → j < c →
      FInv n w Q ORD DEP PAR GL c s →
      ∃ s', fStep n #[a, b] (pg w (mask w) Q j) k s = pure (.yield s') ∧
        ∃ c', FCut n wf R FO (2 * j + k + 1) c' ∧ j < c' ∧ FInv n w Q ORD DEP PAR GL c' s' := by
    intro j hj k hk c s hcut hjc hinv
    obtain ⟨c1, c2, c3⟩ := hcut
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hinv
    have hx := (FA j hj).1
    have hxo := (FA j hj).2.1
    obtain ⟨hyn, hev⟩ := EA (2 * j + k) (by omega)
    have e2 : (2 * j + k) % 2 = k := by omega
    have e3 : (2 * j + k) / 2 = j := by omega
    rw [e2, e3] at hyn hev
    obtain ⟨y, hy⟩ : ∃ y, y = gimg w G0 G1 k (pg w (mask w) Q j) := ⟨_, rfl⟩
    rw [← hy] at hyn hev
    have hgy : (#[a, b][k]!)[pg w (mask w) Q j]! = y := by
      rw [hy]
      exact gens2_getR ha hb hk hx
    obtain ⟨hto, hty⟩ := QS y hyn
    by_cases hseen : pg w (mask w) ORD y < c
    ·
      refine ⟨s, ?_, c, ⟨c1, c2, fun t ht1 ht2 => ⟨fun hlt => ?_, fun htc => ?_⟩⟩, hjc,
        ⟨s1, s2, s3, s4, s5, s6, s7⟩⟩
      · unfold fStep
        rw [hgy, if_neg]
        rw [(s7 y hyn).1]
        simp [hseen]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | h
        · exact (c3 t ht1 ht2).1 h
        · obtain ⟨-, g2, -⟩ := (FA t ht2).2.2.2 ht1
          rw [h, e2, e3, ← hy] at g2
          have : t = pg w (mask w) ORD y := QI t ht2 _ hto (by rw [hty]; exact g2.symm)
          omega
      · have := (c3 t ht1 ht2).2 htc
        omega
    ·
      have htR : R ≤ pg w (mask w) ORD y := by omega
      have hle : pg wf (mask wf) FO (pg w (mask w) ORD y) ≤ 2 * j + k := by
        rcases hev with h | h
        · omega
        · exact h
      have hnlt : ¬ pg wf (mask wf) FO (pg w (mask w) ORD y) < 2 * j + k := fun h =>
        hseen ((c3 _ htR hto).1 h)
      have hFe : pg wf (mask wf) FO (pg w (mask w) ORD y) = 2 * j + k := by omega
      have htc : pg w (mask w) ORD y = c := by
        by_contra hne
        have hgt : c < pg w (mask w) ORD y := by omega
        have h1 := FM c _ c1 hgt hto
        have h2 := (c3 c c1 (by omega)).1 (by omega)
        omega
      have hcn : c < n := by omega
      have hFc : pg wf (mask wf) FO c = 2 * j + k := by rw [← htc]; exact hFe
      obtain ⟨-, -, g3, g4, g5, -⟩ := (FA c hcn).2.2.2 c1
      rw [hFc, e3] at g3 g5
      rw [hFc, e2] at g4
      have hyc : y = pg w (mask w) Q c := by rw [← htc, hty]
      have hxc : pg w (mask w) ORD (pg w (mask w) Q j) < c := by rw [hxo]; exact hjc
      have hdx : s.1[pg w (mask w) Q j]! = pg w (mask w) DEP (pg w (mask w) Q j) := by
        rw [(s7 _ hx).2.1, if_pos hxc]
      refine ⟨(s.1.set! y (s.1[pg w (mask w) Q j]! + 1), s.2.1.set! y (pg w (mask w) Q j),
          s.2.2.1.set! y k, s.2.2.2.1.set! y true, s.2.2.2.2.push y), ?_, c + 1,
          ⟨by omega, by omega, fun t ht1 ht2 => ⟨fun hlt => ?_, fun htc' => ?_⟩⟩, by omega, ?_⟩
      · unfold fStep
        rw [hgy, if_pos]
        rw [(s7 y hyn).1]
        simp [hyn, hseen]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | h
        · have := (c3 t ht1 ht2).1 h
          omega
        · by_contra hne
          rcases Nat.lt_or_gt_of_ne (show t ≠ c by omega) with h' | h'
          · have := FM t c ht1 h' hcn
            omega
          · have := FM c t c1 h' ht2
            omega
      · rcases Nat.lt_succ_iff_lt_or_eq.1 htc' with h | h
        · have := (c3 t ht1 ht2).2 h
          omega
        · rw [h, hFc]
          omega
      · refine ⟨by dsimp only; rw [size_setR, s1], by dsimp only; rw [size_setR, s2],
          by dsimp only; rw [size_setR, s3], by dsimp only; rw [size_setR, s4],
          by dsimp only; rw [Array.size_push, s5], fun i hi => ?_, fun z hz => ?_⟩
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
          · rw [BfsReplay.push_lt (by rw [s5]; exact h)]
            exact s6 i h
          · rw [push_atR (by rw [s5]; exact h), h, hyc]
        · dsimp only
          rw [set_getR (by rw [s4]; exact hyn), set_getR (by rw [s1]; exact hyn),
            set_getR (by rw [s2]; exact hyn), set_getR (by rw [s3]; exact hyn)]
          by_cases hzy : z = y
          · rw [if_pos hzy, if_pos hzy, if_pos hzy, if_pos hzy, hzy, htc]
            refine ⟨by simp, ?_, ?_, ?_⟩
            · rw [if_pos (Nat.lt_succ_self c), hdx, hyc, g5]
            · rw [if_pos (Nat.lt_succ_self c), hyc, g3]
            · rw [if_pos (Nat.lt_succ_self c), hyc, g4]
          · rw [if_neg hzy, if_neg hzy, if_neg hzy, if_neg hzy]
            have hne : pg w (mask w) ORD z ≠ c := fun e =>
              hzy (by rw [← (QS z hz).2, e, ← hyc])
            have hiff : pg w (mask w) ORD z < c + 1 ↔ pg w (mask w) ORD z < c := by omega
            simp only [hiff]
            exact s7 z hz
  have hrl : roots.toList = (List.range R).map fun t => pg w (mask w) Q t := by
    apply List.ext_getElem
    · simp [hr.1]
    · intro i h1 h2
      have hi : i < R := by simpa [hr.1] using h1
      rw [List.getElem_map, List.getElem_range, Array.getElem_toList, ← hr.2 i hi,
        getElem!_pos roots i (by rw [hr.1]; exact hi)]
  have I0 : ∀ s0 : Array Bool × Array Nat,
      forIn (m := Id) roots (Array.replicate n false, (#[] : Array Nat)) (fRoot n) = s0 →
      s0.1.size = n ∧ s0.2.size = R ∧ (∀ i < R, s0.2[i]! = pg w (mask w) Q i) ∧
        ∀ y < n, s0.1[y]! = decide (pg w (mask w) ORD y < R) := by
    intro s0 hs0
    rw [← Array.forIn_toList, hrl, List.forIn_map, List.range_eq_range'] at hs0
    subst hs0
    refine BfsReplay.forIn_range'_yield R 0 _ _ (fun i (s : Array Bool × Array Nat) =>
        s.1.size = n ∧ s.2.size = i ∧ (∀ i' < i, s.2[i']! = pg w (mask w) Q i') ∧
          ∀ y < n, s.1[y]! = decide (pg w (mask w) ORD y < i))
      (fun i hi s ⟨h1, h2, h3, h4⟩ => ?_)
      ⟨by simp, rfl, fun i' hi' => absurd hi' (Nat.not_lt_zero _), fun y hy => ?_⟩
    · have hiN : i < n := by omega
      have hrn := (FA i hiN).1
      have hro := (FA i hiN).2.1
      refine ⟨(s.1.set! (pg w (mask w) Q i) true, s.2.push (pg w (mask w) Q i)), ?_,
        by dsimp only; rw [size_setR, h1], by dsimp only; rw [Array.size_push, h2],
        fun i' hi' => ?_, fun y hy => ?_⟩
      · rw [Nat.zero_add]
        unfold fRoot
        rw [if_pos]
        rw [h4 _ hrn, hro]
        simp [hrn]
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
        · rw [BfsReplay.push_lt (by rw [h2]; exact h)]
          exact h3 i' h
        · rw [push_atR (by rw [h2]; exact h), h]
      · dsimp only
        rw [set_getR (by rw [h1]; exact hrn), h4 y hy]
        by_cases hyr : y = pg w (mask w) Q i
        · rw [if_pos hyr, hyr, hro]
          simp
        · rw [if_neg hyr]
          have hne : pg w (mask w) ORD y ≠ i := fun e => hyr (by rw [← (QS y hy).2, e])
          have hiff : pg w (mask w) ORD y < i + 1 ↔ pg w (mask w) ORD y < i := by omega
          simp only [hiff]
    · rw [replicate_getR hy]
      simp
  have OUT : ∀ s0 : Array Bool × Array Nat,
      (s0.1.size = n ∧ s0.2.size = R ∧ (∀ i < R, s0.2[i]! = pg w (mask w) Q i) ∧
        ∀ y < n, s0.1[y]! = decide (pg w (mask w) ORD y < R)) →
      ∀ st : GSt, forIn (m := Id) [0:n] (Array.replicate n 0, Array.replicate n 0,
        Array.replicate n 0, s0.1, s0.2, 0) (fRound n #[a, b]) = st →
      ∃ c, FCut n wf R FO (2 * n) c ∧
        FInv n w Q ORD DEP PAR GL c (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1) := by
    intro s0 ⟨i1, i2, i3, i4⟩ st hst
    rw [forIn_rngR] at hst
    subst hst
    have STEPO : ∀ j < n, ∀ st : GSt, (st.2.2.2.2.2 = j ∧ ∃ c, FCut n wf R FO (2 * j) c ∧
          FInv n w Q ORD DEP PAR GL c (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1)) →
        ∃ st', fRound n #[a, b] (0 + j) st = pure (.yield st') ∧
          (st'.2.2.2.2.2 = j + 1 ∧ ∃ c, FCut n wf R FO (2 * (j + 1)) c ∧
            FInv n w Q ORD DEP PAR GL c (st'.1, st'.2.1, st'.2.2.1, st'.2.2.2.1, st'.2.2.2.2.1)) := by
      intro j hj st ⟨hh, c, hcut, hinv⟩
      have hjc : j < c := HEAD j hj c hcut
      obtain ⟨-, -, -, -, q5, q6, -⟩ := id hinv
      dsimp only at q5 q6
      have hlt : st.2.2.2.2.2 < st.2.2.2.2.1.size := by
        rw [hh, q5]
        exact hjc
      have hx : st.2.2.2.2.1[st.2.2.2.2.2]! = pg w (mask w) Q j := by
        rw [hh]
        exact q6 j hjc
      obtain ⟨c', hc1, -, hc3⟩ := BfsReplay.forIn_range'_yield 2 0
        (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1) (fStep n #[a, b] (pg w (mask w) Q j))
        (fun k (s : FSt) => ∃ c, FCut n wf R FO (2 * j + k) c ∧ j < c ∧
          FInv n w Q ORD DEP PAR GL c s)
        (fun k hk s ⟨c', h1, h2, h3⟩ => by
          rw [Nat.zero_add]
          exact STEP j hj k hk c' s h1 h2 h3)
        ⟨c, by rw [Nat.add_zero]; exact hcut, hjc, hinv⟩
      refine ⟨(_, _, _, _, _, st.2.2.2.2.2 + 1), ?_, by dsimp only; rw [hh], c',
        by rw [show 2 * (j + 1) = 2 * j + 2 by omega]; exact hc1, hc3⟩
      unfold fRound
      rw [if_pos hlt, hx, show (#[a, b] : Array (Array Nat)).size = 2 from rfl, forIn_rngR]
      rfl
    have INIT : (Array.replicate n 0, Array.replicate n 0, Array.replicate n 0, s0.1, s0.2,
          (0 : Nat)).2.2.2.2.2 = 0 ∧ ∃ c, FCut n wf R FO (2 * 0) c ∧
        FInv n w Q ORD DEP PAR GL c (Array.replicate n 0, Array.replicate n 0,
          Array.replicate n 0, s0.1, s0.2) := by
      refine ⟨rfl, R, ⟨le_refl R, hR, fun t ht1 ht2 => ⟨fun h => by omega, fun h => by omega⟩⟩,
        by simp, by simp, by simp, i1, i2, i3, fun y hy => ⟨i4 y hy, ?_, ?_, ?_⟩⟩
      all_goals
        dsimp only
        rw [replicate_getR hy]
        by_cases hp : pg w (mask w) ORD y < R
        · rw [if_pos hp]
          have h0 := (FA _ (QS y hy).1).2.2.1 hp
          rw [(QS y hy).2] at h0
          first | exact h0.1.symm | exact h0.2.1.symm | exact h0.2.2.symm
        · rw [if_neg hp]
    obtain ⟨-, c, hcut, hinv⟩ := BfsReplay.forIn_range'_yield n 0 _ (fRound n #[a, b])
      (fun j (st : GSt) => st.2.2.2.2.2 = j ∧ ∃ c, FCut n wf R FO (2 * j) c ∧
        FInv n w Q ORD DEP PAR GL c (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1))
      STEPO INIT
    exact ⟨c, hcut, hinv⟩
  have AE : ∀ (arr : Array Nat) (P : Nat), arr.size = n →
      (∀ y < n, arr[y]! = if pg w (mask w) ORD y < n then pg w (mask w) P y else 0) →
      arr = unpack n w P := by
    intro arr P hs ha'
    refine Array.ext (by rw [hs, unpack_sizeR]) fun y h1 h2 => ?_
    have hy : y < n := by omega
    rw [← getElem!_pos arr y h1, ← getElem!_pos (unpack n w P) y h2, ha' y hy, unpack_getR hy,
      if_pos (QS y hy).1]
  have key : ∀ st : GSt, (∃ c, FCut n wf R FO (2 * n) c ∧
        FInv n w Q ORD DEP PAR GL c (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1)) →
      (st.1, st.2.1, st.2.2.1) = (unpack n w DEP, unpack n w PAR, unpack n w GL) := by
    rintro st ⟨c, ⟨c1, c2, c3⟩, ⟨h1, h2, h3, -, -, -, h7⟩⟩
    have hcn : c = n := by
      by_contra hne
      have hlt : c < n := by omega
      have h8 := FB c c1 hlt
      have := (c3 c c1 hlt).1 (by omega)
      omega
    rw [hcn] at h7
    dsimp only at h1 h2 h3 h7
    rw [AE st.1 DEP h1 (fun y hy => (h7 y hy).2.1), AE st.2.1 PAR h2 (fun y hy => (h7 y hy).2.2.1),
      AE st.2.2.1 GL h3 (fun y hy => (h7 y hy).2.2.2)]
  rw [orbitForest_eqR]
  exact key _ (OUT _ (I0 _ rfl) _ rfl)

end CFSG.KS.SporSch.RuOrbKS

end

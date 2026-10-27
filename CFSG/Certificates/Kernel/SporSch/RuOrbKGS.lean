module

public import Certificates.Data.Kernel.SporSch.RuOrbKG
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.RuOrbit
import CFSG.Certificates.Kernel.Spor.BfsReplay
public import CFSG.Sporadic.Schreier.RuCore

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

private theorem strictB_eqG (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem bIf_casesG {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

private theorem blt_falseG {a b : Nat} (h : Nat.blt a b = false) : b ≤ a :=
  Nat.not_lt.1 fun hlt => by
    rw [Nat.blt_eq.mpr hlt] at h
    exact Bool.noConfusion h

private theorem replicate_getG {α : Type} [Inhabited α] {n y : Nat} {v : α} (hy : y < n) :
    (Array.replicate n v)[y]! = v := by
  rw [getElem!_pos _ y (by simpa using hy), Array.getElem_replicate]

private theorem size_setG {α : Type} {a : Array α} {i : Nat} {v : α} :
    (a.set! i v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

private theorem set_getG {α : Type} [Inhabited α] {a : Array α} {i j : Nat} {v : α}
    (hi : i < a.size) : (a.set! i v)[j]! = if j = i then v else a[j]! := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set! i v).size := by rw [size_setG]; exact hj
    rw [getElem!_pos _ j hj', getElem!_pos a j hj]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [if_neg (Ne.symm hij), if_neg hij]
  · have hj' : ¬ j < (a.set! i v).size := by rw [size_setG]; exact hj
    have hij : j ≠ i := by omega
    rw [getElem!_neg _ j hj', getElem!_neg a j hj, if_neg hij]

private theorem push_atG {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat}
    (h : i = a.size) : (a.push x)[i]! = x := by
  subst h
  exact BfsReplay.push_eq

private theorem forIn_rngG {β : Type} (k : Nat) (init : β) (f : Nat → β → Id (ForInStep β)) :
    forIn (m := Id) [0:k] init f = forIn (List.range' 0 k) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hl : List.range' [0:k].start [0:k].size [0:k].step = List.range' 0 k := by
    simp [Std.Legacy.Range.size]
  rw [hl]

private theorem div_mulAddG {kG j k : Nat} (hk : k < kG) : (kG * j + k) / kG = j := by
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hk, Nat.add_zero]

private theorem mod_mulAddG {kG j k : Nat} (hk : k < kG) : (kG * j + k) % kG = k := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

private theorem mul_leG {kG a b : Nat} (h : a ≤ b) : kG * a ≤ kG * b := Nat.mul_le_mul_left kG h

theorem partKG_sound {n kG R : Nat} {g : Nat → Nat → Nat} {LAB Q DEP PAR GI : Nat → Nat}
    {gens : Array (Array Nat)} {lab roots dep par gl : Array Nat}
    (hs : gens.size = kG) (hg : ∀ k < kG, ∀ x < n, (gens[k]!)[x]! = g k x)
    (hr : roots.size = R ∧ ∀ t < R, roots[t]! = Q t)
    (hlab : ∀ x < n, lab[x]! = LAB x) (hdep : ∀ x < n, dep[x]! = DEP x)
    (hpar : ∀ x < n, par[x]! = PAR x) (hgl : ∀ x < n, gl[x]! = GI x)
    (hp : ∀ x < n, partAtG n kG R g LAB Q DEP PAR GI x = true)
    (hk : ∀ k < R, rootAtG n LAB Q k = true) :
    orbitPartOK n gens lab roots dep par gl = true := by
  unfold orbitPartOK
  rw [Bool.and_eq_true, allLt_iff, allLt_iff, hr.1]
  refine ⟨fun x hx => ?_, fun k hk' => ?_⟩
  · have e := hp x hx
    unfold partAtG at e
    simp only [strictB_eqG] at e
    obtain ⟨e0, e2⟩ := (bAnd_iff _ _).1 e
    rw [Bool.and_eq_true, allLt_iff, hs]
    refine ⟨fun k hk => ?_, ?_⟩
    · have e1 := allN_spec e0 k hk
      obtain ⟨e1a, e1b⟩ := (bAnd_iff _ _).1 e1
      have y0 : g k x < n := Nat.blt_eq.mp e1a
      rw [hg k hk x hx, hlab _ y0, hlab x hx, Nat.eq_of_beq_eq_true e1b]
      simp [y0]
    · rw [hdep x hx, hlab x hx, hpar x hx, hgl x hx]
      rcases bIf_casesG e2 with ⟨hd, e3⟩ | ⟨hd, e3⟩
      · have hd' : DEP x = 0 := Nat.eq_of_beq_eq_true hd
        obtain ⟨e4, e5⟩ := (bAnd_iff _ _).1 e3
        have hc : LAB x < R := Nat.blt_eq.mp e4
        rw [hd', hr.2 _ hc, Nat.eq_of_beq_eq_true e5]
        simp
      · obtain ⟨f1, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f2, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f3, f4⟩ := (bAnd_iff _ _).1 e3
        have hpn : PAR x < n := Nat.blt_eq.mp f1
        have hdl : DEP (PAR x) < DEP x := Nat.blt_eq.mp f2
        have hgk : GI x < kG := Nat.blt_eq.mp f3
        have hd' : DEP x ≠ 0 := by omega
        rw [hdep _ hpn, hg _ hgk _ hpn, Nat.eq_of_beq_eq_true f4]
        simp [hd', hpn, hdl, hgk]
  · have e := hk k hk'
    unfold rootAtG at e
    simp only [strictB_eqG] at e
    obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 e
    have hrn : Q k < n := Nat.blt_eq.mp e1
    rw [hr.2 k hk', hlab _ hrn, Nat.eq_of_beq_eq_true e2]
    simp [hrn]

private abbrev FStG :=Array Nat × Array Nat × Array Nat × Array Bool × Array Nat

private abbrev GStG :=Array Nat × Array Nat × Array Nat × Array Bool × Array Nat × Nat

private def fRootG (n r : Nat) (s : Array Bool × Array Nat) :
    Id (ForInStep (Array Bool × Array Nat)) :=
  if (decide (r < n) && !s.1[r]!) = true then pure (.yield (s.1.set! r true, s.2.push r))
  else pure (.yield (s.1, s.2))

private def fStepG (n : Nat) (gens : Array (Array Nat)) (x k : Nat) (s : FStG) :
    Id (ForInStep FStG) :=
  if (decide ((gens[k]!)[x]! < n) && !s.2.2.2.1[(gens[k]!)[x]!]!) = true then
    pure (.yield (s.1.set! (gens[k]!)[x]! (s.1[x]! + 1), s.2.1.set! (gens[k]!)[x]! x,
      s.2.2.1.set! (gens[k]!)[x]! k, s.2.2.2.1.set! (gens[k]!)[x]! true,
      s.2.2.2.2.push (gens[k]!)[x]!))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

private def fRoundG (n : Nat) (gens : Array (Array Nat)) (_ : Nat) (s : GStG) :
    Id (ForInStep GStG) :=
  if s.2.2.2.2.2 < s.2.2.2.2.1.size then do
    let s' ← forIn [0:gens.size] (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1)
      (fStepG n gens s.2.2.2.2.1[s.2.2.2.2.2]!)
    pure (.yield (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2.1, s'.2.2.2.2, s.2.2.2.2.2 + 1))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

private theorem orbitForest_eqG (n : Nat) (gens : Array (Array Nat)) (roots : Array Nat) :
    orbitForest n gens roots =
      (let s0 := (forIn roots (Array.replicate n false, (#[] : Array Nat)) (fRootG n) :
          Id (Array Bool × Array Nat))
       let s := (forIn [0:n] (Array.replicate n 0, Array.replicate n 0, Array.replicate n 0,
          s0.1, s0.2, 0) (fRoundG n gens) : Id GStG)
       (s.1, s.2.1, s.2.2.1)) := rfl

private def FCutG (n R : Nat) (FO : Nat → Nat) (e c : Nat) : Prop :=
  R ≤ c ∧ c ≤ n ∧ ∀ t, R ≤ t → t < n → (FO t < e ↔ t < c)

private def FInvG (n : Nat) (Q ORD DEP PAR GI : Nat → Nat) (c : Nat) (s : FStG) : Prop :=
  s.1.size = n ∧ s.2.1.size = n ∧ s.2.2.1.size = n ∧ s.2.2.2.1.size = n ∧
    s.2.2.2.2.size = c ∧ (∀ i < c, s.2.2.2.2[i]! = Q i) ∧
    ∀ y < n, s.2.2.2.1[y]! = decide (ORD y < c) ∧
      s.1[y]! = (if ORD y < c then DEP y else 0) ∧
      s.2.1[y]! = (if ORD y < c then PAR y else 0) ∧
      s.2.2.1[y]! = (if ORD y < c then GI y else 0)

theorem forestKG_sound {n kG R : Nat} {g : Nat → Nat → Nat} {Q ORD FO DEP PAR GI : Nat → Nat}
    {gens : Array (Array Nat)} {roots : Array Nat} (hkG : 0 < kG)
    (hs : gens.size = kG) (hg : ∀ k < kG, ∀ x < n, (gens[k]!)[x]! = g k x)
    (hr : roots.size = R ∧ ∀ t < R, roots[t]! = Q t) (hR : R ≤ n)
    (hf : ∀ t < n, forestAtG n kG R g Q ORD FO DEP PAR GI t = true)
    (he : ∀ e < kG * n, eventAtG n kG R g Q ORD FO e = true) :
    (orbitForest n gens roots).1.size = n ∧ (orbitForest n gens roots).2.1.size = n ∧
      (orbitForest n gens roots).2.2.size = n ∧ ∀ y < n,
        (orbitForest n gens roots).1[y]! = DEP y ∧ (orbitForest n gens roots).2.1[y]! = PAR y ∧
        (orbitForest n gens roots).2.2[y]! = GI y := by
  have FA : ∀ t < n, Q t < n ∧ ORD (Q t) = t ∧
      (t < R → DEP (Q t) = 0 ∧ PAR (Q t) = 0 ∧ GI (Q t) = 0) ∧
      (R ≤ t → FO t / kG < t ∧ g (FO t % kG) (Q (FO t / kG)) = Q t ∧
        PAR (Q t) = Q (FO t / kG) ∧ GI (Q t) = FO t % kG ∧
        DEP (Q t) = DEP (Q (FO t / kG)) + 1 ∧ (t + 1 < n → FO t < FO (t + 1))) := by
    intro t ht
    have e := hf t ht
    unfold forestAtG at e
    simp only [strictB_eqG] at e
    obtain ⟨e1, e⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e2, e⟩ := (bAnd_iff _ _).1 e
    refine ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2, fun htR => ?_, fun htR => ?_⟩
    · rcases bIf_casesG e with ⟨_, e3⟩ | ⟨hc, _⟩
      · obtain ⟨f1, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f2, f3⟩ := (bAnd_iff _ _).1 e3
        exact ⟨Nat.eq_of_beq_eq_true f1, Nat.eq_of_beq_eq_true f2, Nat.eq_of_beq_eq_true f3⟩
      · have := blt_falseG hc
        omega
    · rcases bIf_casesG e with ⟨hc, _⟩ | ⟨_, e3⟩
      · have := Nat.blt_eq.mp hc
        omega
      · obtain ⟨f1, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f2, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f3, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f4, e3⟩ := (bAnd_iff _ _).1 e3
        obtain ⟨f5, f6⟩ := (bAnd_iff _ _).1 e3
        refine ⟨Nat.blt_eq.mp f1, Nat.eq_of_beq_eq_true f2, Nat.eq_of_beq_eq_true f3,
          Nat.eq_of_beq_eq_true f4, Nat.eq_of_beq_eq_true f5, fun ht1 => ?_⟩
        rcases bIf_casesG f6 with ⟨_, f7⟩ | ⟨hc, _⟩
        · exact Nat.blt_eq.mp f7
        · have := blt_falseG hc
          omega
  have EA : ∀ e < kG * n, g (e % kG) (Q (e / kG)) < n ∧
      (ORD (g (e % kG) (Q (e / kG))) < R ∨ FO (ORD (g (e % kG) (Q (e / kG)))) ≤ e) := by
    intro e hE
    have h1 := he e hE
    unfold eventAtG at h1
    simp only [strictB_eqG] at h1
    obtain ⟨g1, g2⟩ := (bAnd_iff _ _).1 h1
    refine ⟨Nat.blt_eq.mp g1, ?_⟩
    rcases bIf_casesG g2 with ⟨hc, _⟩ | ⟨_, g3⟩
    · exact Or.inl (Nat.blt_eq.mp hc)
    · exact Or.inr (Nat.ble_eq.mp g3)
  have QI : ∀ t1 < n, ∀ t2 < n, Q t1 = Q t2 → t1 = t2 := by
    intro t1 h1 t2 h2 e
    rw [← (FA t1 h1).2.1, ← (FA t2 h2).2.1, e]
  have QS : ∀ y < n, ORD y < n ∧ Q (ORD y) = y := by
    intro y hy
    let f : Fin n → Fin n := fun t => ⟨Q t, (FA t t.2).1⟩
    have hinj : Function.Injective f := fun t1 t2 e =>
      Fin.ext (QI t1 t1.2 t2 t2.2 (congrArg Fin.val e))
    obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
    have e : Q t = y := congrArg Fin.val ht
    refine ⟨?_, ?_⟩
    · rw [← e, (FA t t.2).2.1]
      exact t.2
    · rw [← e, (FA t t.2).2.1]
  have FM0 : ∀ d t1, R ≤ t1 → t1 + 1 + d < n → FO t1 < FO (t1 + 1 + d) := by
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
  have FM : ∀ t1 t2, R ≤ t1 → t1 < t2 → t2 < n → FO t1 < FO t2 := by
    intro t1 t2 h1 h12 h2
    have := FM0 (t2 - t1 - 1) t1 h1 (by omega)
    rwa [show t1 + 1 + (t2 - t1 - 1) = t2 by omega] at this
  have FB : ∀ t, R ≤ t → t < n → FO t < kG * t := by
    intro t h1 h2
    have := ((FA t h2).2.2.2 h1).1
    rw [Nat.div_lt_iff_lt_mul hkG, Nat.mul_comm] at this
    exact this
  have HEAD : ∀ j < n, ∀ c, FCutG n R FO (kG * j) c → j < c := by
    intro j hj c ⟨c1, c2, c3⟩
    by_contra hle
    have hcn : c < n := by omega
    have h1 := FB c c1 hcn
    have h0 : kG * c ≤ kG * j := mul_leG (by omega)
    have h2 := (c3 c c1 hcn).1 (by omega)
    omega
  have STEP : ∀ j < n, ∀ k < kG, ∀ c (s : FStG), FCutG n R FO (kG * j + k) c → j < c →
      FInvG n Q ORD DEP PAR GI c s →
      ∃ s', fStepG n gens (Q j) k s = pure (.yield s') ∧
        ∃ c', FCutG n R FO (kG * j + k + 1) c' ∧ j < c' ∧ FInvG n Q ORD DEP PAR GI c' s' := by
    intro j hj k hk c s hcut hjc hinv
    obtain ⟨c1, c2, c3⟩ := hcut
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hinv
    have hx := (FA j hj).1
    have hxo := (FA j hj).2.1
    have hEn : kG * j + k < kG * n := by
      have : kG * (j + 1) ≤ kG * n := mul_leG (by omega)
      rw [Nat.mul_succ] at this
      omega
    obtain ⟨hyn, hev⟩ := EA (kG * j + k) hEn
    have e2 : (kG * j + k) % kG = k := mod_mulAddG hk
    have e3 : (kG * j + k) / kG = j := div_mulAddG hk
    rw [e2, e3] at hyn hev
    obtain ⟨y, hy⟩ : ∃ y, y = g k (Q j) := ⟨_, rfl⟩
    rw [← hy] at hyn hev
    have hgy : (gens[k]!)[Q j]! = y := by
      rw [hy]
      exact hg k hk _ hx
    obtain ⟨hto, hty⟩ := QS y hyn
    by_cases hseen : ORD y < c
    ·
      refine ⟨s, ?_, c, ⟨c1, c2, fun t ht1 ht2 => ⟨fun hlt => ?_, fun htc => ?_⟩⟩, hjc,
        ⟨s1, s2, s3, s4, s5, s6, s7⟩⟩
      · unfold fStepG
        rw [hgy, if_neg]
        rw [(s7 y hyn).1]
        simp [hseen]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | h
        · exact (c3 t ht1 ht2).1 h
        · obtain ⟨-, g2, -⟩ := (FA t ht2).2.2.2 ht1
          rw [h, e2, e3, ← hy] at g2
          have : t = ORD y := QI t ht2 _ hto (by rw [hty]; exact g2.symm)
          omega
      · have := (c3 t ht1 ht2).2 htc
        omega
    ·
      have htR : R ≤ ORD y := by omega
      have hle : FO (ORD y) ≤ kG * j + k := by
        rcases hev with h | h
        · omega
        · exact h
      have hnlt : ¬ FO (ORD y) < kG * j + k := fun h => hseen ((c3 _ htR hto).1 h)
      have hFe : FO (ORD y) = kG * j + k := by omega
      have htc : ORD y = c := by
        by_contra hne
        have hgt : c < ORD y := by omega
        have h1 := FM c _ c1 hgt hto
        have h2 := (c3 c c1 (by omega)).1 (by omega)
        omega
      have hcn : c < n := by omega
      have hFc : FO c = kG * j + k := by rw [← htc]; exact hFe
      obtain ⟨-, -, g3, g4, g5, -⟩ := (FA c hcn).2.2.2 c1
      rw [hFc, e3] at g3 g5
      rw [hFc, e2] at g4
      have hyc : y = Q c := by rw [← htc, hty]
      have hxc : ORD (Q j) < c := by rw [hxo]; exact hjc
      have hdx : s.1[Q j]! = DEP (Q j) := by
        rw [(s7 _ hx).2.1, if_pos hxc]
      refine ⟨(s.1.set! y (s.1[Q j]! + 1), s.2.1.set! y (Q j),
          s.2.2.1.set! y k, s.2.2.2.1.set! y true, s.2.2.2.2.push y), ?_, c + 1,
          ⟨by omega, by omega, fun t ht1 ht2 => ⟨fun hlt => ?_, fun htc' => ?_⟩⟩, by omega, ?_⟩
      · unfold fStepG
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
      · refine ⟨by dsimp only; rw [size_setG, s1], by dsimp only; rw [size_setG, s2],
          by dsimp only; rw [size_setG, s3], by dsimp only; rw [size_setG, s4],
          by dsimp only; rw [Array.size_push, s5], fun i hi => ?_, fun z hz => ?_⟩
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
          · rw [BfsReplay.push_lt (by rw [s5]; exact h)]
            exact s6 i h
          · rw [push_atG (by rw [s5]; exact h), h, hyc]
        · dsimp only
          rw [set_getG (by rw [s4]; exact hyn), set_getG (by rw [s1]; exact hyn),
            set_getG (by rw [s2]; exact hyn), set_getG (by rw [s3]; exact hyn)]
          by_cases hzy : z = y
          · rw [if_pos hzy, if_pos hzy, if_pos hzy, if_pos hzy, hzy, htc]
            refine ⟨by simp, ?_, ?_, ?_⟩
            · rw [if_pos (Nat.lt_succ_self c), hdx, hyc, g5]
            · rw [if_pos (Nat.lt_succ_self c), hyc, g3]
            · rw [if_pos (Nat.lt_succ_self c), hyc, g4]
          · rw [if_neg hzy, if_neg hzy, if_neg hzy, if_neg hzy]
            have hne : ORD z ≠ c := fun e => hzy (by rw [← (QS z hz).2, e, ← hyc])
            have hiff : ORD z < c + 1 ↔ ORD z < c := by omega
            simp only [hiff]
            exact s7 z hz
  have hrl : roots.toList = (List.range R).map fun t => Q t := by
    apply List.ext_getElem
    · simp [hr.1]
    · intro i h1 h2
      have hi : i < R := by simpa [hr.1] using h1
      rw [List.getElem_map, List.getElem_range, Array.getElem_toList, ← hr.2 i hi,
        getElem!_pos roots i (by rw [hr.1]; exact hi)]
  have I0 : ∀ s0 : Array Bool × Array Nat,
      forIn (m := Id) roots (Array.replicate n false, (#[] : Array Nat)) (fRootG n) = s0 →
      s0.1.size = n ∧ s0.2.size = R ∧ (∀ i < R, s0.2[i]! = Q i) ∧
        ∀ y < n, s0.1[y]! = decide (ORD y < R) := by
    intro s0 hs0
    rw [← Array.forIn_toList, hrl, List.forIn_map, List.range_eq_range'] at hs0
    subst hs0
    refine BfsReplay.forIn_range'_yield R 0 _ _ (fun i (s : Array Bool × Array Nat) =>
        s.1.size = n ∧ s.2.size = i ∧ (∀ i' < i, s.2[i']! = Q i') ∧
          ∀ y < n, s.1[y]! = decide (ORD y < i))
      (fun i hi s ⟨h1, h2, h3, h4⟩ => ?_)
      ⟨by simp, rfl, fun i' hi' => absurd hi' (Nat.not_lt_zero _), fun y hy => ?_⟩
    · have hiN : i < n := by omega
      have hrn := (FA i hiN).1
      have hro := (FA i hiN).2.1
      refine ⟨(s.1.set! (Q i) true, s.2.push (Q i)), ?_,
        by dsimp only; rw [size_setG, h1], by dsimp only; rw [Array.size_push, h2],
        fun i' hi' => ?_, fun y hy => ?_⟩
      · rw [Nat.zero_add]
        unfold fRootG
        rw [if_pos]
        rw [h4 _ hrn, hro]
        simp [hrn]
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
        · rw [BfsReplay.push_lt (by rw [h2]; exact h)]
          exact h3 i' h
        · rw [push_atG (by rw [h2]; exact h), h]
      · dsimp only
        rw [set_getG (by rw [h1]; exact hrn), h4 y hy]
        by_cases hyr : y = Q i
        · rw [if_pos hyr, hyr, hro]
          simp
        · rw [if_neg hyr]
          have hne : ORD y ≠ i := fun e => hyr (by rw [← (QS y hy).2, e])
          have hiff : ORD y < i + 1 ↔ ORD y < i := by omega
          simp only [hiff]
    · rw [replicate_getG hy]
      simp
  have OUT : ∀ s0 : Array Bool × Array Nat,
      (s0.1.size = n ∧ s0.2.size = R ∧ (∀ i < R, s0.2[i]! = Q i) ∧
        ∀ y < n, s0.1[y]! = decide (ORD y < R)) →
      ∀ st : GStG, forIn (m := Id) [0:n] (Array.replicate n 0, Array.replicate n 0,
        Array.replicate n 0, s0.1, s0.2, 0) (fRoundG n gens) = st →
      ∃ c, FCutG n R FO (kG * n) c ∧
        FInvG n Q ORD DEP PAR GI c (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1) := by
    intro s0 ⟨i1, i2, i3, i4⟩ st hst
    rw [forIn_rngG] at hst
    subst hst
    have STEPO : ∀ j < n, ∀ st : GStG, (st.2.2.2.2.2 = j ∧ ∃ c, FCutG n R FO (kG * j) c ∧
          FInvG n Q ORD DEP PAR GI c (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1)) →
        ∃ st', fRoundG n gens (0 + j) st = pure (.yield st') ∧
          (st'.2.2.2.2.2 = j + 1 ∧ ∃ c, FCutG n R FO (kG * (j + 1)) c ∧
            FInvG n Q ORD DEP PAR GI c
              (st'.1, st'.2.1, st'.2.2.1, st'.2.2.2.1, st'.2.2.2.2.1)) := by
      intro j hj st ⟨hh, c, hcut, hinv⟩
      have hjc : j < c := HEAD j hj c hcut
      obtain ⟨-, -, -, -, q5, q6, -⟩ := id hinv
      dsimp only at q5 q6
      have hlt : st.2.2.2.2.2 < st.2.2.2.2.1.size := by
        rw [hh, q5]
        exact hjc
      have hx : st.2.2.2.2.1[st.2.2.2.2.2]! = Q j := by
        rw [hh]
        exact q6 j hjc
      obtain ⟨c', hc1, -, hc3⟩ := BfsReplay.forIn_range'_yield kG 0
        (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1) (fStepG n gens (Q j))
        (fun k (s : FStG) => ∃ c, FCutG n R FO (kG * j + k) c ∧ j < c ∧
          FInvG n Q ORD DEP PAR GI c s)
        (fun k hk s ⟨c', h1, h2, h3⟩ => by
          rw [Nat.zero_add]
          exact STEP j hj k hk c' s h1 h2 h3)
        ⟨c, by rw [Nat.add_zero]; exact hcut, hjc, hinv⟩
      refine ⟨(_, _, _, _, _, st.2.2.2.2.2 + 1), ?_, by dsimp only; rw [hh], c',
        by rw [Nat.mul_succ]; exact hc1, hc3⟩
      unfold fRoundG
      rw [if_pos hlt, hx, hs, forIn_rngG]
      rfl
    have INIT : (Array.replicate n 0, Array.replicate n 0, Array.replicate n 0, s0.1, s0.2,
          (0 : Nat)).2.2.2.2.2 = 0 ∧ ∃ c, FCutG n R FO (kG * 0) c ∧
        FInvG n Q ORD DEP PAR GI c (Array.replicate n 0, Array.replicate n 0,
          Array.replicate n 0, s0.1, s0.2) := by
      refine ⟨rfl, R, ⟨le_refl R, hR, fun t ht1 ht2 => ⟨fun h => by simp at h, fun h => by omega⟩⟩,
        by simp, by simp, by simp, i1, i2, i3, fun y hy => ⟨i4 y hy, ?_, ?_, ?_⟩⟩
      all_goals
        dsimp only
        rw [replicate_getG hy]
        by_cases hp : ORD y < R
        · rw [if_pos hp]
          have h0 := (FA _ (QS y hy).1).2.2.1 hp
          rw [(QS y hy).2] at h0
          first | exact h0.1.symm | exact h0.2.1.symm | exact h0.2.2.symm
        · rw [if_neg hp]
    obtain ⟨-, c, hcut, hinv⟩ := BfsReplay.forIn_range'_yield n 0 _ (fRoundG n gens)
      (fun j (st : GStG) => st.2.2.2.2.2 = j ∧ ∃ c, FCutG n R FO (kG * j) c ∧
        FInvG n Q ORD DEP PAR GI c (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1))
      STEPO INIT
    exact ⟨c, hcut, hinv⟩
  have key : ∀ st : GStG, (∃ c, FCutG n R FO (kG * n) c ∧
        FInvG n Q ORD DEP PAR GI c (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1)) →
      st.1.size = n ∧ st.2.1.size = n ∧ st.2.2.1.size = n ∧ ∀ y < n,
        st.1[y]! = DEP y ∧ st.2.1[y]! = PAR y ∧ st.2.2.1[y]! = GI y := by
    rintro st ⟨c, ⟨c1, c2, c3⟩, ⟨h1, h2, h3, -, -, -, h7⟩⟩
    have hcn : c = n := by
      by_contra hne
      have hlt : c < n := by omega
      have h8 := FB c c1 hlt
      have h9 : kG * c ≤ kG * n := mul_leG (by omega)
      have := (c3 c c1 hlt).1 (by omega)
      omega
    rw [hcn] at h7
    dsimp only at h1 h2 h3 h7
    refine ⟨h1, h2, h3, fun y hy => ?_⟩
    obtain ⟨-, d1, d2, d3⟩ := h7 y hy
    rw [if_pos (QS y hy).1] at d1 d2 d3
    exact ⟨d1, d2, d3⟩
  rw [orbitForest_eqG]
  exact key _ (OUT _ (I0 _ rfl) _ rfl)

theorem orbitPartOK_forestKG {n kG R : Nat} {g : Nat → Nat → Nat}
    {LAB Q ORD FO DEP PAR GI : Nat → Nat} {gens : Array (Array Nat)} {lab roots : Array Nat}
    (hkG : 0 < kG) (hs : gens.size = kG) (hg : ∀ k < kG, ∀ x < n, (gens[k]!)[x]! = g k x)
    (hr : roots.size = R ∧ ∀ t < R, roots[t]! = Q t) (hR : R ≤ n)
    (hlab : ∀ x < n, lab[x]! = LAB x)
    (hf : ∀ t < n, forestAtG n kG R g Q ORD FO DEP PAR GI t = true)
    (he : ∀ e < kG * n, eventAtG n kG R g Q ORD FO e = true)
    (hp : ∀ x < n, partAtG n kG R g LAB Q DEP PAR GI x = true)
    (hk : ∀ k < R, rootAtG n LAB Q k = true) :
    orbitPartOK n gens lab roots (orbitForest n gens roots).1 (orbitForest n gens roots).2.1
      (orbitForest n gens roots).2.2 = true := by
  obtain ⟨-, -, -, hF⟩ := forestKG_sound hkG hs hg hr hR hf he
  exact partKG_sound hs hg hr hlab (fun x hx => (hF x hx).1) (fun x hx => (hF x hx).2.1)
    (fun x hx => (hF x hx).2.2) hp hk

end CFSG.KS.SporSch

end

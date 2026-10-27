module

public import Certificates.Data.Kernel.Fi23P.Defs
public import Certificates.Data.CFSGNative.MonsterAxis.Fi23Sp8
import CFSG.Certificates.Kernel.Fi23P.Spec
import CFSG.Certificates.Kernel.Fi22LH.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Fintype.EquivFin

namespace CFSG.KC.Fi23P

open CFSG.KS.Raw.Orb CFSG.KS.Fi22LH CFSG.Sporadic.Th.Native CFSG.Monster.Existence.Fi23Sp8.Native

theorem osGetSet {xs : Array Nat} {i j : Nat} (hi : i < xs.size) (hj : j < xs.size) (v : Nat) :
    (xs.set! i v)[j]! = if i = j then v else xs[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by rw [Array.size_setIfInBounds]; exact hj)]
  by_cases e : i = j
  · subst e
    rw [if_pos rfl, Array.getElem_setIfInBounds_self]
  · rw [if_neg e, Array.getElem_setIfInBounds_ne hj e, getElem!_pos xs j hj]

theorem osSizeSet (xs : Array Nat) (i v : Nat) : (xs.set! i v).size = xs.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem osGetPushLt (xs : Array Nat) (x : Nat) {i : Nat} (h : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by rw [Array.size_push]; omega), getElem!_pos xs i h,
    Array.getElem_push_lt h]

theorem osGetPushEq (xs : Array Nat) (x : Nat) : (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem osGetReplicate {z v : Nat} (hz : z < 31671) : (Array.replicate 31671 v)[z]! = v := by
  rw [getElem!_pos _ z (by rw [Array.size_replicate]; exact hz), Array.getElem_replicate]

theorem osMemGIdx {k : Nat} (hk : gOK k = true) : k ∈ gIdx () := by
  obtain ⟨h1, h2⟩ := (gOK_iff k).1 hk
  simp only [gIdx, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem osKeyOf (gen par pos : Nat → Nat) (x : Nat) :
    keyOf gen par pos x = 16 * pos (par x) + gen x := rfl

theorem osOfFn (a : Array Nat) (g : Nat → Nat) (hs : a.size = 31671)
    (hg : ∀ k < 31671, a[k]! = g k) : a = Array.ofFn (n := 31671) fun k => g k.val := by
  apply Array.ext (by rw [hs, Array.size_ofFn])
  intro i hi1 hi2
  rw [Array.getElem_ofFn, ← getElem!_pos a i hi1, hg i (by omega)]

theorem osListLoop {β : Type} (J : Nat → β → Prop) (f : Nat → β → Id (ForInStep β))
    (rt : Nat → Nat) : ∀ (m s : Nat) (b : β),
    (∀ c b, s ≤ c → c < s + m → J c b → ∃ b', f (rt c) b = .yield b' ∧ J (c + 1) b') →
    J s b → J (s + m) (forIn ((List.range' s m).map rt) b f)
  | 0, s, b, _, h0 => h0
  | m + 1, s, b, hst, h0 => by
    rw [List.range'_succ, List.map_cons, List.forIn_cons]
    obtain ⟨b', hf, hb'⟩ := hst s b (Nat.le_refl _) (by omega) h0
    rw [hf]
    have e : s + (m + 1) = s + 1 + m := by omega
    rw [e]
    exact osListLoop J f rt m (s + 1) b'
      (fun c b h1 h2 h3 => hst c b (by omega) (by omega) h3) hb'

theorem osBindEx {β : Type} (P : β → Prop) (x : Id β)
    (g : β → Id (Array Nat × Array Nat × Array Nat)) (hx : P x) :
    ∃ s, (x >>= g).run = (g s).run ∧ P s := ⟨x, rfl, hx⟩

theorem osLStepYield {β : Type} {I Q : β → Prop} {x : β} (h : I x) :
    LStep I Q (pure (ForInStep.yield x) : Id (ForInStep β)) := h

theorem osLStepDone {β : Type} {I Q : β → Prop} {x : β} (h : Q x) :
    LStep I Q (pure (ForInStep.done x) : Id (ForInStep β)) := h

def ArrOK (lab par gen : Nat → Nat) (D : Nat → Prop) (la pa ga : Array Nat) : Prop :=
  la.size = 31671 ∧ pa.size = 31671 ∧ ga.size = 31671 ∧ ∀ z < 31671,
    (D z → la[z]! = lab z ∧ pa[z]! = par z ∧ ga[z]! = gen z) ∧
    (¬ D z → la[z]! = 3 ∧ pa[z]! = 0 ∧ ga[z]! = 0)

theorem ArrOK.congr {lab par gen : Nat → Nat} {D D' : Nat → Prop} {la pa ga : Array Nat}
    (h : ArrOK lab par gen D la pa ga) (e : ∀ z < 31671, (D z ↔ D' z)) :
    ArrOK lab par gen D' la pa ga := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun z hz => ⟨fun hd => (h4 z hz).1 ((e z hz).2 hd),
    fun hd => (h4 z hz).2 fun hd' => hd ((e z hz).1 hd')⟩⟩

def QOK (off pts : Nat → Nat) (c m : Nat) (q : Array Nat) : Prop :=
  q.size = m ∧ ∀ j < m, q[j]! = pts (off c + j)

def KOK (off gen par pos pts : Nat → Nat) (c m κ : Nat) : Prop :=
  1 ≤ m ∧ off c + m ≤ off (c + 1) ∧ ∀ P, off c < P → P < off (c + 1) →
    (P < off c + m ↔ 16 * pos (par (pts P)) + gen (pts P) < κ)

def IK (lab gen par pos pts off : Nat → Nat) (c lo κ : Nat)
    (s : Array Nat × Array Nat × Array Nat × Array Nat) : Prop :=
  ∃ m, lo ≤ m ∧ ArrOK lab par gen (fun z => lab z < c ∨ (lab z = c ∧ pos z < off c + m))
    s.1 s.2.1 s.2.2.1 ∧ QOK off pts c m s.2.2.2 ∧ KOK off gen par pos pts c m κ

def kStep (I : Array Table) (c p : Nat) (s : Array Nat × Array Nat × Array Nat × Array Nat)
    (k : Nat) : Array Nat × Array Nat × Array Nat × Array Nat :=
  if (s.1[ap I[k]! p]! == 3) = true then
    (s.1.set! (ap I[k]! p) c, s.2.1.set! (ap I[k]! p) p, s.2.2.1.set! (ap I[k]! p) k,
      s.2.2.2.push (ap I[k]! p))
  else s

public section

theorem orbSearch_eq {I : Array Table} {T : Nat → Nat → Nat}
    (hT : ∀ k ∈ gIdx (), ∀ x < 31671, ap I[k]! x = T k x)
    (hTi : ∀ k ∈ gIdx (), ∀ x < 31671, T k x < 31671 ∧ T k (T k x) = x)
    {rt off lab gen par pos pts : Nat → Nat}
    (h : bfsOK T rt off lab gen par pos pts = true) :
    orbSearch I [rt 0, rt 1, rt 2] =
      (Array.ofFn (n := 31671) fun i => lab i.val, Array.ofFn (n := 31671) fun i => par i.val,
        Array.ofFn (n := 31671) fun i => gen i.val) := by
  unfold bfsOK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hh, ha⟩ := h
  obtain ⟨o0, o1, o12, o23, o3, hroot⟩ := bfsHd_spec hh
  have hF : ∀ y < 31671, BfsFacts T rt off lab gen par pos pts y := fun y hy =>
    bfsAt_spec (allN_iff.1 ha y hy)
  unfold BfsFacts at hF
  have offLe : ∀ a b, a ≤ b → b ≤ 3 → off a ≤ off b := by
    intro a b hab hb
    interval_cases b <;> interval_cases a <;> omega
  have offLt : ∀ a b, a < b → b ≤ 3 → off a < off b := by
    intro a b hab hb
    interval_cases b <;> interval_cases a <;> omega
  have blkU : ∀ c c' P, c < 3 → c' < 3 → off c ≤ P → P < off (c + 1) → off c' ≤ P →
      P < off (c' + 1) → c = c' := by
    intro c c' P hc hc' h1 h2 h3 h4
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := offLe (c + 1) c' (by omega) (by omega)
      omega
    · have := offLe (c' + 1) c (by omega) (by omega)
      omega
  have hposLt : ∀ y < 31671, pos y < 31671 := fun y hy => by
    obtain ⟨-, -, f3, -, f5, -⟩ := hF y hy
    have := offLe (lab y + 1) 3 (by omega) le_rfl
    omega
  have hpts : ∀ i < 31671, pts i < 31671 := by
    intro i hi
    let f : Fin 31671 → Fin 31671 := fun y => ⟨pos y.val, hposLt y.val y.isLt⟩
    have hinj : Function.Injective f := by
      intro a b e
      have e' : pos a.val = pos b.val := congrArg Fin.val e
      apply Fin.ext
      rw [← (hF a.val a.isLt).2.1, ← (hF b.val b.isLt).2.1, e']
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj ⟨i, hi⟩
    have e : pos y.val = i := congrArg Fin.val hy
    rw [← e, (hF y.val y.isLt).2.1]
    exact y.isLt
  have hBlk : ∀ c < 3, ∀ P, off c ≤ P → P < off (c + 1) →
      lab (pts P) = c ∧ pos (pts P) = P ∧ pts P < 31671 := by
    intro c hc P h1 h2
    have hP : P < 31671 := lt_of_lt_of_le h2 (by have := offLe (c + 1) 3 (by omega) le_rfl; omega)
    have hz := hpts P hP
    have e1 : pos (pts P) = P := (hF P hP).1
    obtain ⟨-, -, f3, f4, f5, -⟩ := hF (pts P) hz
    rw [e1] at f4 f5
    exact ⟨(blkU c _ P hc f3 h1 h2 f4 f5).symm, e1, hz⟩
  have hNR : ∀ c < 3, ∀ P, off c < P → P < off (c + 1) →
      gen (pts P) < 10 ∧ gen (pts P) ≠ 8 ∧ par (pts P) < 31671 ∧ off c ≤ pos (par (pts P)) ∧
      pos (par (pts P)) < P ∧ T (gen (pts P)) (par (pts P)) = pts P ∧
      pts (pos (par (pts P))) = par (pts P) ∧
      (off c + 1 < P → 16 * pos (par (pts (P - 1))) + gen (pts (P - 1)) <
        16 * pos (par (pts P)) + gen (pts P)) ∧
      (∀ k, gOK k = true → 16 * pos (par (pts P)) + gen (pts P) ≤ 16 * pos (T k (pts P)) + k) := by
    intro c hc P h1 h2
    obtain ⟨hl, hp, hz⟩ := hBlk c hc P (by omega) h2
    obtain ⟨-, -, -, -, -, -, -, f8⟩ := hF (pts P) hz
    rw [hl, hp] at f8
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := f8 (by omega)
    obtain ⟨-, fp2, -, fp4, -⟩ := hF (par (pts P)) g2
    rw [g3] at fp4
    obtain ⟨k1, k2⟩ := (gOK_iff _).1 g1
    refine ⟨k1, k2, g2, fp4, g5, g4, fp2, fun hlt => ?_, g7⟩
    have := g6 hlt
    rwa [osKeyOf] at this
  have keyId : ∀ c < 3, ∀ P0 k, off c ≤ P0 → P0 < off (c + 1) → k < 10 → ∀ P, off c < P →
      P < off (c + 1) → 16 * pos (par (pts P)) + gen (pts P) = 16 * P0 + k →
      pts P = T k (pts P0) := by
    intro c hc P0 k h0 h0' hk P h1 h2 he
    obtain ⟨g1, -, -, -, -, g6, g7, -⟩ := hNR c hc P h1 h2
    have e1 : pos (par (pts P)) = P0 := by omega
    have e2 : gen (pts P) = k := by omega
    rw [← g6, e2, ← g7, e1]
  have hK : ∀ c, c < 3 → ∀ h lo k κ s, h < lo → gOK k = true → κ = 16 * (off c + h) + k →
      IK lab gen par pos pts off c lo κ s →
      IK lab gen par pos pts off c lo (κ + 1) (kStep I c (pts (off c + h)) s k) := by
    intro c hc h lo k κ s hhlo hk hκ hIK
    obtain ⟨la, pa, ga, q⟩ := s
    obtain ⟨m, hlo, ⟨hs1, hs2, hs3, hA⟩, ⟨hq1, hq2⟩, ⟨hm1, hm2, hKc⟩⟩ := hIK
    dsimp only at hs1 hs2 hs3 hA hq1 hq2
    have hP0 : off c + h < off (c + 1) := by omega
    obtain ⟨hlp, hpp, hpn⟩ := hBlk c hc (off c + h) (by omega) hP0
    have hk' := osMemGIdx hk
    have hk10 : k < 10 := ((gOK_iff k).1 hk).1
    have hy := hT k hk' _ hpn
    obtain ⟨hyn, hyy⟩ := hTi k hk' _ hpn
    have hly : lab (T k (pts (off c + h))) = c := by
      rw [(hF _ hpn).2.2.2.2.2.1 k hk, hlp]
    obtain ⟨-, fy2, -, fy4, fy5, -, -, fy8⟩ := hF _ hyn
    rw [hly] at fy4 fy5 fy8
    unfold kStep
    dsimp only
    rw [hy]
    by_cases hin : pos (T k (pts (off c + h))) < off c + m
    · have hla := ((hA _ hyn).1 (Or.inr ⟨hly, hin⟩)).1
      rw [if_neg (by rw [hla, hly, beq_iff_eq]; omega)]
      refine ⟨m, hlo, ⟨hs1, hs2, hs3, hA⟩, ⟨hq1, hq2⟩, hm1, hm2, fun P h1 h2 => ?_⟩
      rw [hKc P h1 h2]
      constructor
      · intro h3
        omega
      · intro h3
        rcases Nat.lt_or_ge (16 * pos (par (pts P)) + gen (pts P)) κ with h4 | h4
        · exact h4
        · exfalso
          have e := keyId c hc (off c + h) k (by omega) hP0 hk10 P h1 h2 (by omega)
          have hPn : P < 31671 :=
            lt_of_lt_of_le h2 (by have := offLe (c + 1) 3 (by omega) le_rfl; omega)
          have eP : P = pos (T k (pts (off c + h))) := by rw [← e]; exact ((hF P hPn).1).symm
          have := (hKc P h1 h2).1 (by omega)
          omega
    · have hD : ¬ (lab (T k (pts (off c + h))) < c ∨
          (lab (T k (pts (off c + h))) = c ∧ pos (T k (pts (off c + h))) < off c + m)) := by
        rintro (h1 | ⟨-, h1⟩) <;> omega
      have hla := ((hA _ hyn).2 hD).1
      rw [if_pos (by rw [hla]; rfl)]
      obtain ⟨g1, g2, -, -, g5, g6, g7⟩ := fy8 (by omega)
      have hle : 16 * pos (par (T k (pts (off c + h)))) + gen (T k (pts (off c + h))) ≤
          16 * (off c + h) + k := by
        have := g7 k hk
        rwa [hyy, hpp] at this
      have hge : ¬ (16 * pos (par (T k (pts (off c + h)))) + gen (T k (pts (off c + h))) < κ) := by
        intro hlt
        have := (hKc _ (by omega) fy5).2 (by rw [fy2]; exact hlt)
        omega
      have hpy : pos (T k (pts (off c + h))) = off c + m := by
        by_contra hne2
        have h6 := g6 (by omega)
        rw [osKeyOf] at h6
        have := (hKc (pos (T k (pts (off c + h))) - 1) (by omega) (by omega)).2 (by omega)
        omega
      have hg10 : gen (T k (pts (off c + h))) < 10 := ((gOK_iff _).1 g1).1
      have hppar : pos (par (T k (pts (off c + h)))) = off c + h := by omega
      have hgen : gen (T k (pts (off c + h))) = k := by omega
      have hpar : par (T k (pts (off c + h))) = pts (off c + h) := by
        rw [← (hF _ g2).2.1, hppar]
      refine ⟨m + 1, by omega, ⟨?_, ?_, ?_, fun z hz => ?_⟩, ⟨?_, fun j hj => ?_⟩, by omega,
        by omega, fun P h1 h2 => ?_⟩
      · dsimp only
        rw [osSizeSet, hs1]
      · dsimp only
        rw [osSizeSet, hs2]
      · dsimp only
        rw [osSizeSet, hs3]
      · dsimp only
        rw [osGetSet (by rw [hs1]; exact hyn) (by rw [hs1]; exact hz),
          osGetSet (by rw [hs2]; exact hyn) (by rw [hs2]; exact hz),
          osGetSet (by rw [hs3]; exact hyn) (by rw [hs3]; exact hz)]
        by_cases ezy : T k (pts (off c + h)) = z
        · subst ezy
          rw [if_pos rfl, if_pos rfl, if_pos rfl]
          refine ⟨fun _ => ⟨hly.symm, hpar.symm, hgen.symm⟩, fun hd => absurd (Or.inr ⟨hly, ?_⟩) hd⟩
          omega
        · rw [if_neg ezy, if_neg ezy, if_neg ezy]
          have hzz : (lab z < c ∨ (lab z = c ∧ pos z < off c + (m + 1))) ↔
              (lab z < c ∨ (lab z = c ∧ pos z < off c + m)) := by
            constructor
            · rintro (h1 | ⟨h1, h2⟩)
              · exact Or.inl h1
              · rcases Nat.lt_or_ge (pos z) (off c + m) with h3 | h3
                · exact Or.inr ⟨h1, h3⟩
                · exfalso
                  have e3 : pos z = pos (T k (pts (off c + h))) := by omega
                  apply ezy
                  rw [← fy2, ← e3, (hF z hz).2.1]
            · rintro (h1 | ⟨h1, h2⟩)
              · exact Or.inl h1
              · exact Or.inr ⟨h1, by omega⟩
          rw [hzz]
          exact hA z hz
      · dsimp only
        rw [Array.size_push, hq1]
      · dsimp only
        rcases Nat.lt_or_ge j m with hj' | hj'
        · rw [osGetPushLt _ _ (by rw [hq1]; exact hj'), hq2 j hj']
        · have ej : j = q.size := by omega
          rw [ej, osGetPushEq, hq1, ← hpy, fy2]
      · have hPn : P < 31671 :=
          lt_of_lt_of_le h2 (by have := offLe (c + 1) 3 (by omega) le_rfl; omega)
        constructor
        · intro h3
          rcases Nat.lt_or_ge P (off c + m) with h4 | h4
          · have := (hKc P h1 h2).1 h4
            omega
          · have eP : P = pos (T k (pts (off c + h))) := by omega
            rw [eP, fy2]
            omega
        · intro h3
          rcases Nat.lt_or_ge (16 * pos (par (pts P)) + gen (pts P)) κ with h4 | h4
          · have := (hKc P h1 h2).2 h4
            omega
          · have e := keyId c hc (off c + h) k (by omega) hP0 hk10 P h1 h2 (by omega)
            have eP : P = pos (T k (pts (off c + h))) := by rw [← e]; exact ((hF P hPn).1).symm
            omega
  have hSkip : ∀ c lo a b s, IK lab gen par pos pts off c lo a s → a ≤ b →
      (∀ P, off c < P → P < off (c + 1) →
        ¬ (a ≤ 16 * pos (par (pts P)) + gen (pts P) ∧ 16 * pos (par (pts P)) + gen (pts P) < b)) →
      IK lab gen par pos pts off c lo b s := by
    intro c lo a b s hIK hab hgap
    obtain ⟨m, hlo, hA, hQ, hm1, hm2, hKc⟩ := hIK
    refine ⟨m, hlo, hA, hQ, hm1, hm2, fun P h1 h2 => ?_⟩
    rw [hKc P h1 h2]
    constructor
    · intro h3
      omega
    · intro h3
      by_contra h4
      exact hgap P h1 h2 ⟨by omega, h3⟩
  have hFin : ∀ c < 3, ∀ m la pa ga,
      ArrOK lab par gen (fun z => lab z < c ∨ (lab z = c ∧ pos z < off c + m)) la pa ga →
      KOK off gen par pos pts c m (16 * (off c + m)) →
      ArrOK lab par gen (fun z => lab z < c + 1) la pa ga := by
    intro c hc m la pa ga hA hKO
    obtain ⟨hm1, hm2, hKc⟩ := hKO
    have hend : off c + m = off (c + 1) := by
      by_contra hne
      obtain ⟨g1, -, -, -, g5, -⟩ := hNR c hc (off c + m) (by omega) (by omega)
      have := (hKc (off c + m) (by omega) (by omega)).2 (by omega)
      omega
    refine hA.congr fun z hz => ?_
    obtain ⟨-, -, f3, f4, f5, -⟩ := hF z hz
    constructor
    · rintro (h1 | ⟨h1, -⟩) <;> omega
    · intro h1
      rcases Nat.lt_or_ge (lab z) c with h2 | h2
      · exact Or.inl h2
      · have e : lab z = c := by omega
        rw [e] at f5
        exact Or.inr ⟨e, by omega⟩
  obtain ⟨s, hs, -, hJ⟩ : ∃ s : Array Nat × Array Nat × Array Nat × Nat,
      orbSearch I [rt 0, rt 1, rt 2] = (s.1, s.2.1, s.2.2.1) ∧ s.2.2.2 = 0 + 3 ∧
        ArrOK lab par gen (fun z => lab z < 0 + 3) s.1 s.2.1 s.2.2.1 := by
    unfold orbSearch
    dsimp only
    have e : [rt 0, rt 1, rt 2] = (List.range' 0 3).map rt := rfl
    rw [e]
    refine osBindEx (fun (s : Array Nat × Array Nat × Array Nat × Nat) => s.2.2.2 = 0 + 3 ∧
      ArrOK lab par gen (fun z => lab z < 0 + 3) s.1 s.2.1 s.2.2.1) _ _ ?_
    refine osListLoop
      (fun c (b : Array Nat × Array Nat × Array Nat × Nat) =>
        b.2.2.2 = c ∧ ArrOK lab par gen (fun z => lab z < c) b.1 b.2.1 b.2.2.1)
      _ rt 3 0 _ ?_ ?_
    · rintro c ⟨la, pa, ga, c'⟩ - hc3 ⟨hcc, hA⟩
      dsimp only at hcc hA
      subst hcc
      have hc : c' < 3 := by omega
      obtain ⟨hrn, hlr, hpr⟩ := hroot c' hc
      obtain ⟨-, -, -, -, -, -, fr7, -⟩ := hF (rt c') hrn
      rw [hlr] at fr7
      obtain ⟨-, hpar0, hgen0⟩ := fr7 hpr
      have hla : la[rt c']! = 3 := ((hA.2.2.2 (rt c') hrn).2 (by omega)).1
      dsimp only
      rw [if_pos (by rw [hla]; rfl)]
      refine ⟨_, rfl, ?_⟩
      dsimp only
      refine ⟨rfl, ?_⟩
      refine range_loop
        (fun i (b : Array Nat × Array Nat × Array Nat × Array Nat × Nat) => b.2.2.2.2 = i ∧
          IK lab gen par pos pts off c' i (16 * (off c' + i)) (b.1, b.2.1, b.2.2.1, b.2.2.2.1))
        (fun (X : Array Nat × Array Nat × Array Nat × Array Nat × Nat) =>
          ArrOK lab par gen (fun z => lab z < c' + 1) X.1 X.2.1 X.2.2.1) _ 31671 _ ?_ ?_ ?_
      · rintro i ⟨la', pa', ga', q, hq⟩ hi ⟨hqi, hIK⟩
        dsimp only at hqi hIK
        subst hqi
        obtain ⟨m, him, hA', ⟨hq1, hq2⟩, hKO⟩ := hIK
        dsimp only at hA' hq1 hq2
        dsimp only
        by_cases hlt : hq < q.size
        · rw [if_pos hlt]
          have hp : q[hq]! = pts (off c' + hq) := hq2 hq (by omega)
          rw [hp, forIn_yield _ (fun k s => kStep I c' (pts (off c' + hq)) s k) (fun a b => by
            dsimp only [kStep]
            split <;> rfl)]
          refine osLStepYield ?_
          dsimp only
          refine ⟨rfl, ?_⟩
          have i0 :
              IK lab gen par pos pts off c' (hq + 1) (16 * (off c' + hq)) (la', pa', ga', q) :=
            ⟨m, by omega, hA', ⟨hq1, hq2⟩, hKO⟩
          have hh : hq < hq + 1 := Nat.lt_succ_self hq
          have j0 := hK c' hc hq _ 0 _ _ hh rfl (by omega) i0
          have j1 := hK c' hc hq _ 1 _ _ hh rfl (by omega) j0
          have j2 := hK c' hc hq _ 2 _ _ hh rfl (by omega) j1
          have j3 := hK c' hc hq _ 3 _ _ hh rfl (by omega) j2
          have j4 := hK c' hc hq _ 4 _ _ hh rfl (by omega) j3
          have j5 := hK c' hc hq _ 5 _ _ hh rfl (by omega) j4
          have j6 := hK c' hc hq _ 6 _ _ hh rfl (by omega) j5
          have j7 := hK c' hc hq _ 7 _ _ hh rfl (by omega) j6
          have j8 := hSkip c' _ _ (16 * (off c' + hq) + 9) _ j7 (by omega) (fun P h1 h2 h3 => by
            obtain ⟨g1, g2, -⟩ := hNR c' hc P h1 h2
            obtain ⟨h4, h5⟩ := h3
            omega)
          have j9 := hK c' hc hq _ 9 _ _ hh rfl (by omega) j8
          have j10 := hSkip c' _ _ (16 * (off c' + (hq + 1))) _ j9 (by omega)
            (fun P h1 h2 h3 => by
              obtain ⟨g1, g2, -⟩ := hNR c' hc P h1 h2
              obtain ⟨h4, h5⟩ := h3
              omega)
          simp only [Prod.mk.eta, gIdx, List.foldl_cons, List.foldl_nil]
          exact j10
        · rw [if_neg hlt]
          refine osLStepDone ?_
          dsimp only
          have e : hq = m := by omega
          subst e
          exact hFin c' hc hq la' pa' ga' hA' hKO
      · rintro ⟨la', pa', ga', q, hq⟩ ⟨hqi, hIK⟩
        dsimp only at hqi hIK
        obtain ⟨m, him, -, -, hm1, hm2, -⟩ := hIK
        exfalso
        have := offLe (c' + 1) 3 (by omega) le_rfl
        by_cases hc0 : c' = 0
        · have := offLt (c' + 1) 3 (by omega) le_rfl
          omega
        · have := offLt 0 c' (by omega) (by omega)
          omega
      · have hb1 := offLt c' (c' + 1) (by omega) (by omega)
        refine ⟨rfl, 1, by omega, ⟨?_, ?_, ?_, fun z hz => ?_⟩, ⟨rfl, fun j hj => ?_⟩, le_rfl,
          by omega, fun P h1 h2 => ?_⟩
        · dsimp only
          rw [osSizeSet, hA.1]
        · exact hA.2.1
        · exact hA.2.2.1
        · dsimp only
          rw [osGetSet (by rw [hA.1]; exact hrn) (by rw [hA.1]; exact hz)]
          by_cases ezr : rt c' = z
          · subst ezr
            rw [if_pos rfl]
            have hz' := (hA.2.2.2 (rt c') hz).2 (by omega)
            refine ⟨fun _ => ⟨hlr.symm, by rw [hz'.2.1, hpar0], by rw [hz'.2.2, hgen0]⟩,
              fun hd => absurd (Or.inr ⟨hlr, by omega⟩) hd⟩
          · rw [if_neg ezr]
            have hzz : (lab z < c' ∨ (lab z = c' ∧ pos z < off c' + 1)) ↔ lab z < c' := by
              constructor
              · rintro (h1 | ⟨h1, h2⟩)
                · exact h1
                · exfalso
                  obtain ⟨-, fz2, -, fz4, -⟩ := hF z hz
                  rw [h1] at fz4
                  have e : pos z = pos (rt c') := by omega
                  apply ezr
                  rw [← fz2, e, (hF _ hrn).2.1]
              · exact Or.inl
            rw [hzz]
            exact hA.2.2.2 z hz
        · have e : j = 0 := by omega
          subst e
          rw [Nat.add_zero, ← hpr, (hF _ hrn).2.1]
          rfl
        · obtain ⟨-, -, -, g4, -⟩ := hNR c' hc P h1 h2
          constructor <;> intro h3 <;> omega
    · refine ⟨rfl, ?_, ?_, ?_, fun z hz => ⟨fun hd => absurd hd (Nat.not_lt_zero _), fun _ => ?_⟩⟩
      · exact Array.size_replicate
      · exact Array.size_replicate
      · exact Array.size_replicate
      · exact ⟨osGetReplicate hz, osGetReplicate hz, osGetReplicate hz⟩
  rw [hs]
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  have hD : ∀ z < 31671, lab z < 0 + 3 := fun z hz => by
    have := (hF z hz).2.2.1
    omega
  rw [osOfFn _ _ h1 fun k hk => ((h4 k hk).1 (hD k hk)).1,
    osOfFn _ _ h2 fun k hk => ((h4 k hk).1 (hD k hk)).2.1,
    osOfFn _ _ h3 fun k hk => ((h4 k hk).1 (hD k hk)).2.2]

end

end CFSG.KC.Fi23P

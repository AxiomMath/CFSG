module

public import CFSG.Certificates.Kernel.GilmanCensus.MemoSound
public import CFSG.Certificates.Kernel.GilmanCensus.DiagramSound
import all Certificates.Data.Census

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def LoopRes {α σ : Type} (P : α → Bool) (Q : α → σ → σ → Prop) (l : List α) (s : σ)
    (r : (Option Bool × Unit) × σ) : Prop :=
  match l.find? P with
  | none => r = ((none, ()), s)
  | some a => r.1 = (some true, ()) ∧ Q a s r.2

theorem sloop {α σ : Type} (I : σ → Prop) (P : α → Bool) (Q : α → σ → σ → Prop)
    (f : α → Option Bool × Unit → StateT σ Id (ForInStep (Option Bool × Unit)))
    (hf : ∀ a st s, I s → if P a then ((f a st).run s).1 = ForInStep.done (some true, ()) ∧
        Q a s ((f a st).run s).2 else (f a st).run s = (ForInStep.yield (none, ()), s)) :
    ∀ (l : List α) (s : σ), I s → LoopRes P Q l s ((forIn l (none, ()) f).run s)
  | [], s, _ => rfl
  | a :: l, s, hs => by
    unfold LoopRes
    rw [List.forIn_cons, StateT.run_bind, List.find?_cons]
    have h := hf a (none, ()) s hs
    by_cases hp : P a = true
    · simp only [hp, ↓reduceIte] at h ⊢
      rw [idBind]
      generalize (f a (none, ())).run s = r at h ⊢
      obtain ⟨v, s'⟩ := r
      obtain ⟨h1, h2⟩ := h
      simp only at h1 h2
      subst h1
      exact ⟨rfl, h2⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [h, idBind]
      exact sloop I P Q f hf l s hs

@[expose] def mBad (dt : Data) (L K : Nat) (V : Array (Nat × Int)) : Bool :=
  !((kerPure dt L).size == 1 && (kerPure dt K).size == 1) ||
    (closureOf dt ((V.extract 0 (V.size - 1)).map (·.1)) != L ||
      closureOf dt (((V.extract 0 (V.size - 2)).push V[V.size - 1]!).map (·.1)) != K)

@[expose] def MStep (dt : Data) (L K : Nat) (V : Array (Nat × Int)) (s s' : Cache) : Prop :=
  (CacheOK dt s → CacheOK dt s') ∧ (CacheOK dt s → s'.bad = (s.bad || mBad dt L K V))

@[expose] def mV (dt : Data) (L K : Nat) (b a : Nat × Int) : Array (Nat × Int) :=
  ((Array.map (fun i => (i, (1 : Int))) (simpOf dt (L &&& K))).push b).push a

@[expose] def mAct (dt : Data) (L K : Nat) (V : Array (Nat × Int)) :
    CM (ForInStep (Option Bool × Unit)) := do
  let kL ← kernelM dt L
  let kK ← kernelM dt K
  if !(kL.size == 1 && kK.size == 1) then markBad
  let idsL := (V.extract 0 (V.size - 1)).map (fun x : Nat × Int => x.1)
  let idsK := ((V.extract 0 (V.size - 2)).push V[V.size - 1]!).map (fun x : Nat × Int => x.1)
  if closureOf dt idsL != L || closureOf dt idsK != K then markBad
  return ForInStep.done (some true, ())

@[expose] def mInner (dt : Data) (L K : Nat) (b a : Nat × Int) (_ : Option Bool × Unit) :
    CM (ForInStep (Option Bool × Unit)) :=
  match diagram dt (mV dt L K b a) with
  | none => pure (ForInStep.yield (none, ()))
  | some _ => mAct dt L K (mV dt L K b a)

@[expose] def mOuter (dt : Data) (L K : Nat) (b : Nat × Int) (_ : Option Bool × Unit) :
    CM (ForInStep (Option Bool × Unit)) := do
  let r ← forIn (extensions dt (L &&& K) K) ((none : Option Bool), ()) (mInner dt L K b)
  match r.1 with
  | some x => pure (ForInStep.done (some x, ()))
  | none => pure (ForInStep.yield (none, ()))

@[expose] def mProg (dt : Data) (L K : Nat) : CM Bool := do
  let r ← forIn (extensions dt (L &&& K) L) ((none : Option Bool), ()) (mOuter dt L K)
  match r.1 with
  | some x => pure x
  | none => pure false

theorem modelM_prog (dt : Data) (L K : Nat) : modelM dt L K = mProg dt L K := by
  unfold modelM mProg mOuter mInner mAct mV
  dsimp only
  have e1 : (fun (p : Option Bool × Unit) => match p.1 with
      | some r => (pure r : CM Bool)
      | none => pure false) = (fun p => match p.1 with
      | some x => pure x
      | none => pure false) := by
    funext p
    obtain ⟨o, u⟩ := p
    cases o <;> rfl
  have e2 : (fun (p : Option Bool × Unit) => match p.1 with
      | some r => (pure (ForInStep.done (some r, ())) : CM (ForInStep (Option Bool × Unit)))
      | none => pure (ForInStep.yield (none, ()))) = (fun p => match p.1 with
      | some x => pure (ForInStep.done (some x, ()))
      | none => pure (ForInStep.yield (none, ()))) := by
    funext p
    obtain ⟨o, u⟩ := p
    cases o <;> rfl
  congr 1
  all_goals try exact e1
  congr 1
  funext b st
  congr 1
  all_goals first
    | (funext p; obtain ⟨o, u⟩ := p; cases o <;> rfl)
    | skip

theorem mact {dt : Data} (L K : Nat) (V : Array (Nat × Int)) (s : Cache) (hs : CacheOK dt s) :
    ((mAct dt L K V).run s).1 = ForInStep.done (some true, ()) ∧
      MStep dt L K V s ((mAct dt L K V).run s).2 := by
  unfold mAct
  obtain ⟨k1, k2, k3⟩ := kernelM_ok hs L
  generalize hr1 : (kernelM dt L).run s = r1 at k1 k2 k3
  obtain ⟨kl, s1⟩ := r1
  obtain ⟨j1, j2, j3⟩ := kernelM_ok k2 K
  generalize hr2 : (kernelM dt K).run s1 = r2 at j1 j2 j3
  obtain ⟨kk, s2⟩ := r2
  simp only at k1 k2 k3 j1 j2 j3
  subst k1 j1
  simp only [StateT.run_bind, hr1]
  rw [idBind]
  dsimp only
  rw [hr2, idBind]
  dsimp only
  have hb : s2.bad = s.bad := j3.trans k3
  split
  · rename_i hk
    rw [StateT.run_bind]
    split
    · rename_i hcl
      refine ⟨rfl, fun _ => j2, fun _ => ?_⟩
      simp only [mBad, hk, hcl, Bool.true_or, Bool.or_true]
      rfl
    · rename_i hcl
      refine ⟨rfl, fun _ => j2, fun _ => ?_⟩
      simp only [mBad, hk, Bool.true_or, Bool.or_true]
      rfl
  · rename_i hk
    split
    · rename_i hcl
      refine ⟨rfl, fun _ => j2, fun _ => ?_⟩
      simp only [mBad, hcl, Bool.or_true]
      rfl
    · rename_i hcl
      refine ⟨rfl, fun _ => j2, fun _ => ?_⟩
      simp only [Bool.not_eq_true] at hk hcl
      simp only [mBad, hk, hcl, Bool.or_false]
      exact hb

@[expose] def mHit (dt : Data) (L K : Nat) (b : Nat × Int) : Bool :=
  ((extensions dt (L &&& K) K).toList.find? fun a => (diagram dt (mV dt L K b a)).isSome).isSome

@[expose] def mFound (dt : Data) (L K : Nat) : Option (Array (Nat × Int)) :=
  (extensions dt (L &&& K) L).toList.findSome? fun b =>
    ((extensions dt (L &&& K) K).toList.find? fun a => (diagram dt (mV dt L K b a)).isSome).map
      (mV dt L K b)

theorem findSome_none {α β γ : Type} (g : α → Option β) (h : α → β → γ) :
    ∀ l : List α, l.find? (fun b => (g b).isSome) = none →
      l.findSome? (fun b => (g b).map (h b)) = none
  | [], _ => rfl
  | b :: l, hl => by
    rw [List.find?_cons] at hl
    rw [List.findSome?_cons]
    split at hl
    · simp at hl
    · rename_i hb
      have : g b = none := by simpa using hb
      rw [this]
      exact findSome_none g h l hl

theorem findSome_some {α β γ : Type} (g : α → Option β) (h : α → β → γ) :
    ∀ (l : List α) (b : α), l.find? (fun b => (g b).isSome) = some b →
      ∃ a, g b = some a ∧ l.findSome? (fun b => (g b).map (h b)) = some (h b a)
  | [], _, hl => by simp at hl
  | x :: l, b, hl => by
    rw [List.find?_cons] at hl
    rw [List.findSome?_cons]
    split at hl
    · rename_i hx
      cases hl
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hx
      exact ⟨a, ha, by rw [ha]; rfl⟩
    · rename_i hx
      have : g x = none := by simpa using hx
      rw [this]
      exact findSome_some g h l b hl

theorem modelM_ok {dt : Data} {c : Cache} (hc : CacheOK dt c) (L K : Nat) :
    ((modelM dt L K).run c).1 = (mFound dt L K).isSome ∧ CacheOK dt ((modelM dt L K).run c).2 ∧
      ((modelM dt L K).run c).2.bad =
        (c.bad || match mFound dt L K with | none => false | some V => mBad dt L K V) := by
  rw [modelM_prog]
  have hin : ∀ b s, CacheOK dt s → LoopRes (fun a => (diagram dt (mV dt L K b a)).isSome)
      (fun a => MStep dt L K (mV dt L K b a)) (extensions dt (L &&& K) K).toList s
      ((forIn (extensions dt (L &&& K) K).toList (none, ()) (mInner dt L K b)).run s) := by
    intro b s hs
    refine sloop (CacheOK dt) _ _ _ ?_ _ s hs
    intro a st s2 hs2
    unfold mInner
    split
    · rename_i hd
      split
      · rename_i hd'
        rw [hd'] at hd
        simp at hd
      · exact mact L K _ s2 hs2
    · rename_i hd
      split
      · rfl
      · rename_i hd'
        rw [hd'] at hd
        simp at hd
  have hout := sloop (CacheOK dt) (mHit dt L K)
    (fun b s s' => ∃ a, ((extensions dt (L &&& K) K).toList.find? fun a =>
      (diagram dt (mV dt L K b a)).isSome) = some a ∧ MStep dt L K (mV dt L K b a) s s')
    (mOuter dt L K) (by
      intro b st s hs
      have h := hin b s hs
      unfold mOuter
      rw [StateT.run_bind, ← Array.forIn_toList]
      unfold LoopRes at h
      unfold mHit
      generalize (forIn (extensions dt (L &&& K) K).toList (none, ()) (mInner dt L K b)).run s = r at h ⊢
      split at h
      · rename_i hf
        rw [hf, h]
        rfl
      · rename_i a hf
        rw [hf]
        obtain ⟨⟨o, u⟩, s'⟩ := r
        obtain ⟨h1, h2⟩ := h
        simp only at h1 h2
        cases h1
        exact ⟨rfl, a, rfl, h2⟩)
    (extensions dt (L &&& K) L).toList c hc
  unfold mProg
  rw [StateT.run_bind, ← Array.forIn_toList]
  unfold LoopRes at hout
  generalize (forIn (extensions dt (L &&& K) L).toList (none, ()) (mOuter dt L K)).run c = r at hout ⊢
  have hg := findSome_none (fun b => (extensions dt (L &&& K) K).toList.find? fun a =>
    (diagram dt (mV dt L K b a)).isSome) (mV dt L K) (extensions dt (L &&& K) L).toList
  have hg2 := findSome_some (fun b => (extensions dt (L &&& K) K).toList.find? fun a =>
    (diagram dt (mV dt L K b a)).isSome) (mV dt L K) (extensions dt (L &&& K) L).toList
  unfold mHit at hout
  split at hout
  · rename_i hf
    have e := hg hf
    unfold mFound
    rw [e, hout]
    refine ⟨rfl, hc, ?_⟩
    rw [Bool.or_false]
    rfl
  · rename_i b hf
    obtain ⟨a, ha, e⟩ := hg2 b hf
    obtain ⟨⟨o, u⟩, s'⟩ := r
    obtain ⟨h1, a', ha', h2⟩ := hout
    simp only at h1 h2 ha'
    cases h1
    rw [ha] at ha'
    cases ha'
    unfold mFound
    rw [e]
    exact ⟨rfl, h2.1 hc, h2.2 hc⟩

theorem sub_xor_lt (X common N : Nat) (hX : X < 2 ^ N) : X ^^^ (X &&& common) < 2 ^ N := by
  apply Nat.lt_of_le_of_lt _ hX
  apply Nat.le_of_testBit
  intro t ht
  simp only [Nat.testBit_xor, Nat.testBit_and] at ht
  cases hx : X.testBit t <;> simp_all

theorem extK_lt (dk : DK) (common X : Nat) (hX : X < 2 ^ dk.N) :
    ∀ p ∈ extensionsK dk common X, p.1 < dk.N := by
  intro p hp
  unfold extensionsK at hp
  dsimp only at hp
  split at hp
  · simp at hp
  · simp only [List.mem_flatMap, List.mem_map] at hp
    obtain ⟨i, hi, sg, _, rfl⟩ := hp
    exact bitsK_lt _ dk.N i (sub_xor_lt X common dk.N hX) hi

theorem simpK_lt (dk : DK) (common : Nat) (hc : common < 2 ^ dk.N) :
    ∀ j ∈ simpOfK dk common, j < dk.N := fun j hj =>
  bitsK_lt common dk.N j hc (List.mem_filter.mp hj).1

theorem simpK_len (dk : DK) (common : Nat) (hc : common < 2 ^ dk.N) :
    (simpOfK dk common).length ≤ dk.N :=
  Nat.le_trans (List.length_filter_le _ _) (bitsA_length 128 0 common dk.N hc)

theorem and_lt (L K N : Nat) (hL : L < 2 ^ N) : L &&& K < 2 ^ N := by
  rw [Nat.and_comm]
  exact Nat.and_lt_two_pow K hL

theorem find_congr' {α : Type} (p q : α → Bool) : ∀ (l : List α), (∀ x ∈ l, p x = q x) →
    l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      find_congr' p q l (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem mV_eq {dt : Data} {dk : DK} (h : Rel dt dk) (L K : Nat) (hL : L < 2 ^ dk.N) (b a : Nat × Int) :
    mV dt L K b a = (((simpOfK dk (L &&& K)).map fun i => (i, (1 : Int))) ++ [b] ++ [a]).toArray := by
  unfold mV
  rw [simpOf_eq h _ (and_lt L K dk.N hL)]
  simp

theorem diag_isSome {dt : Data} {dk : DK} (h : Rel dt dk) (V : List (Nat × Int))
    (hV : ∀ p ∈ V, p.1 < dk.N) (hl : V.length ≤ 127) :
    (diagram dt V.toArray).isSome = (diagramK dk V).isSome := by
  rw [← diagram_eq h V hV hl, Option.isSome_map]

theorem mFound_eq {dt : Data} {dk : DK} (h : Rel dt dk) (hN : dk.N ≤ 125) (L K : Nat)
    (hL : L < 2 ^ dk.N) (hK : K < 2 ^ dk.N) :
    (mFound dt L K).map Array.toList =
      ((extensionsK dk (L &&& K) L).flatMap fun b => (extensionsK dk (L &&& K) K).map fun a =>
        ((simpOfK dk (L &&& K)).map fun i => (i, (1 : Int))) ++ [b] ++ [a]).find? fun V =>
          (diagramK dk V).isSome := by
  have hc := and_lt L K dk.N hL
  unfold mFound
  rw [extensions_eq h _ _ hc hL, extensions_eq h _ _ hc hK, List.find?_flatMap]
  generalize hS : (simpOfK dk (L &&& K)).map (fun i => (i, (1 : Int))) = S
  have hSl : S.length ≤ dk.N := by rw [← hS, List.length_map]; exact simpK_len dk _ hc
  have hSb : ∀ p ∈ S, p.1 < dk.N := by
    intro p hp
    rw [← hS] at hp
    simp only [List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact simpK_lt dk _ hc i hi
  have hLb := extK_lt dk (L &&& K) L hL
  have hKb := extK_lt dk (L &&& K) K hK
  generalize extensionsK dk (L &&& K) L = eL at hLb ⊢
  generalize extensionsK dk (L &&& K) K = eK at hKb ⊢
  induction eL with
  | nil => rfl
  | cons b eL ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    have hb := hLb b List.mem_cons_self
    have e : (eK.find? fun a => (diagram dt (mV dt L K b a)).isSome) =
        eK.find? fun a => (diagramK dk (S ++ [b] ++ [a])).isSome := by
      apply find_congr'
      intro a ha
      rw [mV_eq h L K hL, hS, diag_isSome h _ (by
        intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | hp) | hp
        · exact hSb p hp
        · rw [hp]
          exact hb
        · rw [hp]
          exact hKb a ha) (by simp; omega)]
    rw [e, List.find?_map]
    cases hf : eK.find? fun a => (diagramK dk (S ++ [b] ++ [a])).isSome with
    | none =>
      have : (eK.find? ((fun V => (diagramK dk V).isSome) ∘ fun a => S ++ [b] ++ [a])) = none := hf
      rw [this]
      simp only [Option.map_none]
      exact ih (fun p hp => hLb p (List.mem_cons_of_mem b hp))
    | some a =>
      have : (eK.find? ((fun V => (diagramK dk V).isSome) ∘ fun a => S ++ [b] ++ [a])) = some a := hf
      rw [this]
      simp only [Option.map_some]
      rw [mV_eq h L K hL, hS]

theorem toArray_getBang (l : List (Nat × Int)) (i : Nat) : l.toArray[i]! = l.getD i (0, 0) := by
  by_cases hi : i < l.length
  · rw [getElem!_pos l.toArray i (by simpa using hi), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    simp
  · rw [getElem!_neg l.toArray i (by simpa using hi), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega)]
    rfl

theorem extract_map (l : List (Nat × Int)) (k : Nat) :
    (l.toArray.extract 0 k).map (fun x : Nat × Int => x.1) = ((l.take k).map (·.1)).toArray := by
  apply Array.toList_inj.mp
  simp

theorem mBad_eq {dt : Data} {dk : DK} (h : Rel dt dk) (L K : Nat) (hL : L < 2 ^ dk.N)
    (hK : K < 2 ^ dk.N) (V : List (Nat × Int)) (hV : ∀ p ∈ V, p.1 < dk.N) (hl : V.length ≤ 128)
    (hne : 0 < V.length) :
    mBad dt L K V.toArray = (!((kernelK dk L).length == 1 && (kernelK dk K).length == 1) ||
      (closureK dk ((V.take (V.length - 1)).map (·.1)) != L ||
        closureK dk ((V.take (V.length - 2) ++ [V.getD (V.length - 1) (0, 0)]).map (·.1)) != K)) := by
  have k1 : (kerPure dt L).size = (kernelK dk L).length := by rw [← kerPure_eq h L hL, length_LL]
  have k2 : (kerPure dt K).size = (kernelK dk K).length := by rw [← kerPure_eq h K hK, length_LL]
  unfold mBad
  simp only [List.size_toArray, k1, k2]
  rw [extract_map, toArray_getBang, closureOf_eq h _ (by
      intro i hi
      simp only [List.mem_map] at hi
      obtain ⟨p, hp, rfl⟩ := hi
      exact hV p (List.mem_of_mem_take hp)) (by simp; omega)]
  have e : (((V.toArray.extract 0 (V.length - 2)).push (V.getD (V.length - 1) (0, 0))).map
      (fun x : Nat × Int => x.1)) =
      ((V.take (V.length - 2) ++ [V.getD (V.length - 1) (0, 0)]).map (·.1)).toArray := by
    apply Array.toList_inj.mp
    simp
  rw [e, closureOf_eq h _ (by
      intro i hi
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hi
      obtain ⟨p, hp | hp, rfl⟩ := hi
      · exact hV p (List.mem_of_mem_take hp)
      · rw [hp]
        have hv : V.length - 1 < V.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]
        exact hV _ (List.getElem_mem hv)) (by simp; omega)]

theorem modelM_eq {dt : Data} {dk : DK} {c : Cache} (h : Rel dt dk) (hN : dk.N ≤ 125)
    (hc : CacheOK dt c) (L K : Nat) (hL : L < 2 ^ dk.N) (hK : K < 2 ^ dk.N) :
    ((modelM dt L K).run c).1 = (modelK dk L K).1 ∧ CacheOK dt ((modelM dt L K).run c).2 ∧
      ((modelM dt L K).run c).2.bad = (c.bad || (modelK dk L K).2) := by
  obtain ⟨h1, h2, h3⟩ := modelM_ok hc L K
  have hf := mFound_eq h hN L K hL hK
  refine ⟨?_, h2, ?_⟩
  · rw [h1]
    unfold modelK
    dsimp only
    rw [← hf]
    cases mFound dt L K <;> rfl
  · rw [h3]
    unfold modelK
    dsimp only
    rw [← hf]
    cases e : mFound dt L K with
    | none => rfl
    | some V =>
      simp only [Option.map_some]
      have hc' := and_lt L K dk.N hL
      have hmem : V.toList ∈ (extensionsK dk (L &&& K) L).flatMap fun b =>
          (extensionsK dk (L &&& K) K).map fun a =>
            ((simpOfK dk (L &&& K)).map fun i => (i, (1 : Int))) ++ [b] ++ [a] := by
        apply List.mem_of_find?_eq_some (p := fun V => (diagramK dk V).isSome)
        rw [← hf, e]
        rfl
      simp only [List.mem_flatMap, List.mem_map] at hmem
      obtain ⟨b, hb, a, ha, hV⟩ := hmem
      have hVb : ∀ p ∈ V.toList, p.1 < dk.N := by
        rw [← hV]
        intro p hp
        simp only [List.mem_append, List.mem_singleton, List.mem_map] at hp
        rcases hp with (⟨i, hi, rfl⟩ | hp) | hp
        · exact simpK_lt dk _ hc' i hi
        · rw [hp]
          exact extK_lt dk _ L hL b hb
        · rw [hp]
          exact extK_lt dk _ K hK a ha
      have hlen : V.toList.length ≤ 128 ∧ 0 < V.toList.length := by
        rw [← hV]
        have := simpK_len dk _ hc'
        simp only [List.length_append, List.length_map, List.length_singleton]
        omega
      rw [← Array.toArray_toList (xs := V), mBad_eq h L K hL hK V.toList hVb hlen.1 hlen.2]

end Certificates.GilmanCensusK

end

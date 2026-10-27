module

public import Certificates.Data.Kernel.BfsReach
public import Certificates.Data.CatFactsL4U4P1U43Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CentTriv
public import CFSG.Certificates.Kernel.MonsterB.Co2PermSound
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv

public section

namespace CFSG.KC.BfsPairs

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.U43

theorem forIn_rel {α β γ : Type} (R : β → γ → Prop) (f : α → β → Id (ForInStep β))
    (g : α → γ → Id (ForInStep γ)) :
    ∀ l : List α, (∀ a ∈ l, ∀ b c, R b c → ∃ b' c', f a b = pure (ForInStep.yield b') ∧
      g a c = pure (ForInStep.yield c') ∧ R b' c') →
    ∀ b c, R b c → R (Id.run (forIn l b f)) (Id.run (forIn l c g))
  | [], _, _, _, h => h
  | a :: l, hs, b, c, h => by
    obtain ⟨b', c', hb, hc, h'⟩ := hs a List.mem_cons_self b c h
    rw [List.forIn_cons, List.forIn_cons, hb, hc]
    exact forIn_rel R f g l (fun a ha => hs a (List.mem_cons_of_mem _ ha)) b' c' h'

abbrev PSt := Array (Option (Table × Table)) × Array Nat

abbrev RSt := Array Bool × Array Nat

@[expose] def pInner (n : Nat) (gens : Array Table) (p : Nat) (h₁ h₂ : Table) (l : Nat)
    (s : PSt) : Id (ForInStep PSt) :=
  if s.1[ap gens[l]! p]!.isNone = true then
    pure (ForInStep.yield ⟨s.1.set! (ap gens[l]! p)
      (some (conjT n gens[l]! (Array.map (invT n) gens)[l]! h₁,
        conjT n gens[l]! (Array.map (invT n) gens)[l]! h₂)), s.2.push (ap gens[l]! p)⟩)
  else pure (ForInStep.yield ⟨s.1, s.2⟩)

@[expose] def pOuter (n : Nat) (gens : Array Table) (h : Nat) (s : PSt) : Id (ForInStep PSt) :=
  if h < s.2.size then
    match s.1[s.2[h]!]! with
    | some (h₁, h₂) => pure (ForInStep.yield
        (Id.run (forIn (List.range' 0 gens.size) ⟨s.1, s.2⟩ (pInner n gens s.2[h]! h₁ h₂))))
    | none => pure (ForInStep.yield ⟨s.1, s.2⟩)
  else pure (ForInStep.yield ⟨s.1, s.2⟩)

@[expose] def rInner (step : Nat → Nat → Nat) (p : Nat) (l : Nat) (s : RSt) :
    Id (ForInStep RSt) :=
  if (!s.1[step l p]!) = true then
    pure (ForInStep.yield ⟨s.1.set! (step l p) true, s.2.push (step l p)⟩)
  else pure (ForInStep.yield ⟨s.1, s.2⟩)

@[expose] def rOuter (k : Nat) (step : Nat → Nat → Nat) (h : Nat) (s : RSt) :
    Id (ForInStep RSt) :=
  if h < s.2.size then
    if s.1[s.2[h]!]! = true then
      pure (ForInStep.yield (Id.run (forIn (List.range' 0 k) ⟨s.1, s.2⟩ (rInner step s.2[h]!))))
    else pure (ForInStep.yield ⟨s.1, s.2⟩)
  else pure (ForInStep.yield ⟨s.1, s.2⟩)

theorem bfsPairs_eq (n : Nat) (gens : Array Table) (bases : List (Nat × Table × Table)) :
    bfsPairs n gens bases = (Id.run (forIn (List.range' 0 n)
      (bases.foldl (fun b a => (⟨b.1.set! a.1 (some a.2), b.2.push a.1⟩ : PSt))
        ⟨Array.replicate n none, #[]⟩) (pOuter n gens))).1.map (·.getD default) := by
  unfold bfsPairs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl]
  rfl

theorem bfsReach_eq (n k : Nat) (step : Nat → Nat → Nat) (bases : List Nat) :
    bfsReach n k step bases = (Id.run (forIn (List.range' 0 n)
      (bases.foldl (fun b a => (⟨b.1.set! a true, b.2.push a⟩ : RSt))
        ⟨Array.replicate n false, #[]⟩) (rOuter k step))).1 := by
  unfold bfsReach
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl]
  rfl

variable {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {gens : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool}

@[expose] def Good (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) (i : ℕ) (x : Table × Table) :
    Prop :=
  i < n ∧ ∃ a ∈ P, ∃ b ∈ P, Rep n x.1 a ∧ Rep n x.2 b ∧ idx n a i = i ∧ idx n b i = i ∧
    ∀ j < n, idx n a j = j → idx n b j = j → j = i

theorem permOK_of_rep {T : Table} {a : Equiv.Perm (Fin n)} (hT : Rep n T a) :
    permOK n T = true := by
  unfold permOK
  apply CFSG.KC.Co2Mem.isInvA_invCand
  · intro i hi
    rw [natArr_getElem!, hT i hi]
    exact idx_lt a hi
  · intro i j hi hj e
    rw [natArr_getElem!, natArr_getElem!, hT i hi, hT j hj, idx_of_lt _ hi, idx_of_lt _ hj] at e
    have := a.injective (Fin.ext e)
    exact congrArg Fin.val this

theorem getElem!_map_invT {l : ℕ} (hl : l < gens.size) :
    (Array.map (invT n) gens)[l]! = invT n gens[l]! := by
  rw [getElem!_pos _ l (by simpa using hl), getElem!_pos _ l hl, Array.getElem_map]

theorem good_conj (hD : GroupData n P gens gg sift) {p : ℕ} {h₁ h₂ : Table}
    (hg : Good n P p (h₁, h₂)) {l : ℕ} (hl : l < gens.size) :
    Good n P (ap gens[l]! p) (conjT n gens[l]! (Array.map (invT n) gens)[l]! h₁,
      conjT n gens[l]! (Array.map (invT n) gens)[l]! h₂) := by
  obtain ⟨hp, a, ha, b, hb, ra, rb, fa, fb, only⟩ := hg
  have rg := hD.rep l hl
  have rgi : Rep n (Array.map (invT n) gens)[l]! (gg l)⁻¹ := by
    rw [getElem!_map_invT hl]
    exact CFSG.Sporadic.Th.rep_invT_of_rep hD.lt rg
  have hq : ap gens[l]! p = idx n (gg l) p := rg p hp
  have hgP := hD.mem hl
  refine ⟨hq ▸ idx_lt _ hp, gg l * a * (gg l)⁻¹, P.mul_mem (P.mul_mem hgP ha) (P.inv_mem hgP),
    gg l * b * (gg l)⁻¹, P.mul_mem (P.mul_mem hgP hb) (P.inv_mem hgP), rep_conjT rg rgi ra,
    rep_conjT rg rgi rb, ?_, ?_, ?_⟩
  · rw [hq, idx_mul, idx_mul, idx_inv_idx, fa]
  · rw [hq, idx_mul, idx_mul, idx_inv_idx, fb]
  · intro j hj ea eb
    rw [idx_mul, idx_mul] at ea eb
    have ea' := congrArg (idx n (gg l)⁻¹) ea
    have eb' := congrArg (idx n (gg l)⁻¹) eb
    rw [idx_inv_idx] at ea' eb'
    have e := only _ (idx_lt _ hj) ea' eb'
    rw [hq, ← e, idx_idx_inv]

theorem cell_of_good (hD : GroupData n P gens gg sift) {i : ℕ} {x : Table × Table}
    (hg : Good n P i x) :
    (permOK n x.1 && permOK n x.2 && sift x.1 && sift x.2 && ap x.1 i == i && ap x.2 i == i &&
      (List.range n).all fun j => j == i || ap x.1 j != j || ap x.2 j != j) = true := by
  obtain ⟨hi, a, ha, b, hb, ra, rb, fa, fb, only⟩ := hg
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨⟨⟨permOK_of_rep ra, permOK_of_rep rb⟩, (hD.sift _ _ ra).2 ha⟩,
    (hD.sift _ _ rb).2 hb⟩, by rw [ra i hi, fa]⟩, by rw [rb i hi, fb]⟩, ?_⟩
  intro j hj
  by_cases e1 : ap x.1 j = j
  · by_cases e2 : ap x.2 j = j
    · exact Or.inl (Or.inl (only j hj ((ra j hj).symm.trans e1) ((rb j hj).symm.trans e2)))
    · exact Or.inr e2
  · exact Or.inl (Or.inr e1)

@[expose] def Rel (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) (s : PSt) (t : RSt) : Prop :=
  s.2 = t.2 ∧ s.1.size = n ∧ t.1.size = n ∧
    (∀ i : ℕ, t.1[i]! = (s.1[i]! : Option (Table × Table)).isSome) ∧
    ∀ (i : ℕ) x, s.1[i]! = some x → Good n P i x

theorem getElem!_set! {α : Type} [Inhabited α] (a : Array α) (q i : ℕ) (v : α) :
    (a.set! q v)[i]! = if q = i ∧ q < a.size then v else a[i]! := by
  by_cases hqi : q = i
  · subst hqi
    by_cases hq : q < a.size
    · simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, hq]
    · simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, hq]
  · simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, hqi]

theorem rel_set {s : PSt} {t : RSt} (hR : Rel n P s t) {q : ℕ} {x : Table × Table}
    (hx : Good n P q x) :
    Rel n P ⟨s.1.set! q (some x), s.2.push q⟩ ⟨t.1.set! q true, t.2.push q⟩ := by
  obtain ⟨hq, hs, ht, hst, hg⟩ := hR
  refine ⟨by rw [hq], by rw [Array.size_set!, hs], by rw [Array.size_set!, ht], ?_, ?_⟩
  · intro i
    rw [getElem!_set!, getElem!_set!, hs, ht, hst]
    split_ifs <;> rfl
  · intro i y hy
    rw [getElem!_set!] at hy
    split_ifs at hy with h
    · obtain ⟨rfl, -⟩ := h
      cases hy
      exact hx
    · exact hg i y hy

theorem inner_rel (hD : GroupData n P gens gg sift)
    {step : ℕ → ℕ → ℕ} (hstep : ∀ l < gens.size, ∀ p < n, step l p = ap gens[l]! p) {p : ℕ}
    {h₁ h₂ : Table} (hg : Good n P p (h₁, h₂)) :
    ∀ l ∈ List.range' 0 gens.size, ∀ s t, Rel n P s t → ∃ s' t',
      pInner n gens p h₁ h₂ l s = pure (ForInStep.yield s') ∧
      rInner step p l t = pure (ForInStep.yield t') ∧ Rel n P s' t' := by
  intro l hl s t hR
  have hl' : l < gens.size := by
    rw [List.mem_range'_1] at hl
    omega
  have hst : step l p = ap gens[l]! p := hstep l hl' p hg.1
  have hc := hR.2.2.2.1 (ap gens[l]! p)
  unfold pInner rInner
  rw [hst]
  by_cases hn : (s.1[ap gens[l]! p]!).isNone = true
  · have hf : (!t.1[ap gens[l]! p]!) = true := by
      rw [hc]
      cases e : s.1[ap gens[l]! p]! <;> simp_all
    rw [if_pos hn, if_pos hf]
    exact ⟨_, _, rfl, rfl, rel_set hR (good_conj hD hg hl')⟩
  · have hf : ¬(!t.1[ap gens[l]! p]!) = true := by
      rw [hc]
      cases e : s.1[ap gens[l]! p]! <;> simp_all
    rw [if_neg hn, if_neg hf]
    exact ⟨_, _, rfl, rfl, hR⟩

theorem outer_rel (hD : GroupData n P gens gg sift)
    {step : ℕ → ℕ → ℕ} (hstep : ∀ l < gens.size, ∀ p < n, step l p = ap gens[l]! p) :
    ∀ h ∈ List.range' 0 n, ∀ s t, Rel n P s t → ∃ s' t',
      pOuter n gens h s = pure (ForInStep.yield s') ∧
      rOuter gens.size step h t = pure (ForInStep.yield t') ∧ Rel n P s' t' := by
  intro h _ s t hR
  rcases s with ⟨s1, q⟩
  rcases t with ⟨t1, q'⟩
  obtain rfl : q = q' := hR.1
  unfold pOuter rOuter
  dsimp only
  by_cases hh : h < q.size
  · rw [if_pos hh, if_pos hh]
    have hc : t1[q[h]!]! = (s1[q[h]!]!).isSome := hR.2.2.2.1 q[h]!
    obtain ⟨o, ho⟩ : ∃ o, s1[q[h]!]! = o := ⟨_, rfl⟩
    rcases o with _ | ⟨h₁, h₂⟩
    · have hf : ¬t1[q[h]!]! = true := by rw [hc, ho]; simp
      rw [if_neg hf]
      simp only [ho]
      exact ⟨_, _, rfl, rfl, hR⟩
    · have hf : t1[q[h]!]! = true := by rw [hc, ho]; rfl
      rw [if_pos hf]
      simp only [ho]
      refine ⟨_, _, rfl, rfl, ?_⟩
      exact forIn_rel (Rel n P) _ _ _ (inner_rel hD hstep (hR.2.2.2.2 _ _ ho)) _ _ hR
  · rw [if_neg hh, if_neg hh]
    exact ⟨_, _, rfl, rfl, hR⟩

theorem bases_rel : ∀ (bases : List (ℕ × Table × Table)), (∀ b ∈ bases, Good n P b.1 b.2) →
    ∀ s t, Rel n P s t →
      Rel n P (bases.foldl (fun b a => (⟨b.1.set! a.1 (some a.2), b.2.push a.1⟩ : PSt)) s)
        ((bases.map Prod.fst).foldl (fun b a => (⟨b.1.set! a true, b.2.push a⟩ : RSt)) t)
  | [], _, _, _, h => h
  | b :: bases, hb, s, t, h => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    exact bases_rel bases (fun c hc => hb c (List.mem_cons_of_mem _ hc)) _ _
      (rel_set h (hb b List.mem_cons_self))

theorem rel_init : Rel n P ⟨Array.replicate n none, #[]⟩ ⟨Array.replicate n false, #[]⟩ := by
  refine ⟨rfl, Array.size_replicate, Array.size_replicate, ?_, ?_⟩
  · intro i
    by_cases hi : i < n <;> simp [getElem!_def, hi] <;> rfl
  · intro i x hx
    by_cases hi : i < n
    · simp [getElem!_def, hi] at hx
    · simp [getElem!_def, hi] at hx

theorem centTrivOK_bfsPairs (hD : GroupData n P gens gg sift)
    {step : ℕ → ℕ → ℕ} (hstep : ∀ l < gens.size, ∀ p < n, step l p = ap gens[l]! p)
    {bases : List (ℕ × Table × Table)} (hb : ∀ b ∈ bases, Good n P b.1 b.2)
    (hr : (bfsReach n gens.size step (bases.map Prod.fst)).toList.all id = true) :
    centTrivOK n sift (bfsPairs n gens bases).toList = true := by
  have hR := forIn_rel (Rel n P) (pOuter n gens) (rOuter gens.size step) (List.range' 0 n)
    (outer_rel hD hstep) _ _ (bases_rel bases hb _ _ rel_init)
  have hT := bfsReach_eq n gens.size step (bases.map Prod.fst)
  rw [bfsPairs_eq]
  generalize Id.run (forIn (List.range' 0 n) _ (pOuter n gens)) = S at hR ⊢
  generalize Id.run (forIn (List.range' 0 n) _ (rOuter gens.size step)) = T at hR hT
  rw [hT] at hr
  obtain ⟨-, hs, ht, hst, hg⟩ := hR
  have hall : ∀ i < n, ∃ x, S.1[i]! = some x := by
    intro i hi
    have hm : T.1[i]! = true := by
      rw [List.all_eq_true] at hr
      have := hr _ (Array.getElem_mem_toList (by omega : i < T.1.size))
      rw [getElem!_pos _ i (by omega)]
      simpa using this
    rw [hst] at hm
    exact Option.isSome_iff_exists.1 hm
  simp only [centTrivOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨by simp [hs], fun i hi => ?_⟩
  obtain ⟨x, hx⟩ := hall i hi
  have hget : (S.1.map (·.getD default)).toList.getD i default = x := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_map]
    rw [getElem!_pos _ i (by omega)] at hx
    rw [Array.getElem?_eq_getElem (by omega), hx]
    rfl
  rw [hget]
  have hc := cell_of_good hD (hg i x hx)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
  exact hc

end CFSG.KC.BfsPairs

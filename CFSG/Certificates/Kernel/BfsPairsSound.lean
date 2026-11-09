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
    · simp [Array.set!_eq_setIfInBounds, hq]
    · simp [Array.set!_eq_setIfInBounds, hq]
  · simp [Array.set!_eq_setIfInBounds, getElem!_def, hqi]

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
    rw [ite_eq_left hn, ite_eq_left hf]
    exact ⟨_, _, rfl, rfl, rel_set hR (good_conj hD hg hl')⟩
  · have hf : ¬(!t.1[ap gens[l]! p]!) = true := by
      rw [hc]
      cases e : s.1[ap gens[l]! p]! <;> simp_all
    rw [ite_eq_right hn, ite_eq_right hf]
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
  · rw [ite_eq_left hh, ite_eq_left hh]
    have hc : t1[q[h]!]! = (s1[q[h]!]!).isSome := hR.2.2.2.1 q[h]!
    obtain ⟨o, ho⟩ : ∃ o, s1[q[h]!]! = o := ⟨_, rfl⟩
    rcases o with _ | ⟨h₁, h₂⟩
    · have hf : ¬t1[q[h]!]! = true := by rw [hc, ho]; simp
      rw [ite_eq_right hf]
      simp only [ho]
      exact ⟨_, _, rfl, rfl, hR⟩
    · have hf : t1[q[h]!]! = true := by rw [hc, ho]; rfl
      rw [ite_eq_left hf]
      simp only [ho]
      refine ⟨_, _, rfl, rfl, ?_⟩
      exact forIn_rel (Rel n P) _ _ _ (inner_rel hD hstep (hR.2.2.2.2 _ _ ho)) _ _ hR
  · rw [ite_eq_right hh, ite_eq_right hh]
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
    by_cases hi : i < n <;> (simp [hi]; try rfl)
  · intro i x hx
    by_cases hi : i < n
    · simp [hi] at hx
    · simp [hi] at hx

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

theorem pk10OK_getD : ∀ (l : List ℕ) (P i : ℕ), pk10OK l P = true → l.getD i 0 = P / 1024 ^ i % 1024
  | [], P, i, h => by
    rw [pk10OK, beq_iff_eq] at h
    rw [h, Nat.zero_div, Nat.zero_mod, List.getD_nil]
  | a :: l, P, 0, h => by
    rw [pk10OK, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.getD_cons_zero, pow_zero, Nat.div_one, h.1]
  | a :: l, P, i + 1, h => by
    rw [pk10OK, Bool.and_eq_true] at h
    rw [List.getD_cons_succ, pk10OK_getD l _ i h.2, Nat.div_div_eq_div_mul, pow_succ']

theorem getElem!_push_le {α : Type} [Inhabited α] (a : Array α) (x : α) {h : ℕ}
    (hh : h ≤ a.size) : (a.push x)[h]! = if h < a.size then a[h]! else x := by
  rcases Nat.lt_or_eq_of_le hh with hh | rfl
  · rw [ite_eq_left hh, getElem!_pos _ h (by rw [Array.size_push]; omega), getElem!_pos _ h hh,
      Array.getElem_push_lt hh]
  · rw [ite_eq_right (lt_irrefl _), getElem!_pos _ _ (by rw [Array.size_push]; omega),
      Array.getElem_push_eq]

theorem fieldAdd {w m h Q q : ℕ} (hQ : Q < 2 ^ (w * m)) (hq : q < 2 ^ w) (hh : h ≤ m) :
    (Q + q * 2 ^ (w * m)) / 2 ^ (w * h) % 2 ^ w =
      if h < m then Q / 2 ^ (w * h) % 2 ^ w else q := by
  split_ifs with hlt
  · obtain ⟨d, rfl⟩ : ∃ d, m = h + 1 + d := ⟨m - h - 1, by omega⟩
    have e : 2 ^ (w * (h + 1 + d)) = 2 ^ w * 2 ^ (w * d) * 2 ^ (w * h) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    have e2 : q * (2 ^ w * 2 ^ (w * d)) = 2 ^ w * (q * 2 ^ (w * d)) := by ring
    rw [e, ← mul_assoc, Nat.add_mul_div_right _ _ (by positivity), e2,
      Nat.add_mul_mod_self_left]
  · obtain rfl : h = m := by omega
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hQ, zero_add,
      Nat.mod_eq_of_lt hq]

def RelRF (n w : ℕ) (s : RSt) (t : ℕ × ℕ × ℕ) : Prop :=
  s.1.size = n ∧ (∀ i, s.1[i]! = (decide (i < n) && t.1.testBit i)) ∧ s.2.size = t.2.2 ∧
    (∀ h < t.2.2, s.2[h]! = t.2.1 / 2 ^ (w * h) % 2 ^ w) ∧ t.2.1 < 2 ^ (w * t.2.2)

theorem relRF_push {n w : ℕ} {s : RSt} {t : ℕ × ℕ × ℕ} (hR : RelRF n w s t) {q : ℕ}
    (hq : q < 2 ^ w) :
    RelRF n w ⟨s.1.set! q true, s.2.push q⟩
      ⟨t.1 ||| 2 ^ q, t.2.1 + q * 2 ^ (w * t.2.2), t.2.2 + 1⟩ := by
  obtain ⟨hs, hb, hl, hf, hQ⟩ := hR
  refine ⟨by rw [Array.size_set!, hs], ?_, by rw [Array.size_push, hl], ?_, ?_⟩
  · intro i
    rw [getElem!_set!, hb, hs, Nat.testBit_or, Nat.testBit_two_pow]
    by_cases hqi : q = i
    · subst hqi
      by_cases hqn : q < n <;> simp [hqn]
    · simp [hqi]
  · intro h hh
    dsimp only at hh ⊢
    rw [getElem!_push_le _ _ (by omega), fieldAdd hQ hq (by omega), hl]
    split_ifs with h1
    · exact hf h h1
    · rfl
  · dsimp only
    have h1 : (q + 1) * 2 ^ (w * t.2.2) ≤ 2 ^ w * 2 ^ (w * t.2.2) := Nat.mul_le_mul_right _ hq
    rw [mul_add, mul_one, pow_add, mul_comm (2 ^ (w * t.2.2))]
    rw [add_mul, one_mul] at h1
    linarith

theorem inner_relF {n w : ℕ} {step : ℕ → ℕ → ℕ} (hw : ∀ l p, step l p < 2 ^ w) (k p : ℕ) :
    ∀ l ∈ List.range' 0 k, ∀ s t, RelRF n w s t → ∃ s' t',
      rInner step p l s = pure (ForInStep.yield s') ∧
      rInnerF n w step p l t = pure (ForInStep.yield t') ∧ RelRF n w s' t' := by
  intro l _ s t hR
  have hc := hR.2.1 (step l p)
  unfold rInner rInnerF
  by_cases hn : (decide (step l p < n) && t.1.testBit (step l p)) = false
  · have hf : (!s.1[step l p]!) = true := by rw [hc, hn]; rfl
    rw [ite_eq_left hf, ite_eq_left hn]
    exact ⟨_, _, rfl, rfl, relRF_push hR (hw l p)⟩
  · have hf : ¬(!s.1[step l p]!) = true := by
      rw [hc]
      revert hn
      cases (decide (step l p < n) && t.1.testBit (step l p)) <;> simp
    rw [ite_eq_right hf, ite_eq_right hn]
    exact ⟨_, _, rfl, rfl, hR⟩

theorem outer_relF {n w k : ℕ} {step : ℕ → ℕ → ℕ} (hw : ∀ l p, step l p < 2 ^ w) :
    ∀ h ∈ List.range' 0 n, ∀ s t, RelRF n w s t → ∃ s' t',
      rOuter k step h s = pure (ForInStep.yield s') ∧
      rOuterF n w k step h t = pure (ForInStep.yield t') ∧ RelRF n w s' t' := by
  intro h _ s t hR
  unfold rOuter rOuterF
  by_cases hh : h < t.2.2
  · have hh' : h < s.2.size := by rw [hR.2.2.1]; exact hh
    rw [ite_eq_left hh', ite_eq_left hh, hR.2.2.2.1 h hh, hR.2.1]
    by_cases hb : (decide (t.2.1 / 2 ^ (w * h) % 2 ^ w < n) &&
        t.1.testBit (t.2.1 / 2 ^ (w * h) % 2 ^ w)) = true
    · rw [ite_eq_left hb, ite_eq_left hb]
      exact ⟨_, _, rfl, rfl, forIn_rel (RelRF n w) _ _ _ (inner_relF hw k _) _ _ hR⟩
    · rw [ite_eq_right hb, ite_eq_right hb]
      exact ⟨_, _, rfl, rfl, hR⟩
  · have hh' : ¬h < s.2.size := by rw [hR.2.2.1]; exact hh
    rw [ite_eq_right hh', ite_eq_right hh]
    exact ⟨_, _, rfl, rfl, hR⟩

theorem bases_relF {n w : ℕ} : ∀ (bases : List ℕ), (∀ b ∈ bases, b < 2 ^ w) →
    ∀ s t, RelRF n w s t →
      RelRF n w (bases.foldl (fun b a => (⟨b.1.set! a true, b.2.push a⟩ : RSt)) s)
        (bases.foldl (fun b a => (b.1 ||| 2 ^ a, b.2.1 + a * 2 ^ (w * b.2.2), b.2.2 + 1)) t)
  | [], _, _, _, h => h
  | b :: bases, hb, s, t, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact bases_relF bases (fun c hc => hb c (List.mem_cons_of_mem _ hc)) _ _
      (relRF_push h (hb b List.mem_cons_self))

theorem relRF_init {n w : ℕ} : RelRF n w ⟨Array.replicate n false, #[]⟩ (0, 0, 0) := by
  refine ⟨Array.size_replicate, ?_, rfl, fun h hh => absurd hh (Nat.not_lt_zero _), by simp⟩
  intro i
  by_cases hi : i < n <;> simp [hi]

theorem bfsReach_of_F {n w k : ℕ} {step : ℕ → ℕ → ℕ} (hw : ∀ l p, step l p < 2 ^ w)
    {bases : List ℕ} (hb : ∀ b ∈ bases, b < 2 ^ w)
    (hF : bfsReachF n w k step bases = 2 ^ n - 1) :
    (bfsReach n k step bases).toList.all id = true := by
  have hR := forIn_rel (RelRF n w) (rOuter k step) (rOuterF n w k step) (List.range' 0 n)
    (outer_relF hw) _ _ (bases_relF bases hb _ _ relRF_init)
  obtain ⟨hs, hbits, -⟩ := hR
  unfold bfsReachF at hF
  rw [bfsReach_eq, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have e := hbits i
  rw [Array.length_toList] at hi
  rw [getElem!_pos _ i hi, hF, Nat.testBit_two_pow_sub_one] at e
  rw [Array.getElem_toList, id, e]
  simp only [Bool.and_self, decide_eq_true_eq]
  exact lt_of_lt_of_eq hi hs

end CFSG.KC.BfsPairs

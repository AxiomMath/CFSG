module

public import CFSG.Certificates.Kernel.Misc.Coset.PG

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.KB.Sound

variable {m : ℕ}

theorem wWalkList_append' (F Wd2 : ℕ → ℕ) (RW RM nCos nW : ℕ) :
    ∀ (l1 l2 : List ℕ) (f : ℕ), KB.wWalkList F Wd2 RW RM nCos nW (l1 ++ l2) f =
      KB.wWalkList F Wd2 RW RM nCos nW l2 (KB.wWalkList F Wd2 RW RM nCos nW l1 f)
  | [], _, _ => rfl
  | E :: l1, l2, f => wWalkList_append' F Wd2 RW RM nCos nW l1 l2 (KB.wElem F Wd2 RW RM nCos nW E f)

theorem wWalkList_range (F Wd2 : ℕ → ℕ) (RW RM nCos nW : ℕ) (E st : ℕ → ℕ) :
    ∀ n, (∀ j < n, KB.wElem F Wd2 RW RM nCos nW (E j) (st j) = st (j + 1)) →
      KB.wWalkList F Wd2 RW RM nCos nW ((List.range n).map E) (st 0) = st n
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.map_append, wWalkList_append',
      wWalkList_range F Wd2 RW RM nCos nW E st n (fun j hj => h j (by omega))]
    exact h n (by omega)

@[expose] noncomputable def stepB (F : ℕ → ℕ) (nF c x y f : ℕ) : Bool :=
  Nat.blt f nF && ((Nat.beq (KB.rX (F f)) x && Nat.beq (KB.rC (F f)) c && Nat.beq (KB.rY (F f)) y) ||
    (Nat.beq (KB.rX (F f)) y && Nat.beq (KB.rC (F f)) (Nat.xor c 1) && Nat.beq (KB.rY (F f)) x))

theorem stepB_spec {F : ℕ → ℕ} {nF c x y f : ℕ} (h : stepB F nF c x y f = true) :
    f < nF ∧ ((KB.rX (F f) = x ∧ KB.rC (F f) = c ∧ KB.rY (F f) = y) ∨
      (KB.rX (F f) = y ∧ KB.rC (F f) = Nat.xor c 1 ∧ KB.rY (F f) = x)) := by
  simp only [stepB, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at h
  obtain ⟨hf, h⟩ := h
  refine ⟨hf, ?_⟩
  rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩
  · exact Or.inr ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem pow_three_mem_of_facts (ws : List (List (Fin m × Bool))) {rels : List (List (ℕ × Bool))}
    (hrels : ws.map encW = rels) (hm : m < 256) {amap : ℕ} (htop : KB.topOk amap m = true)
    (T : List (Fin m)) {words : List (List (ℕ × Bool))} (hw : words = T.map fun x => [(x.val, true)])
    {inv L eps nLab nT RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {walk : List ℕ}
    (hL128 : Nat.ble (Nat.succ L) 128 = true) (hlab : Nat.beq nLab (Nat.succ nT) = true)
    (hlabbad : Nat.ble (Nat.succ nLab) KB.bad = true) (hFbad : Nat.ble (Nat.succ nF) KB.bad = true)
    (hnRb : Nat.ble (Nat.succ nR) KB.bad = true) (hnSb : Nat.ble (Nat.succ nS) KB.bad = true)
    (hlr : KB.lensLt rels 256 = true) (hlw : KB.lensLt words 256 = true)
    (hhdr : KB.hdrOk inv L eps amap = true) (hrel : KB.relsOk R nR amap rels = true)
    (hsub : KB.subsOk S nS amap words = true) (hwords : KB.wordsOkB Wd R S inv eps nR nS nW = true)
    (hw2 : KB.words2Ok Wd Wd2 inv nW = true) (htree : KB.treeRange F D L nLab 0 nT = true)
    (hwalk : KB.wWalkList F Wd2 RW RM nLab nW walk nT = nF)
    (g : Fin m) {c a b f1 f2 f3 : ℕ} (hc : KB.sCode amap (g.val, true) = c)
    (h1 : stepB F nF c 0 a f1 = true) (h2 : stepB F nF c a b f2 = true)
    (h3 : stepB F nF c b 0 f3 = true) :
    PresentedGroup.of g ^ 3 ∈ genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T := by
  obtain ⟨hF, hxor, hcode⟩ := KB.facts_sound (pgGen ws) (sword_rels ws hrels) hL128 hlab hlabbad
    hFbad hnRb hnSb hlr hlw hhdr hrel hsub hwords hw2 htree hwalk
  have hg : KB.inAlpha amap g.val := (KB.topOk_sound hm htop g.val).2 g.isLt
  obtain ⟨hcL, hval⟩ := hcode g.val hg
  rw [hc] at hcL hval
  have hgen : pgGen ws g.val = PresentedGroup.of g := by simp [pgGen, g.isLt]
  have step : ∀ {x y f : ℕ}, stepB F nF c x y f = true →
      rel (KB.wordSub (pgGen ws) words) (rep (KB.letterVal (pgGen ws) amap L) F D nT x *
        KB.letterVal (pgGen ws) amap L c) (rep (KB.letterVal (pgGen ws) amap L) F D nT y) := by
    intro x y f hs
    obtain ⟨hf, hfb⟩ := stepB_spec hs
    rcases hfb with ⟨hx, hcc, hy⟩ | ⟨hx, hcc, hy⟩
    · exact rel_of_fwd (hF f hf) hx hcc hy
    · exact rel_of_bwd (hF f hf) hx (by rw [hcc]; exact hxor c hcL) hy
  have := pow_three_mem (rep_zero _ F D nT) (step h1) (step h2) (step h3)
  rwa [hval, hgen, hw, wordSub_letters] at this

end CFSG.KC.MiscCoset

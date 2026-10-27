module

public import Certificates.Data.Kernel.MergeG
public import CFSG.Certificates.Kernel.SporSch.TitsPrimSound
public import CFSG.Certificates.Kernel.MergeReplaySound
public import Certificates.Data.CFSGNative.Schreier.Merge

public section

namespace CFSG.KC.MergeG

section Search

open CFSG.Sporadic.Co1Block.Native CFSG.KC.Enum CFSG.KS CFSG.KC.Pack CFSG.KC.MergeR

@[expose] def initSt (n b x : Nat) : St :=
  ((Array.ofFn (n := n) fun i => i.val).set! x b, (Array.replicate n 1).set! b 2, #[(b, x)], #[])

theorem step_idle {n : Nat} {G : Array (Array Nat)} {st : St} {h : Nat}
    (hh : st.2.2.1.size ≤ h) : mergeSearchStep n G st h = st := by
  rw [step_eq, if_neg (by omega)]

theorem steps_idle {n : Nat} {G : Array (Array Nat)} :
    ∀ (l : List Nat) (st : St), (∀ h ∈ l, st.2.2.1.size ≤ h) → l.foldl (mergeSearchStep n G) st = st
  | [], _, _ => rfl
  | h :: l, st, hl => by
    rw [List.foldl_cons, step_idle (hl h List.mem_cons_self)]
    exact steps_idle l st fun h' hh => hl h' (List.mem_cons_of_mem h hh)

theorem mergeSearchSteps_eq_of_searchK {n w m nw nG : Nat} {Gp : Nat → Nat} {b x cnt Lp F : Nat}
    {G : Array (Array Nat)} (hGs : G.size = nG)
    (hGp : ∀ i < nG, ∀ y < n, (G[i]!)[y]! = pg w m (Gp i) y)
    (h : searchK n w m nw nG Gp b x cnt Lp = true) (hF : n + 1 ≤ F) (hc : cnt ≤ n) :
    ((List.range F).foldl (mergeSearchStep n G) (initSt n b x)).2.2.2.toList =
      (List.range cnt).map fun j => (pg w m Lp (3 * j), pg w m Lp (3 * j + 1),
        pg w m Lp (3 * j + 2)) := by
  unfold searchK at h
  simp only [band_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, strictB_eq] at h
  obtain ⟨hm, hnw, hnm, h2m, hb, hx, hcnt, hf1, hf2⟩ := h
  rw [mask_eq] at hm
  subst hm hnw
  have hw0 := Nat.two_pow_pos w
  have hn : n < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hcnt' : cnt < 2 ^ 32 := hcnt
  rw [foldUp_eq] at hf1 hf2
  have hgood : ((List.range (n + 1)).foldl
      (fun t h => stepK n w (2 ^ w - 1) (n * w) nG cnt Lp Gp b x h t)
      (initK n w (2 ^ w - 1) (n * w) b x)) % 2 = 0 := by
    rw [← land_one]
    exact hf1
  have hrel := stepK_fold rfl hn hcnt' hGs hGp _ _ _ (rel_init (G := G) (Lp := Lp) hn h2 hb hx)
    hgood
  have hk : kOf ((List.range (n + 1)).foldl
      (fun t h => stepK n w (2 ^ w - 1) (n * w) nG cnt Lp Gp b x h t)
      (initK n w (2 ^ w - 1) (n * w) b x)) = cnt := hf2
  have hout := hrel.2.2.2.2.2.2.1
  have hque := hrel.2.2.2.2.2.2.2
  rw [hk] at hout
  obtain ⟨d, rfl⟩ : ∃ d, F = n + 1 + d := ⟨F - (n + 1), by omega⟩
  change (List.foldl (mergeSearchStep n G) (initSt n b x) (List.range (n + 1 + d))).2.2.2.toList = _
  rw [List.range_add, List.foldl_append]
  unfold initSt
  generalize List.foldl (mergeSearchStep n G)
    ((Array.ofFn (n := n) fun i => i.val).set! x b, (Array.replicate n 1).set! b 2, #[(b, x)],
      #[]) (List.range (n + 1)) = s at hout hque
  have hsize : s.2.2.1.size = cnt + 1 := by
    rw [← Array.length_toList, hque, List.length_cons, List.length_map, hout, List.length_map,
      List.length_range]
  rw [steps_idle _ s fun h hh => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hh
    omega]
  rw [hout]
  rfl

end Search

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem strictB_eqM (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bIfT_iff (c e : Bool) :
    Bool.rec (motive := fun _ => Bool) e true c = true ↔ c = true ∨ e = true := by
  cases c <;> simp

theorem nIf_beq (y x t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t (Nat.beq y x) = if y = x then t else e := by
  by_cases h : y = x
  · subst h
    rw [Nat.beq_refl, ite_eq_left rfl]
  · have hb : Nat.beq y x = false := by
      cases h' : Nat.beq y x
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') h
    rw [hb, ite_eq_right h]

theorem nIf_blt (y x t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t (Nat.blt y x) = if y < x then t else e := by
  by_cases h : y < x
  · rw [Nat.blt_eq.mpr h, ite_eq_left h]
  · have hb : Nat.blt y x = false := by
      cases h' : Nat.blt y x
      · rfl
      · exact absurd (Nat.blt_eq.mp h') h
    rw [hb, ite_eq_right h]

theorem isRoot_iff {n TP k r : Nat} :
    isRoot n TP k r = true ↔ r < n ∧ k ≤ pgW 12 TP r := by
  unfold isRoot
  rw [bAnd_iff, Nat.blt_eq]
  by_cases h : pgW 12 TP r < k
  · rw [Nat.blt_eq.mpr h]
    exact ⟨fun h' => absurd h'.2 Bool.false_ne_true, fun h' => absurd h'.2 (by omega)⟩
  · have hb : Nat.blt (pgW 12 TP r) k = false := by
      cases h' : Nat.blt (pgW 12 TP r) k
      · rfl
      · exact absurd (Nat.blt_eq.mp h') h
    rw [hb]
    exact ⟨fun h' => ⟨h'.1, by omega⟩, fun h' => ⟨h'.1, rfl⟩⟩

theorem findK_succ (n w TP PP k f l : Nat) :
    findK n w TP PP k (f + 1) l =
      if pgW 12 TP l < k then findK n w TP PP k f (pgW w PP l) else l :=
  nIf_blt _ _ _ _

theorem div_eqM {S s m : Nat} (hS : 0 < S) (h1 : S * s ≤ m) (h2 : m < S * s + S) :
    m / S = s := by
  apply Nat.le_antisymm
  · have : m / S < s + 1 := (Nat.div_lt_iff_lt_mul hS).2 (by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      exact h2)
    omega
  · exact (Nat.le_div_iff_mul_le hS).2 (by rw [Nat.mul_comm]; exact h1)

theorem allLt_of {n : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    allLt n p = true := by
  unfold allLt
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.all_succ, Bool.and_eq_true]
    exact ⟨ih fun i hi => h i (by omega), h n (by omega)⟩

theorem stepCG_facts {n w kG S TP PP s k i u v : Nat} {GS A : Nat → Nat}
    (h : stepCG n w kG GS S TP PP A s k i u v = true) :
    i < kG ∧ u < n ∧ v < n ∧
      findK n w TP PP k (S + 1) (pgW w (A s) u) = findK n w TP PP k (S + 1) (pgW w (A s) v) ∧
      (findK n w TP PP k (S + 1) (pgW w (A s) (pgW w (GS i) u)) < n ∧
        k ≤ pgW 12 TP (findK n w TP PP k (S + 1) (pgW w (A s) (pgW w (GS i) u)))) ∧
      (findK n w TP PP k (S + 1) (pgW w (A s) (pgW w (GS i) v)) < n ∧
        k ≤ pgW 12 TP (findK n w TP PP k (S + 1) (pgW w (A s) (pgW w (GS i) v)))) ∧
      (findK n w TP PP k (S + 1) (pgW w (A s) (pgW w (GS i) v)) =
          findK n w TP PP k (S + 1) (pgW w (A s) (pgW w (GS i) u)) ∨
        (pgW 12 TP (findK n w TP PP k (S + 1) (pgW w (A s) (pgW w (GS i) v))) = k ∧
          pgW w PP (findK n w TP PP k (S + 1) (pgW w (A s) (pgW w (GS i) v))) =
            findK n w TP PP k (S + 1) (pgW w (A s) (pgW w (GS i) u)))) := by
  unfold stepCG at h
  simp only [strictB_eqM] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h6, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h7, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h8, h9⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h6,
    isRoot_iff.1 h7, isRoot_iff.1 h8, ?_⟩
  rcases (bIfT_iff _ _).1 h9 with h9 | h9
  · exact Or.inl (Nat.eq_of_beq_eq_true h9)
  · obtain ⟨h10, h11⟩ := (bAnd_iff _ _).1 h9
    exact Or.inr ⟨Nat.eq_of_beq_eq_true h10, Nat.eq_of_beq_eq_true h11⟩

theorem mergeCKG_sound {n w kG b x Lc S NS TP PP : Nat} {GS RI RU RV A : Nat → Nat}
    {G : Array (Array Nat)} {L : List (Nat × Nat × Nat)} (_hw : n + 1 < 2 ^ w)
    (hg : G.size = kG ∧ ∀ i < kG, G[i]! = unpack n w (GS i))
    (hc : allN kG (fun i => canonK n w (mask w) (n * w) (GS i)) = true)
    (hL : L = (List.range Lc).map fun k => (RI k, RU k, RV k))
    (h : mergeCKG n w kG GS b x Lc S NS RI RU RV TP PP A = true) : mergeOK n G b x L = true := by
  subst hL
  unfold mergeCKG at h
  obtain ⟨hb, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hx, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hS, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hLS, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hA0, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hseg, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hcnt, hfinal⟩ := (bAnd_iff _ _).1 h
  replace hb : b < n := Nat.blt_eq.mp hb
  replace hx : x < n := Nat.blt_eq.mp hx
  replace hS : 0 < S := Nat.blt_eq.mp hS
  replace hLS : Lc ≤ S * NS := Nat.ble_eq.mp hLS
  have hA0' : ∀ y < n, pgW w (A 0) y = if y = x then b else y := fun y hy => by
    rw [Nat.eq_of_beq_eq_true (allN_spec hA0 y hy), nIf_beq]
  have hGn : ∀ i < kG, ∀ y < n, pgW w (GS i) y < n := by
    intro i hi y hy
    have h1 := allN_spec hc i hi
    unfold canonK at h1
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨-, h3⟩ := (bAnd_iff _ _).1 h2
    rw [pgW_eq]
    exact Nat.blt_eq.mp (allN_spec h3 y hy)
  have SEG : ∀ s < NS, (∀ k, S * s ≤ k → k < min (S * s + S) Lc →
      stepCG n w kG GS S TP PP A s k (RI k) (RU k) (RV k) = true) ∧
      ∀ y < n, pgW w (A (s + 1)) y =
        findK n w TP PP (min (S * s + S) Lc) (S + 1) (pgW w (A s) y) := by
    intro s hs
    have h := allN_spec hseg s hs
    unfold segCG at h
    simp only [strictB_eqM] at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    refine ⟨fun k hk1 hk2 => ?_, fun y hy => Nat.eq_of_beq_eq_true (allN_spec h2 y hy)⟩
    have h3 := allN_spec h1 (k - S * s) (by
      change k - S * s < min (S * s + S) Lc - S * s
      omega)
    have e : Nat.add (Nat.mul S s) (k - S * s) = k := by
      change S * s + (k - S * s) = k
      omega
    rw [e] at h3
    exact h3
  have STEPC : ∀ k < Lc, stepCG n w kG GS S TP PP A (k / S) k (RI k) (RU k) (RV k) = true := by
    intro k hk
    have hd := Nat.div_add_mod k S
    have hm := Nat.mod_lt k hS
    have hs : k / S < NS := by
      by_contra hc'
      have := Nat.mul_le_mul_left S (Nat.le_of_not_lt hc')
      omega
    exact (SEG (k / S) hs).1 k (by omega) (by omega)
  have SF := fun k (hk : k < Lc) => stepCG_facts (STEPC k hk)
  obtain ⟨lq, hlq⟩ : ∃ f : Nat → Nat, ∀ k, f k =
      findK n w TP PP k (S + 1) (pgW w (A (k / S)) (pgW w (GS (RI k)) (RV k))) := ⟨_, fun _ => rfl⟩
  obtain ⟨lp, hlp⟩ : ∃ f : Nat → Nat, ∀ k, f k =
      findK n w TP PP k (S + 1) (pgW w (A (k / S)) (pgW w (GS (RI k)) (RU k))) := ⟨_, fun _ => rfl⟩
  have SFq : ∀ k < Lc, lq k < n ∧ k ≤ pgW 12 TP (lq k) := fun k hk => by
    rw [hlq]
    exact (SF k hk).2.2.2.2.2.1
  have SFp : ∀ k < Lc, lp k < n ∧ k ≤ pgW 12 TP (lp k) := fun k hk => by
    rw [hlp]
    exact (SF k hk).2.2.2.2.1
  have SFd : ∀ k < Lc, lq k = lp k ∨ (pgW 12 TP (lq k) = k ∧ pgW w PP (lq k) = lp k) :=
    fun k hk => by
      rw [hlq, hlp]
      exact (SF k hk).2.2.2.2.2.2
  have D1 : ∀ l < n, pgW 12 TP l < Lc →
      lq (pgW 12 TP l) = l ∧ lq (pgW 12 TP l) ≠ lp (pgW 12 TP l) := by
    have hsum1 : mergeCnt n w GS Lc S TP PP A RI RU RV =
        ∑ k ∈ Finset.range Lc, if lq k ≠ lp k then 1 else 0 := by
      unfold mergeCnt
      rw [foldN_add (g := fun k => mergedC n w GS S TP PP A (Nat.div k S) k (RI k) (RU k) (RV k)),
        Nat.zero_add]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have e0 : mergedC n w GS S TP PP A (Nat.div k S) k (RI k) (RU k) (RV k) =
            if lq k = lp k then 0 else 1 := by
          rw [hlq, hlp]
          exact nIf_beq _ _ _ _
        rw [e0]
        by_cases e : lq k = lp k
        · rw [ite_eq_left e, ite_eq_right (not_not.2 e)]
        · rw [ite_eq_right e, ite_eq_left e]
      · intro _ _
        rfl
    have hsum2 : timedCnt n Lc TP = ∑ l ∈ Finset.range n, if pgW 12 TP l < Lc then 1 else 0 := by
      unfold timedCnt
      rw [foldN_add (g := fun l => if pgW 12 TP l < Lc then 1 else 0), Nat.zero_add]
      intro l c
      rw [nIf_blt]
      by_cases e : pgW 12 TP l < Lc
      · rw [ite_eq_left e, ite_eq_left e]
      · rw [ite_eq_right e, ite_eq_right e, Nat.add_zero]
    have hc' := Nat.eq_of_beq_eq_true hcnt
    rw [hsum1, hsum2, ← Finset.card_filter, ← Finset.card_filter] at hc'
    have hsub : ((Finset.range Lc).filter fun k => lq k ≠ lp k).image lq ⊆
        (Finset.range n).filter fun l => pgW 12 TP l < Lc := by
      intro l hl
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hl
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
      have hk1' := Finset.mem_range.1 hk1
      have h1 := SFd k hk1'
      have h2 : pgW 12 TP (lq k) = k := by
        rcases h1 with h1 | h1
        · exact absurd h1 hk2
        · exact h1.1
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (SFq k hk1').1, by rw [h2]; exact hk1'⟩
    have hinj : Set.InjOn lq ((Finset.range Lc).filter fun k => lq k ≠ lp k) := by
      intro k hk k' hk' e
      have hT : ∀ k, k ∈ ((Finset.range Lc).filter fun k => lq k ≠ lp k) →
          pgW 12 TP (lq k) = k := by
        intro k hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
        rcases SFd k (Finset.mem_range.1 hk1) with h1 | h1
        · exact absurd h1 hk2
        · exact h1.1
      rw [← hT k hk, ← hT k' hk', e]
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_image_of_injOn hinj]; omega)
    intro l hl hlt
    have hmem : l ∈ ((Finset.range Lc).filter fun k => lq k ≠ lp k).image lq := by
      rw [heq]
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hl, hlt⟩
    obtain ⟨k, hk, hkl⟩ := Finset.mem_image.1 hmem
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    have hTk : pgW 12 TP (lq k) = k := by
      rcases SFd k (Finset.mem_range.1 hk1) with h1 | h1
      · exact absurd h1 hk2
      · exact h1.1
    rw [← hkl, hTk]
    exact ⟨rfl, hk2⟩
  have FOR : ∀ l < n, pgW 12 TP l < Lc →
      pgW w PP l < n ∧ pgW 12 TP l < pgW 12 TP (pgW w PP l) := by
    intro l hl hlt
    obtain ⟨h1, h2⟩ := D1 l hl hlt
    have hP : pgW w PP l = lp (pgW 12 TP l) := by
      rcases SFd _ hlt with h3 | h3
      · exact absurd h3 h2
      · rw [← h3.2, h1]
    obtain ⟨hpn, hpk⟩ := SFp _ hlt
    refine ⟨by rw [hP]; exact hpn, ?_⟩
    rw [hP]
    rcases Nat.lt_or_ge (pgW 12 TP l) (pgW 12 TP (lp (pgW 12 TP l))) with h3 | h3
    · exact h3
    · exfalso
      have e : pgW 12 TP (lp (pgW 12 TP l)) = pgW 12 TP l := by omega
      have := (D1 _ hpn (by omega)).1
      rw [e] at this
      exact h2 this
  have R1 : ∀ k < Lc, ∀ r < n, pgW 12 TP r = k → r = lq k ∧ lq k ≠ lp k := by
    intro k hk r hr e
    obtain ⟨h1, h2⟩ := D1 r hr (by omega)
    rw [e] at h1 h2
    exact ⟨h1.symm, h2⟩
  have Fid : ∀ k f l, k ≤ pgW 12 TP l → findK n w TP PP k (f + 1) l = l := fun k f l h => by
    rw [findK_succ, ite_eq_right (by omega)]
  have R : ∀ f l k0 k, l < n → k0 ≤ pgW 12 TP l → k ≤ Lc → k ≤ k0 + f →
      findK n w TP PP k (f + 1) l < n ∧ k ≤ pgW 12 TP (findK n w TP PP k (f + 1) l) := by
    intro f
    induction f with
    | zero =>
      intro l k0 k hl hk0 hk hkf
      rw [Fid k 0 l (by omega)]
      exact ⟨hl, by omega⟩
    | succ f ih =>
      intro l k0 k hl hk0 hk hkf
      rw [findK_succ]
      by_cases hlt : pgW 12 TP l < k
      · rw [ite_eq_left hlt]
        obtain ⟨hPn, hPgt⟩ := FOR l hl (by omega)
        exact ih (pgW w PP l) (k0 + 1) k hPn (by omega) hk (by omega)
      · rw [ite_eq_right hlt]
        exact ⟨hl, by omega⟩
  have F2 : ∀ f l k0 k, l < n → k0 ≤ pgW 12 TP l → k < Lc → k + 1 ≤ k0 + f →
      findK n w TP PP (k + 1) (f + 1) l =
        if pgW 12 TP (findK n w TP PP k (f + 1) l) = k then
          pgW w PP (findK n w TP PP k (f + 1) l) else findK n w TP PP k (f + 1) l := by
    intro f
    induction f with
    | zero =>
      intro l k0 k hl hk0 hk hkf
      rw [Fid (k + 1) 0 l (by omega), Fid k 0 l (by omega),
        ite_eq_right (by omega : ¬ pgW 12 TP l = k)]
    | succ f ih =>
      intro l k0 k hl hk0 hk hkf
      rw [findK_succ n w TP PP (k + 1), findK_succ n w TP PP k]
      rcases Nat.lt_trichotomy (pgW 12 TP l) k with hlt | hlt | hlt
      · rw [ite_eq_left (by omega : pgW 12 TP l < k + 1), ite_eq_left hlt]
        obtain ⟨hPn, hPgt⟩ := FOR l hl (by omega)
        exact ih (pgW w PP l) (k0 + 1) k hPn (by omega) hk (by omega)
      · rw [ite_eq_left (by omega : pgW 12 TP l < k + 1),
          ite_eq_right (by omega : ¬ pgW 12 TP l < k), ite_eq_left hlt]
        obtain ⟨hPn, hPgt⟩ := FOR l hl (by omega)
        exact Fid (k + 1) f (pgW w PP l) (by omega)
      · rw [ite_eq_right (by omega : ¬ pgW 12 TP l < k + 1),
          ite_eq_right (by omega : ¬ pgW 12 TP l < k),
          ite_eq_right (by omega : ¬ pgW 12 TP l = k)]
  have Aroot : ∀ s ≤ NS, ∀ y < n,
      pgW w (A s) y < n ∧ min (S * s) Lc ≤ pgW 12 TP (pgW w (A s) y) := by
    intro s
    induction s with
    | zero =>
      intro _ y hy
      rw [hA0' y hy]
      refine ⟨?_, by simp⟩
      by_cases e : y = x
      · rw [ite_eq_left e]
        exact hb
      · rw [ite_eq_right e]
        exact hy
    | succ s ih =>
      intro hs y hy
      rw [(SEG s (by omega)).2 y hy, Nat.mul_succ]
      obtain ⟨h1, h2⟩ := ih (by omega) y hy
      exact R S _ (min (S * s) Lc) (min (S * s + S) Lc) h1 h2 (by omega) (by omega)
  have STEPL : ∀ k < Lc, ∀ (lab : Array Nat), lab.size = n →
      (∀ y < n, lab[y]! = findK n w TP PP k (S + 1) (pgW w (A (k / S)) y)) →
      (mergeStep n G (true, lab) (RI k, RU k, RV k)).1 = true ∧
        (mergeStep n G (true, lab) (RI k, RU k, RV k)).2.size = n ∧
        ∀ y < n, (mergeStep n G (true, lab) (RI k, RU k, RV k)).2[y]! =
          findK n w TP PP (k + 1) (S + 1) (pgW w (A ((k + 1) / S)) y) := by
    intro k hk lab hsz hlab
    obtain ⟨hi, hu, hv, hruv, -, -, -⟩ := SF k hk
    have hd := Nat.div_add_mod k S
    have hm := Nat.mod_lt k hS
    have hs : k / S < NS := by
      by_contra hc'
      have := Nat.mul_le_mul_left S (Nat.le_of_not_lt hc')
      omega
    have hG : ∀ y < n, (G[RI k]!)[y]! = pgW w (GS (RI k)) y := fun y hy => by
      rw [hg.2 _ hi, unpackW_get hy, pgW_eq]
    unfold mergeStep
    dsimp only
    refine ⟨?_, by simp [relabel, hsz], fun y hy => ?_⟩
    · rw [hlab _ hu, hlab _ hv, hruv]
      simp [hg.1, hi, hu, hv]
    · simp only [relabel]
      rw [getElem!_pos _ y (by simpa [hsz] using hy), Array.getElem_map,
        ← getElem!_pos lab y (by omega), hG _ hu, hG _ hv, hlab _ (hGn _ hi _ hu),
        hlab _ (hGn _ hi _ hv), ← hlq, ← hlp, hlab y hy]
      have hA := Aroot (k / S) (by omega) y hy
      rw [Nat.min_eq_left (by omega : S * (k / S) ≤ Lc)] at hA
      obtain ⟨hr1, hr2⟩ :=
        R S (pgW w (A (k / S)) y) (S * (k / S)) k hA.1 hA.2 (by omega) (by omega)
      have hF2 := F2 S (pgW w (A (k / S)) y) (S * (k / S)) k hA.1 hA.2 hk (by omega)
      generalize findK n w TP PP k (S + 1) (pgW w (A (k / S)) y) = r at hr1 hr2 hF2 ⊢
      have key : (if (r == lq k) = true then lp k else r) =
          findK n w TP PP (k + 1) (S + 1) (pgW w (A (k / S)) y) := by
        rw [hF2]
        rcases SFd k hk with e | ⟨e1, e2⟩
        · have hne : pgW 12 TP r ≠ k := fun e' => (R1 k hk r hr1 e').2 e
          rw [ite_eq_right hne]
          by_cases hr : r = lq k
          · rw [ite_eq_left (by simp [hr] : (r == lq k) = true), ← e, hr]
          · rw [ite_eq_right (by simp [hr] : ¬ (r == lq k) = true)]
        · by_cases hr : r = lq k
          · rw [ite_eq_left (by simp [hr] : (r == lq k) = true), hr, ite_eq_left e1, e2]
          · have hne : pgW 12 TP r ≠ k := fun e' => hr (R1 k hk r hr1 e').1
            rw [ite_eq_right (by simp [hr] : ¬ (r == lq k) = true), ite_eq_right hne]
      rw [key]
      rcases Nat.lt_or_ge (k % S + 1) S with h1 | h1
      · rw [div_eqM hS (s := k / S) (m := k + 1) (by omega) (by omega)]
      · have e1 : (k + 1) / S = k / S + 1 := div_eqM hS (by rw [Nat.mul_succ]; omega)
          (by rw [Nat.mul_succ]; omega)
        have e2 : min (S * (k / S) + S) Lc = k + 1 := by omega
        rw [e1, (SEG _ hs).2 y hy, e2]
        refine (Fid _ _ _ ?_).symm
        have := (Aroot (k / S + 1) (by omega) y hy).2
        rw [(SEG _ hs).2 y hy, e2, Nat.mul_succ] at this
        omega
  have J : ∀ k ≤ Lc,
      (((List.range k).map fun k => (RI k, RU k, RV k)).foldl (mergeStep n G)
          (true, mergeInit n b x)).1 = true ∧
      (((List.range k).map fun k => (RI k, RU k, RV k)).foldl (mergeStep n G)
          (true, mergeInit n b x)).2.size = n ∧
      ∀ y < n, (((List.range k).map fun k => (RI k, RU k, RV k)).foldl (mergeStep n G)
          (true, mergeInit n b x)).2[y]! =
        findK n w TP PP k (S + 1) (pgW w (A (k / S)) y) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [List.range_zero, List.map_nil, List.foldl_nil]
      refine ⟨trivial, by simp [mergeInit], fun y hy => ?_⟩
      rw [Nat.zero_div, Fid 0 S _ (Nat.zero_le _), hA0' y hy]
      unfold mergeInit
      rw [getElem!_pos _ y (by simpa using hy), Array.getElem_ofFn]
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      generalize List.foldl (mergeStep n G) (true, mergeInit n b x)
        (List.map (fun k => (RI k, RU k, RV k)) (List.range k)) = st at h1 h2 h3 ⊢
      obtain ⟨ok, lab⟩ := st
      dsimp only at h1 h2 h3
      subst h1
      exact STEPL k (by omega) lab h2 h3
  have Afin : ∀ y < n, findK n w TP PP Lc (S + 1) (pgW w (A (Lc / S)) y) = pgW w (A NS) y := by
    intro y hy
    have hs0 : Lc / S ≤ NS := Nat.div_le_of_le_mul hLS
    have hdm := Nat.div_add_mod Lc S
    have hmod := Nat.mod_lt Lc hS
    rcases Nat.lt_or_ge (Lc / S) NS with hlt | hge
    · have h1 : pgW w (A (Lc / S + 1)) y =
          findK n w TP PP Lc (S + 1) (pgW w (A (Lc / S)) y) := by
        rw [(SEG _ hlt).2 y hy]
        have e : min (S * (Lc / S) + S) Lc = Lc := by omega
        rw [e]
      have h2 : ∀ d, Lc / S + 1 + d ≤ NS →
          pgW w (A (Lc / S + 1 + d)) y = pgW w (A (Lc / S + 1)) y := by
        intro d
        induction d with
        | zero => intro _; rfl
        | succ d ih =>
          intro hd
          have hs : Lc / S + 1 + d < NS := by omega
          have hle := Nat.mul_le_mul_left S (Nat.le_add_right (Lc / S + 1) d)
          rw [Nat.mul_succ] at hle
          change pgW w (A (Lc / S + 1 + d + 1)) y = _
          rw [(SEG _ hs).2 y hy]
          have hroot := (Aroot (Lc / S + 1 + d) (by omega) y hy).2
          have e : min (S * (Lc / S + 1 + d) + S) Lc = Lc := by omega
          have e2 : min (S * (Lc / S + 1 + d)) Lc = Lc := by omega
          rw [e2] at hroot
          rw [e, Fid _ _ _ hroot, ih (by omega)]
      have e : Lc / S + 1 + (NS - (Lc / S + 1)) = NS := by omega
      have h3 := h2 (NS - (Lc / S + 1)) (by omega)
      rw [e] at h3
      rw [h3, h1]
    · have e : Lc / S = NS := by omega
      have hroot := (Aroot NS (Nat.le_refl _) y hy).2
      have hNS : S * NS ≤ Lc := by rw [← e]; omega
      rw [Nat.min_eq_right hLS] at hroot
      rw [e, Fid _ _ _ hroot]
  obtain ⟨hok, -, hlab⟩ := J Lc (Nat.le_refl _)
  unfold finalC at hfinal
  rw [strictB_eqM] at hfinal
  obtain ⟨-, hall⟩ := (bAnd_iff _ _).1 hfinal
  unfold mergeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hb, hx⟩, hok⟩, allLt_of fun a ha => ?_⟩
  rw [hlab a ha, hlab 0 (by omega), Afin a ha, Afin 0 (by omega),
    Nat.eq_of_beq_eq_true (allN_spec hall a ha)]
  exact beq_self_eq_true _

end CFSG.KC.MergeG

end

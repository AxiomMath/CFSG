
module

public import CFSG.Certificates.Kernel.L5.HFCSound
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

section Grp

variable {G : List (CV 16)} {n : Nat} {mul : Nat → Nat → Nat} (hl : G.length = n)
  (hnd : G.Nodup) (h1 : (1 : CV 16) ∈ G)
  (hm : ∀ a < n, ∀ b < n, mul a b < n ∧ G.getD a 1 * G.getD b 1 = G.getD (mul a b) 1)

include hl hm in
theorem mulClosed_of_tab : mulClosedChkP G = true := by
  unfold mulClosedChkP
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  simp only [decide_eq_true_eq]
  obtain ⟨ia, ea⟩ := getD_idxOf ha
  obtain ⟨ib, eb⟩ := getD_idxOf hb
  obtain ⟨hlt, he⟩ := hm _ (hl ▸ ia) _ (hl ▸ ib)
  rw [← ea, ← eb, he, List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

include hl hnd h1 hm in
theorem decide_mem_clos_idx {gsx : List (CV 16)} (hgs : ∀ g ∈ gsx, g ∈ G) (k : Nat) {y : CV 16}
    (hy : y ∈ G) :
    decide (y ∈ closureList gsx k) =
      (closG n mul (G.idxOf 1) (gsx.map G.idxOf) k).testBit (G.idxOf y) := by
  obtain ⟨i1, e1⟩ := getD_idxOf h1
  have e : gsx = (gsx.map G.idxOf).map fun s => G.getD s 1 := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id gsx]
    apply List.map_congr_left
    intro g hg
    exact ((getD_idxOf (hgs g hg)).2).symm
  have hg : ∀ s ∈ gsx.map G.idxOf, s < n := by
    intro s hs
    obtain ⟨g, hg, hs'⟩ := List.mem_map.1 hs
    rw [← hs', ← hl]
    exact (getD_idxOf (hgs g hg)).1
  obtain ⟨iy, ey⟩ := getD_idxOf hy
  conv_lhs => rw [e, ← ey]
  exact decide_mem_closure_gen G n mul (G.idxOf 1) (hl ▸ i1) e1 hm hl hnd _ hg k (hl ▸ iy)

end Grp

theorem G72tab_facts (hG : G72TabChk = true) : G72C.length = 72 ∧ G72C.Nodup ∧
    (1 : CV 16) ∈ G72C ∧ ∀ a < 72, ∀ b < 72,
      mG a b < 72 ∧ G72C.getD a 1 * G72C.getD b 1 = G72C.getD (mG a b) 1 := by
  unfold G72TabChk at hG
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hG
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hG
  exact ⟨h1, h2, h3, fun a ha b hb => h4 a ha b hb⟩

theorem G72chk_facts (hC : G72Chk = true) : invClosedChkP G72C = true ∧ (∀ a ∈ n24C, a ∈ G72C) ∧
    yC ∈ G72C ∧ wC ∈ G72C ∧ cHC ∈ G72C ∧ twC⁻¹ * yC * twC = yC ∧ twC⁻¹ * wC * twC = wC := by
  unfold G72Chk at hC
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hC
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hC
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem G72C_mul (hG : G72TabChk = true) : mulClosedChkP G72C = true :=
  mulClosed_of_tab (G72tab_facts hG).1 (G72tab_facts hG).2.2.2

theorem n24CovC_false (C : List (CV 16)) : n24CovC C false = n24C.all fun a => decide (a ∈ C) := by
  unfold n24CovC
  rfl

theorem n24CovC_tw (C : List (CV 16)) :
    n24CovC C true = n24C.all fun a => decide (twC * a * twC⁻¹ ∈ C) := by
  unfold n24CovC
  rfl

theorem mem3 {a b c : CV 16} (ha : a ∈ G72C) (hb : b ∈ G72C) (hc : c ∈ G72C) :
    ∀ g ∈ [a, b, c], g ∈ G72C := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> assumption

section G72

variable (hG : G72TabChk = true) (hC : G72Chk = true)
include hG hC

theorem decide_mem_G72 {gsx : List (CV 16)} (hgs : ∀ g ∈ gsx, g ∈ G72C) (k : Nat) {y : CV 16}
    (hy : y ∈ G72C) :
    decide (y ∈ closureList gsx k) =
      (closG 72 mG (G72C.idxOf 1) (gsx.map G72C.idxOf) k).testBit (G72C.idxOf y) :=
  decide_mem_clos_idx (G72tab_facts hG).1 (G72tab_facts hG).2.1 (G72tab_facts hG).2.2.1
    (G72tab_facts hG).2.2.2 hgs k hy

theorem covC_eq (x : CV 16) : covC x = n24CovC (closureList [yC, wC, x] 8) false := by
  obtain ⟨-, hsub, hy, hw, -⟩ := G72chk_facts hC
  unfold covC
  split_ifs with hx
  · rw [n24CovC_false]
    unfold covIdx idx72
    dsimp only
    apply all_congr_mem
    intro a ha
    rw [decide_mem_G72 hG hC (mem3 hy hw hx) 8 (hsub a ha)]
    simp only [List.map_cons, List.map_nil]
  · rfl

theorem n24CovC_true (x : CV 16) : n24CovC (closureList [yC, wC, x] 8) true =
    n24CovC (closureList [yC, wC, twC⁻¹ * x * twC] 8) false := by
  obtain ⟨-, -, -, -, -, hty, htw⟩ := G72chk_facts hC
  have hmap : closureList [yC, wC, twC⁻¹ * x * twC] 8 =
      (closureList [yC, wC, x] 8).map fun g => twC⁻¹ * g * twC := by
    rw [← closureList_map_hom (fun g => twC⁻¹ * g * twC) (fun a b => by group) (by group)
      (fun a b h => by simpa using h)]
    simp only [List.map_cons, List.map_nil, hty, htw]
  rw [n24CovC_tw, n24CovC_false, hmap]
  apply all_congr_mem
  intro a _
  rw [decide_eq_decide, List.mem_map]
  constructor
  · intro h
    exact ⟨_, h, by group⟩
  · rintro ⟨c, hc, rfl⟩
    have e : twC * (twC⁻¹ * c * twC) * twC⁻¹ = c := by group
    rw [e]
    exact hc

theorem n24TailC_eq (x : CV 16) (o : List Nat) : n24TailC x o = n24TailF x o := by
  unfold n24TailC n24TailF
  dsimp only
  rw [covC_eq hG hC, covC_eq hG hC, n24CovC_true hG hC]

theorem n24ChkC_eq (x : CV 16) : n24ChkC x = n24ChkF x := by
  unfold n24ChkC n24ChkF
  dsimp only
  by_cases h : (orbListN [yC, wC, x] 3).length = 5
  · have h5 := orbListN_len5 _ h
    rw [decide_eq_true h, Bool.true_or, decide_eq_true h5, Bool.true_or]
  · rw [decide_eq_false h, Bool.false_or, n24TailC_eq hG hC]

theorem n24Entry_ev (x : CV 16) : n24Entry (ev x) = n24EntryC x := by
  unfold n24Entry n24EntryC
  rw [n24Pre_ev, n24Chk_ev, n24ChkC_eq hG hC]

theorem cHatC_eq (x : CV 16) : cHatC x = decide (cHC ∈ closureList [wC, n24C.getD 6 1, x] 8) := by
  obtain ⟨-, hsub, -, hw, hc, -⟩ := G72chk_facts hC
  unfold cHatC
  split_ifs with hx
  · have h6 : n24C.getD 6 1 ∈ G72C := by
      apply hsub
      rw [List.getD_eq_getElem _ _ (by simp [n24C, n24L])]
      exact List.getElem_mem _
    unfold idx72
    rw [decide_mem_G72 hG hC (mem3 hw h6 hx) 8 hc]
    simp only [List.map_cons, List.map_nil]
  · rfl

theorem famEntry_eq (x : CV 16) : famEntry G72L (ev x) = famEntryC x := by
  rw [famEntry_ev]
  unfold famEntryF famEntryC
  rw [cHatC_eq hG hC]

end G72

@[expose] noncomputable def d8ChkG (G D : List (CV 16)) (y b c : CV 16) : Bool :=
  let gens : List (CV 16) := [y, b, c]
  let T := closureList gens 8
  (T.all fun t => gens.all fun s => decide (t * s ∈ T) && decide (t * s⁻¹ ∈ T)) &&
    (let L := G.filter fun x => decide (x ∈ T)
     !decide (L.length = 8) || (L.all (fun x => decide (x ∈ D)) && D.all fun x => decide (x ∈ L)))

@[expose] noncomputable def d8ChkIG (G D : List (CV 16)) (n : Nat) (mul : Nat → Nat → Nat)
    (inv : Nat → Nat) (i0 iy i j : Nat) : Bool :=
  let gs := [iy, i, j]
  let M := closG n mul i0 gs 8
  ((List.range n).all fun a => !(M.testBit a) || gs.all fun s =>
      M.testBit (mul a s) && M.testBit (mul a (inv s))) &&
    (let L := ((List.range n).filter fun a => M.testBit a).map fun a => G.getD a 1
     !decide (L.length = 8) || (L.all (fun x => decide (x ∈ D)) && D.all fun x => decide (x ∈ L)))

theorem G_eq_map {G : List (CV 16)} {n : Nat} (hl : G.length = n) :
    G = (List.range n).map fun a => G.getD a 1 := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h1]

section D8

variable {G : List (CV 16)} {n : Nat} {mul : Nat → Nat → Nat} {inv : Nat → Nat} {i0 iy : Nat}
  {y : CV 16} (D : List (CV 16)) (hl : G.length = n) (hnd : G.Nodup) (hi0 : i0 < n)
  (h0 : G.getD i0 1 = 1) (hiy : iy < n) (hy : G.getD iy 1 = y)
  (hm : ∀ a < n, ∀ b < n, mul a b < n ∧ G.getD a 1 * G.getD b 1 = G.getD (mul a b) 1)
  (hv : ∀ a < n, inv a < n ∧ (G.getD a 1)⁻¹ = G.getD (inv a) 1)
include hl hnd hi0 h0 hiy hy hm hv

theorem d8ChkG_eq {i j : Nat} (hi : i < n) (hj : j < n) :
    d8ChkG G D y (G.getD i 1) (G.getD j 1) = d8ChkIG G D n mul inv i0 iy i j := by
  have hg : ∀ s ∈ [iy, i, j], s < n := by
    intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> assumption
  have eg : [y, G.getD i 1, G.getD j 1] = [iy, i, j].map fun s => G.getD s 1 := by
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, hy]
  have hmem := mem_closureList_gen G n mul i0 hi0 h0 hm [iy, i, j] hg 8
  unfold d8ChkG d8ChkIG
  dsimp only
  rw [eg]
  generalize closureList ([iy, i, j].map fun s => G.getD s 1) 8 = T at hmem ⊢
  generalize closG n mul i0 [iy, i, j] 8 = M at hmem ⊢
  have hbit : ∀ e < n, decide (G.getD e 1 ∈ T) = M.testBit e := by
    intro e he
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    rw [hmem]
    constructor
    · rintro ⟨a, ha, hb, h⟩
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h
      rw [(hnd.getElem_inj_iff).1 h]
      exact hb
    · intro hb
      exact ⟨e, he, hb, rfl⟩
  have hall : ∀ P : CV 16 → Bool,
      T.all P = (List.range n).all fun a => !(M.testBit a) || P (G.getD a 1) := by
    intro P
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    simp only [List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · intro h a ha
      by_cases hb : M.testBit a
      · exact Or.inr (h _ ((hmem _).2 ⟨a, ha, hb, rfl⟩))
      · exact Or.inl (by simpa using hb)
    · intro h x hx
      obtain ⟨a, ha, hb, rfl⟩ := (hmem x).1 hx
      rcases h a ha with h' | h'
      · rw [hb] at h'
        exact absurd h' (by decide)
      · exact h'
  have hfil : G.filter (fun x => decide (x ∈ T)) =
      ((List.range n).filter fun a => M.testBit a).map fun a => G.getD a 1 := by
    conv_lhs => rw [G_eq_map hl]
    rw [List.filter_map]
    refine congrArg (List.map fun a => G.getD a 1) (List.filter_congr fun a ha => ?_)
    simp only [Function.comp_apply]
    exact hbit a (List.mem_range.1 ha)
  rw [hfil, hall]
  refine congrArg (fun z => z && _) ?_
  apply all_congr_mem
  intro a ha
  have ha' := List.mem_range.1 ha
  refine congrArg (fun z => _ || z) ?_
  beta_reduce
  rw [List.all_map]
  apply all_congr_mem
  intro s hs
  have hs' := hg s hs
  obtain ⟨hi1, hi2⟩ := hv s hs'
  obtain ⟨hm1, hm2⟩ := hm a ha' s hs'
  obtain ⟨hn1, hn2⟩ := hm a ha' (inv s) hi1
  simp only [Function.comp_apply]
  rw [hm2, hi2, hn2, hbit _ hm1, hbit _ hn1]

end D8

theorem tab_facts (hT : n24TabChk = true) : n24C.length = 24 ∧ n24C.Nodup ∧ n24C.getD 0 1 = 1 ∧
    n24C.getD 3 1 = yC ∧ ∀ a < 24, iI a < 24 ∧ (n24C.getD a 1)⁻¹ = n24C.getD (iI a) 1 ∧
      ∀ b < 24, mI a b < 24 ∧ n24C.getD a 1 * n24C.getD b 1 = n24C.getD (mI a b) 1 := by
  unfold n24TabChk at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hT
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hT
  exact ⟨h1, h2, h3, h4, fun a ha => ⟨(h5 a ha).1.1, (h5 a ha).1.2, fun b hb => h5 a ha |>.2 b hb⟩⟩

theorem d8_enum_of (hT : n24TabChk = true) (hd : d8ChkAll = true) :
    n24L.all (fun b => n24L.all fun c => d8Chk b c) = true := by
  obtain ⟨hl, hnd, h0, h3, hmi⟩ := tab_facts hT
  have hm : ∀ a < 24, ∀ b < 24,
      mI a b < 24 ∧ n24C.getD a 1 * n24C.getD b 1 = n24C.getD (mI a b) 1 :=
    fun a ha b hb => (hmi a ha).2.2 b hb
  have hv : ∀ a < 24, iI a < 24 ∧ (n24C.getD a 1)⁻¹ = n24C.getD (iI a) 1 :=
    fun a ha => ⟨(hmi a ha).1, (hmi a ha).2.1⟩
  have key : ∀ i < 24, ∀ j < 24, d8ChkC (n24C.getD i 1) (n24C.getD j 1) = d8ChkI i j :=
    fun i hi j hj => d8ChkG_eq d8C hl hnd (by norm_num) h0 (by norm_num) h3 hm hv hi hj
  rw [n24L_eq, List.all_map, G_eq_map hl, List.all_map]
  unfold d8ChkAll at hd
  rw [List.all_eq_true] at hd ⊢
  intro i hi
  have hi' := List.mem_range.1 hi
  have h := hd i hi
  rw [List.all_eq_true] at h
  simp only [Function.comp_apply, List.all_map, List.all_eq_true]
  intro j hj
  rw [d8Chk_ev, key i hi' j (List.mem_range.1 hj)]
  exact h j hj

end CFSG.Certificates.Kernel.L5H

end

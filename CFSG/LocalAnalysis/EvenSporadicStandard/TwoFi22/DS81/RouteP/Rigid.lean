module

public import CFSG.Perm.ChainSpec
public import Certificates.Data.RouteP.Rigid
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.RigidAction

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid.Native

section Native

theorem inTree_spec {T : CFSG.Perm.Native.Tree} {p : ℕ} (h : inTree T p = true) :
    ∃ k < T.pts.size, ap T.pts k = p := by
  simp only [inTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨ap T.pos p, h.1, h.2⟩

theorem mem_candList_iff {letters : Array Table} {T : CFSG.Perm.Native.Tree} {c : ℕ} :
    c ∈ candList letters T ↔ (∃ k < T.pts.size, ap T.pts k = c) ∧ candOK letters T c = true := by
  unfold candList
  rw [List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨u, hu, huc⟩, hc⟩
    rw [Array.mem_toList_iff] at hu
    obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.1 hu
    refine ⟨⟨k, hk, ?_⟩, hc⟩
    rw [ap, getElem!_pos T.pts k hk, hke]
    exact huc
  · rintro ⟨⟨k, hk, hkc⟩, hc⟩
    refine ⟨⟨T.pts[k], ?_, ?_⟩, hc⟩
    · rw [Array.mem_toList_iff]
      exact Array.mem_iff_getElem.2 ⟨k, hk, rfl⟩
    · rw [← hkc, ap, getElem!_pos T.pts k hk]

theorem ofFn_getElem! {n : ℕ} {f : Fin n → ℕ} {i : ℕ} (hi : i < n) :
    (Array.ofFn (n := n) f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa [Array.size_ofFn] using hi)]
  simp only [Array.getElem_ofFn]

theorem candOK_of_forall {letters : Array Table} {T : CFSG.Perm.Native.Tree} {c : ℕ}
    (hcl : ∀ k < T.pts.size, ∀ l < letters.size,
      ap T.pos (ap letters[l]! (ap T.pts k)) < T.pts.size)
    (h : ∀ k < T.pts.size, ∀ l < letters.size,
      propagate T letters c (ap T.pos (ap letters[l]! (ap T.pts k))) =
        ap letters[l]! (propagate T letters c k)) :
    candOK letters T c = true := by
  unfold candOK
  dsimp only
  rw [allIn_eq_true]
  intro k _ hk
  rw [allIn_eq_true]
  intro l _ hl
  rw [beq_iff_eq, ofFn_getElem! (hcl k hk l hl), ofFn_getElem! hk]
  exact h k hk l hl

theorem allSections_spec {α : Type} {p : List α → Bool} : ∀ {cs : List (List α)},
    allSections cs p = true → ∀ l : List α, List.Forall₂ (fun x s => x ∈ s) l cs → p l = true := by
  intro cs
  induction cs generalizing p with
  | nil =>
    intro h l hl
    simp only [allSections] at h
    cases hl with
    | nil => exact h
  | cons s rest ih =>
    intro h l hl
    simp only [allSections] at h
    rw [List.all_eq_true] at h
    obtain ⟨x, l', hx, hl', rfl⟩ := List.forall₂_cons_right_iff.mp hl
    exact ih (p := fun l => p (x :: l)) (h x hx) l' hl'

theorem forall₂_map_mem {α β : Type} {f : α → β} {F : α → List β} {xs : List α}
    (h : ∀ x ∈ xs, f x ∈ F x) : List.Forall₂ (fun x s => x ∈ s) (xs.map f) (xs.map F) := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons]
    rw [List.forall_mem_cons] at h
    exact List.Forall₂.cons h.1 (ih h.2)

theorem combined_eq {letters : Array Table} {φ : ℕ → ℕ} {g : CFSG.Perm.Native.Tree → ℕ}
    {trees : List CFSG.Perm.Native.Tree}
    (hT : ∀ T ∈ trees, ∀ w, inTree T w = true → propagate T letters (g T) (ap T.pos w) = φ w)
    {v : ℕ} (hv : ∃ T ∈ trees, inTree T v = true) :
    combined letters trees (trees.map g) v = φ v := by
  induction trees with
  | nil =>
    obtain ⟨T, hTmem, -⟩ := hv
    simp at hTmem
  | cons T Ts ih =>
    rw [List.map_cons]
    by_cases h : inTree T v = true
    · simp only [combined, h, if_true]
      exact hT T List.mem_cons_self v h
    · simp only [combined, h, if_false]
      obtain ⟨T', hT'mem, hT'in⟩ := hv
      rcases List.mem_cons.mp hT'mem with rfl | hT'mem
      · exact absurd hT'in h
      · exact ih (fun T' hT' => hT T' (List.mem_cons_of_mem T hT')) ⟨T', hT'mem, hT'in⟩

theorem ap_toTables {n : ℕ} {gens : Array (Array ℕ)} (hn : n < 2 ^ 32)
    (hg : ∀ k < gens.size, gens[k]!.size = n ∧ ∀ i < n, (gens[k]!)[i]! < n)
    {k : ℕ} (hk : k < gens.size) {i : ℕ} (hi : i < n) :
    ap (toTables gens)[k]! i = (gens[k]!)[i]! := by
  have hsize : (gens[k]!).size = n := (hg k hk).1
  have hx : (gens[k]!)[i]! < n := (hg k hk).2 i hi
  have hget : (toTables gens)[k]! = (gens[k]!).map UInt32.ofNat := by
    unfold toTables
    rw [getElem!_pos (gens.map fun g => g.map UInt32.ofNat) k (by rw [Array.size_map]; exact hk),
      Array.getElem_map, getElem!_pos gens k hk]
  have hlt : i < ((gens[k]!).map UInt32.ofNat).size := by
    rw [Array.size_map, hsize]; exact hi
  have hlt' : i < (gens[k]!).size := by rw [hsize]; exact hi
  have hx' : (gens[k]!)[i]'hlt' < n := by
    rw [← getElem!_pos (gens[k]!) i hlt']; exact hx
  rw [hget]
  unfold ap
  rw [getElem!_pos ((gens[k]!).map UInt32.ofNat) i hlt, Array.getElem_map,
    getElem!_pos (gens[k]!) i hlt', UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
  exact lt_trans hx' hn

theorem tablesOK_spec {n : ℕ} {gens : Array (Array ℕ)} (h : tablesOK n gens = true) :
    n < 2 ^ 32 ∧ (∀ k < gens.size, gens[k]!.size = n ∧ ∀ i < n, (gens[k]!)[i]! < n) ∧
      ∀ k < gens.size, ∀ i j, i < n → j < n → (gens[k]!)[i]! = (gens[k]!)[j]! → i = j := by
  unfold tablesOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hn, hgens⟩, hinv⟩ := h
  rw [Array.all_eq_true] at hgens
  rw [Array.all_eq_true] at hinv
  have hspec : ∀ k < gens.size, gens[k]!.size = n ∧ ∀ i < n, (gens[k]!)[i]! < n := by
    intro k hk
    have hk' := hgens k hk
    rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at hk'
    obtain ⟨hs, hb⟩ := hk'
    have hkp : gens[k]! = gens[k] := getElem!_pos gens k hk
    refine ⟨by rw [hkp]; exact hs, fun i hi => ?_⟩
    have hi' : i < (gens[k]).size := by rw [hs]; exact hi
    have hb' : (gens[k])[i]'hi' < n := of_decide_eq_true (hb i hi')
    rwa [hkp, getElem!_pos (gens[k]) i hi']
  refine ⟨hn, hspec, ?_⟩
  intro k hk i j hi hj heq
  have hkT : k < (toTables gens).size := by
    unfold toTables
    rw [Array.size_map]
    exact hk
  have hT : (toTables gens)[k]! = (toTables gens)[k] := getElem!_pos (toTables gens) k hkT
  have hinv' := hinv k hkT
  rw [← hT] at hinv'
  unfold invOK at hinv'
  rw [allIn_eq_true] at hinv'
  simp only [beq_iff_eq] at hinv'
  have e1 := ap_toTables hn hspec hk hi
  have e2 := ap_toTables hn hspec hk hj
  have hai : ap ((toTables gens)[k]!) i = ap ((toTables gens)[k]!) j := by rw [e1, e2]; exact heq
  calc i = ap (invT n ((toTables gens)[k]!)) (ap ((toTables gens)[k]!) i) :=
        (hinv' i (Nat.zero_le _) hi).symm
    _ = ap (invT n ((toTables gens)[k]!)) (ap ((toTables gens)[k]!) j) := by rw [hai]
    _ = j := hinv' j (Nat.zero_le _) hj

theorem rigidOKAt_spec {n : ℕ} {gens : Array (Array ℕ)} {R : ℕ → ℕ → ℕ}
    {trees : List CFSG.Perm.Native.Tree} (h : rigidOKAt n gens R trees = true) :
    tablesOK n gens = true ∧
      (∀ T ∈ trees, CFSG.Perm.Native.treeOK n (ap T.pts 0) T (toTables gens)
        (Array.range gens.size) = true) ∧
      (∀ v < n, ∃ T ∈ trees, inTree T v = true) ∧
      (trees.map fun T => T.pts.size).sum = n ∧
      (trees.map fun T => T.pts.size).Nodup ∧
      allSections (trees.map (candList (toTables gens))) (fun cs =>
        cs == trees.map (fun T => ap T.pts 0) ||
          !preservesR n R (Array.ofFn (n := n) fun v => combined (toTables gens) trees cs v.val))
        = true := by
  simp only [rigidOKAt] at h
  simp only [Bool.and_eq_true, and_assoc] at h
  refine ⟨h.1, ?_, ?_, ?_, ?_, h.2.2.2.2.2⟩
  · simpa only [List.all_eq_true] using h.2.1
  · have hc := (allIn_eq_true.1 h.2.2.1)
    intro v hv
    simpa only [List.any_eq_true] using hc v (Nat.zero_le v) hv
  · simpa only [beq_iff_eq] using h.2.2.2.1
  · simpa only [decide_eq_true_eq] using h.2.2.2.2.1

theorem preservesR_of_forall {n : ℕ} {R : ℕ → ℕ → ℕ} {f : ℕ → ℕ}
    (hf : ∀ a b, a < n → b < n → R (f a) (f b) = R a b) :
    preservesR n R (Array.ofFn (n := n) fun v => f v.val) = true := by
  unfold preservesR
  rw [allIn_eq_true]
  intro a _ ha
  dsimp only
  rw [allIn_eq_true]
  intro b _ hb
  rw [beq_iff_eq, ofFn_getElem! ha, ofFn_getElem! hb]
  exact hf a b ha hb

end Native

section Core

variable {n : ℕ} {G : Type*} [Group G] [MulAction G (Fin n)]

theorem rep_toTables {gens : Array (Array ℕ)} (hn : n < 2 ^ 32)
    (hg : ∀ k < gens.size, gens[k]!.size = n ∧ ∀ i < n, (gens[k]!)[i]! < n) (lG : ℕ → G)
    (hrep : ∀ k < gens.size, ∀ i : Fin n, (gens[k]!)[i.val]! = ((lG k • i : Fin n) : ℕ)) :
    ∀ l ∈ Array.range gens.size, Rep n (toTables gens)[l]! (lG l) := by
  intro l hl
  rw [Array.mem_range] at hl
  unfold CFSG.Sporadic.Th.Rep
  intro i hi
  rw [ap_toTables hn hg hl hi, hrep l hl ⟨i, hi⟩, idx_of_lt (lG l) hi]

theorem idx_perm_comm (π : Equiv.Perm (Fin n)) {g : G} (hg : ∀ y, π (g • y) = g • π y)
    (x : ℕ) : idx n g (idx n π x) = idx n π (idx n g x) := by
  by_cases hx : x < n
  · set y : Fin n := ⟨x, hx⟩ with hy
    have hπx : idx n π x = (π • y).val := by
      rw [hy, idx_of_lt π hx]
    have hgx : idx n g x = (g • y).val := by
      rw [hy, idx_of_lt g hx]
    rw [hπx, hgx, idx_of_lt g (π • y).isLt, idx_of_lt π (g • y).isLt]
    have e : g • (π • y) = π • (g • y) := by
      rw [Equiv.Perm.smul_def, Equiv.Perm.smul_def]
      exact (hg y).symm
    simpa using congrArg Fin.val e
  · simp only [idx_of_not_lt π hx, idx_of_not_lt g hx]

theorem comm_of_gens {lv : Array ℕ} {lG : ℕ → G} (π : Equiv.Perm (Fin n))
    (hπ : ∀ l ∈ lv, ∀ y, π (lG l • y) = lG l • π y) :
    ∀ g ∈ lettersGroup lv lG, ∀ y, π (g • y) = g • π y := by
  intro g hg
  unfold lettersGroup at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact hπ l hl
  | one => intro y; rw [one_smul, one_smul]
  | mul x y hx hy ihx ihy =>
      intro z
      rw [mul_smul, ihx, ihy, mul_smul]
  | inv x hx ihx =>
      intro z
      rw [eq_inv_smul_iff, ← ihx (x⁻¹ • z), smul_inv_smul]

theorem propagate_eq {T : CFSG.Perm.Native.Tree} {lv : Array ℕ} {lG : ℕ → G} {r : ℕ}
    {letters : Array Table} (hT : TreeFacts n T lv lG r)
    (hrep : ∀ l ∈ lv, Rep n letters[l]! (lG l)) {c : ℕ} (hc : c < n) :
    ∀ k < T.pts.size, propagate T letters c k = idx n (treeG T lG k) c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [propagate.eq_def, treeG.eq_def]
    split_ifs with hg
    · rw [ih (ap T.par k) hg.2 (lt_trans hg.2 hk),
        hrep _ (hT.par k hk hg.1).2 _ (idx_lt _ hc), idx_mul]
    · rw [idx_one]

theorem propagate_perm {T : CFSG.Perm.Native.Tree} {lv : Array ℕ} {lG : ℕ → G} {r : ℕ}
    {letters : Array Table} (hT : TreeFacts n T lv lG r)
    (hrep : ∀ l ∈ lv, Rep n letters[l]! (lG l)) (π : Equiv.Perm (Fin n))
    (hπ : ∀ g ∈ lettersGroup lv lG, ∀ y, π (g • y) = g • π y) :
    ∀ k < T.pts.size, propagate T letters (idx n π r) k = idx n π (ap T.pts k) := by
  intro k hk
  rw [propagate_eq hT hrep (idx_lt π hT.r_lt) k hk,
    idx_perm_comm π (hπ (treeG T lG k) (hT.treeG_mem hk)) r, hT.elt k hk]

theorem treeFacts_of_rigidOKAt {gens : Array (Array ℕ)} {R : ℕ → ℕ → ℕ}
    {trees : List CFSG.Perm.Native.Tree} (lG : ℕ → G)
    (hrep : ∀ k < gens.size, ∀ i : Fin n, (gens[k]!)[i.val]! = ((lG k • i : Fin n) : ℕ))
    (h : rigidOKAt n gens R trees = true) :
    (∀ l ∈ Array.range gens.size, Rep n (toTables gens)[l]! (lG l)) ∧
      ∀ T ∈ trees, TreeFacts n T (Array.range gens.size) lG (ap T.pts 0) := by
  obtain ⟨htab, htree, -⟩ := rigidOKAt_spec h
  obtain ⟨hn, hg, -⟩ := tablesOK_spec htab
  have hreps := rep_toTables hn hg lG hrep
  exact ⟨hreps, fun T hT => treeOK_facts hreps (htree T hT)⟩

theorem mem_orbit_of_card_eq {trees : List CFSG.Perm.Native.Tree} {lv : Array ℕ} {lG : ℕ → G}
    (hT : ∀ T ∈ trees, TreeFacts n T lv lG (ap T.pts 0))
    (hcov : ∀ v < n, ∃ T ∈ trees, inTree T v = true)
    (hnd : (trees.map fun T => T.pts.size).Nodup) (y z : Fin n)
    (h : Nat.card (MulAction.orbit (lettersGroup lv lG) y) =
      Nat.card (MulAction.orbit (lettersGroup lv lG) z)) :
    z ∈ MulAction.orbit (lettersGroup lv lG) y := by
  have key : ∀ y : Fin n, ∃ T ∈ trees, ∃ hr : ap T.pts 0 < n,
      MulAction.orbit (lettersGroup lv lG) y =
        MulAction.orbit (lettersGroup lv lG) (⟨ap T.pts 0, hr⟩ : Fin n) ∧
      Nat.card (MulAction.orbit (lettersGroup lv lG) y) = T.pts.size := by
    intro y
    obtain ⟨T, hTm, hin⟩ := hcov y.val y.isLt
    obtain ⟨k, hk, hkp⟩ := inTree_spec hin
    have hy : y ∈ MulAction.orbit (lettersGroup lv lG)
        (⟨ap T.pts 0, (hT T hTm).r_lt⟩ : Fin n) := ((hT T hTm).mem_orbit_iff y).2 ⟨k, hk, hkp⟩
    have he := MulAction.orbit_eq_iff.2 hy
    exact ⟨T, hTm, (hT T hTm).r_lt, he, by rw [he]; exact (hT T hTm).card_orbit⟩
  obtain ⟨T, hTm, hr, hey, hcy⟩ := key y
  obtain ⟨T', hTm', hr', hez, hcz⟩ := key z
  have hsz : T.pts.size = T'.pts.size := by rw [← hcy, ← hcz, h]
  have hTT : T = T' := List.inj_on_of_nodup_map hnd hTm hTm' hsz
  subst hTT
  rw [hey, ← hez]
  exact MulAction.mem_orbit_self z

theorem rigidOKAt_mem_orbit {gens : Array (Array ℕ)} {R : ℕ → ℕ → ℕ}
    {trees : List CFSG.Perm.Native.Tree} (lG : ℕ → G)
    (hrep : ∀ k < gens.size, ∀ i : Fin n, (gens[k]!)[i.val]! = ((lG k • i : Fin n) : ℕ))
    (h : rigidOKAt n gens R trees = true) (π : Equiv.Perm (Fin n))
    (hπ : ∀ k < gens.size, ∀ y, π (lG k • y) = lG k • π y) (y : Fin n) :
    π y ∈ MulAction.orbit (lettersGroup (Array.range gens.size) lG) y := by
  obtain ⟨-, hTF⟩ := treeFacts_of_rigidOKAt lG hrep h
  obtain ⟨-, -, hcov, -, hnd, -⟩ := rigidOKAt_spec h
  have hπ' : ∀ l ∈ Array.range gens.size, ∀ y, π (lG l • y) = lG l • π y := fun l hl =>
    hπ l (Array.mem_range.1 hl)
  exact perm_mem_orbit_of_card_orbit (H := lettersGroup (Array.range gens.size) lG)
    (mem_orbit_of_card_eq hTF hcov hnd) π (fun g z => comm_of_gens π hπ' g.1 g.2 z) y

theorem rigidOKAt_sound_of_smul {gens : Array (Array ℕ)} {R : ℕ → ℕ → ℕ}
    {trees : List CFSG.Perm.Native.Tree} (lG : ℕ → G)
    (hrep : ∀ k < gens.size, ∀ i : Fin n, (gens[k]!)[i.val]! = ((lG k • i : Fin n) : ℕ))
    (h : rigidOKAt n gens R trees = true) (π : Equiv.Perm (Fin n))
    (hπ : ∀ k < gens.size, ∀ y, π (lG k • y) = lG k • π y)
    (hR : ∀ a b : Fin n, R (π a : ℕ) (π b : ℕ) = R a b) : π = 1 := by
  obtain ⟨hreps, hTF⟩ := treeFacts_of_rigidOKAt lG hrep h
  obtain ⟨-, -, hcov, -, -, hsec⟩ := rigidOKAt_spec h
  have hπ' : ∀ l ∈ Array.range gens.size, ∀ y, π (lG l • y) = lG l • π y := fun l hl =>
    hπ l (Array.mem_range.1 hl)
  have hπK := comm_of_gens π hπ'
  have hlsz : (toTables gens).size = gens.size := by simp [toTables]
  let g : CFSG.Perm.Native.Tree → ℕ := fun T => idx n π (ap T.pts 0)
  have hprop : ∀ T ∈ trees, ∀ k < T.pts.size,
      propagate T (toTables gens) (g T) k = idx n π (ap T.pts k) := fun T hT =>
    propagate_perm (hTF T hT) hreps π hπK
  have hrepl : ∀ l < gens.size, ∀ x < n, ap (toTables gens)[l]! x = idx n (lG l) x :=
    fun l hl x hx => hreps l (Array.mem_range.2 hl) x hx
  have hcand : ∀ T ∈ trees, g T ∈ candList (toTables gens) T := by
    intro T hT
    have hTf := hTF T hT
    rw [mem_candList_iff]
    refine ⟨?_, candOK_of_forall ?_ ?_⟩
    · obtain ⟨k, hk, hkp⟩ := (hTf.mem_orbit_iff _).1
        (rigidOKAt_mem_orbit lG hrep h π hπ ⟨ap T.pts 0, hTf.r_lt⟩)
      exact ⟨k, hk, by rw [hkp]; exact (idx_of_lt π hTf.r_lt).symm⟩
    · intro k hk l hl
      rw [hlsz] at hl
      rw [hrepl l hl _ (hTf.pts_lt k hk)]
      exact (hTf.closed k hk l (Array.mem_range.2 hl)).1
    · intro k hk l hl
      rw [hlsz] at hl
      have hx := hTf.pts_lt k hk
      have hcl := hTf.closed k hk l (Array.mem_range.2 hl)
      rw [hrepl l hl _ hx, hprop T hT _ hcl.1, hcl.2, hprop T hT k hk,
        hrepl l hl _ (idx_lt π hx)]
      exact (idx_perm_comm π (hπ l hl) (ap T.pts k)).symm
  have hres := allSections_spec hsec (trees.map g)
    (forall₂_map_mem (f := g) (F := candList (toTables gens)) (xs := trees) hcand)
  have hcomb : ∀ v < n, combined (toTables gens) trees (trees.map g) v = idx n π v := by
    intro v hv
    refine combined_eq (φ := idx n π) (g := g) ?_ (hcov v hv)
    intro T hT w hw
    obtain ⟨k, hk, hkw⟩ := inTree_spec hw
    have hpos : ap T.pos w = k := by rw [← hkw]; exact (hTF T hT).pos_pts k hk
    rw [hpos, hprop T hT k hk, hkw]
  have hpres := preservesR_of_forall (n := n) (R := R)
    (f := combined (toTables gens) trees (trees.map g)) fun a b ha hb => by
      rw [hcomb a ha, hcomb b hb, idx_of_lt π ha, idx_of_lt π hb]
      exact hR ⟨a, ha⟩ ⟨b, hb⟩
  simp only [hpres, Bool.not_true, Bool.or_false, beq_iff_eq] at hres
  have hfix : ∀ T ∈ trees, idx n π (ap T.pts 0) = ap T.pts 0 := fun T hT =>
    List.map_inj_left.1 hres T hT
  ext y
  obtain ⟨T, hT, hin⟩ := hcov y.val y.isLt
  obtain ⟨k, hk, hky⟩ := inTree_spec hin
  have hTf := hTF T hT
  have e1 : idx n π (ap T.pts k) = ap T.pts k := by
    rw [← hTf.elt k hk, ← idx_perm_comm π (hπK _ (hTf.treeG_mem hk)) _, hfix T hT]
  have hy : idx n π y.val = y.val := by rw [← hky]; exact e1
  rw [Equiv.Perm.one_apply]
  exact (idx_of_lt π y.isLt).symm.trans hy

end Core

section Sound

variable {n : ℕ} {gens : Array (Array ℕ)} {R : ℕ → ℕ → ℕ}

theorem rigidOKAt_of_rigidOK (h : rigidOK n gens R = true) :
    rigidOKAt n gens R (orbitTrees n (toTables gens)) = true := by
  simp only [rigidOK, Bool.and_eq_true] at h
  exact h.2

theorem rigidOK_sound_of_smul {G : Type*} [Group G] [MulAction G (Fin n)] (lG : ℕ → G)
    (hrep : ∀ k < gens.size, ∀ i : Fin n, (gens[k]!)[i.val]! = ((lG k • i : Fin n) : ℕ))
    (h : rigidOK n gens R = true) (π : Equiv.Perm (Fin n))
    (hπ : ∀ k < gens.size, ∀ y, π (lG k • y) = lG k • π y)
    (hR : ∀ a b : Fin n, R (π a : ℕ) (π b : ℕ) = R a b) : π = 1 :=
  rigidOKAt_sound_of_smul lG hrep (rigidOKAt_of_rigidOK h) π hπ hR

theorem rigidOK_exists_smul_eq_of_smul {G : Type*} [Group G] [MulAction G (Fin n)] (lG : ℕ → G)
    (hrep : ∀ k < gens.size, ∀ i : Fin n, (gens[k]!)[i.val]! = ((lG k • i : Fin n) : ℕ))
    (h : rigidOK n gens R = true) (H : Subgroup G) (hH : ∀ k < gens.size, lG k ∈ H)
    (π : Equiv.Perm (Fin n)) (hπ : ∀ k < gens.size, ∀ y, π (lG k • y) = lG k • π y)
    (y : Fin n) : ∃ g ∈ H, π y = g • y := by
  obtain ⟨⟨g, hg⟩, hgy⟩ :=
    rigidOKAt_mem_orbit lG hrep (rigidOKAt_of_rigidOK h) π hπ y
  have hle : lettersGroup (Array.range gens.size) lG ≤ H :=
    (Subgroup.closure_le H).2 (by rintro _ ⟨l, hl, rfl⟩; exact hH l (Array.mem_range.1 hl))
  exact ⟨g, hle hg, hgy.symm⟩

theorem eq_refl_of_rigidOK {Q : Type*} [Group Q] [MulAction Q (Fin n)]
    [MulAction.IsPretransitive Q (Fin n)] (x₀ : Fin n) (H : Subgroup Q)
    (hH : H ≤ MulAction.stabilizer Q x₀) (lG : ℕ → Q) (hlG : ∀ k < gens.size, lG k ∈ H)
    (hrep : ∀ k < gens.size, ∀ i : Fin n, (gens[k]!)[i.val]! = ((lG k • i : Fin n) : ℕ))
    (hR : ∀ (q : Q) (a b : Fin n), R ((q • a : Fin n) : ℕ) ((q • b : Fin n) : ℕ) = R a b)
    (h : rigidOK n gens R = true)
    (hker : ∀ q : Q, (∀ y : Fin n, q • y = y) → q ∈ Subgroup.center Q)
    (hgen : MulAction.stabilizer Q x₀ ⊔ commutator Q = ⊤)
    (β : Q ≃* Q) (hβ : ∀ d ∈ MulAction.stabilizer Q x₀, β d = d) : β = MulEquiv.refl Q :=
  eq_refl_of_rigid_action x₀ H hH (fun a b => R a.val b.val) hR
    (fun π hπ y => rigidOK_exists_smul_eq_of_smul lG hrep h H hlG π
      (fun k hk z => hπ (lG k) (hlG k hk) z) y)
    (fun π _ hπ hπR => rigidOK_sound_of_smul lG hrep h π
      (fun k hk z => hπ (lG k) (hlG k hk) z) hπR)
    hker hgen β hβ

end Sound

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid

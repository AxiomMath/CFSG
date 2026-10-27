module

public import CFSG.Certificates.Kernel.SporLatDcWords
public import CFSG.Certificates.Kernel.SporLatDcLists

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

private theorem dc_check_parts :
    globalOK P.C P.D = true ∧
    (List.range P.D.npc).all (ptChunk P.C P.D) = true ∧
    (List.range P.D.obase.length).all (orbOKS P.C P.D P.s) = true ∧
    (List.range P.D.Rc.length).all (chunkOK P.C P.D) = true := by
  have h := P.h
  unfold dcCheckS at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem global_parts :
    (P.C.Δ.all fun p => Nat.blt p P.C.n) = true ∧
    P.C.Δ.Pairwise (· < ·) ∧ Nat.ble P.C.ng P.C.ns = true ∧
    ((List.range P.C.ns).all fun i => labF (P.C.L (Nat.add 2 i)) P.C.Δ == P.C.Δ) = true ∧
    (P.D.sep.all fun p => Nat.blt p P.C.n) = true ∧
    Nat.beq P.D.osz.length P.D.obase.length = true ∧
    Nat.beq P.D.K.length P.D.obase.length = true ∧
    Nat.blt 0 P.D.mw.length = true ∧
    (P.D.mw.getD 0 [[0]] == []) = true ∧
    (P.D.mw.all fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) = true ∧
    Nat.blt 0 P.D.Rc.length = true ∧ Nat.blt 0 P.D.csz = true ∧
    Nat.beq P.D.msum.length P.D.Rc.length = true ∧
    Nat.beq (sumN P.D.msum) P.C.N = true ∧ refOK P.D P.D.c0 = true ∧
    ((refR P.D P.D.c0).w == []) = true ∧
    Nat.ble P.C.n (Nat.mul P.D.npc P.D.pcz) = true ∧
    (P.D.joins.map (fun e => (e.1, e.2.1)) == pairsL P.D.mw.length) = true ∧
    (P.D.joins.all (joinOK P.C P.D)) = true := by
  have h := (dc_check_parts P).1
  unfold globalOK at h
  repeat rw [Bool.and_assoc] at h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

theorem delta_lt {p : ℕ} (hp : p ∈ P.C.Δ) : p < n := by
  have h := (List.all_eq_true.mp (global_parts P).1) p hp
  rw [Nat.blt_eq] at h
  rw [← P.hn]
  exact h

theorem delta_pair : P.C.Δ.Pairwise (· < ·) := (global_parts P).2.1

theorem ng_le_ns : P.C.ng ≤ P.C.ns := by
  have h := (global_parts P).2.2.1
  rw [Nat.ble_eq] at h
  exact h

theorem sep_lt {p : ℕ} (hp : p ∈ P.D.sep) : p < n := by
  have h := (List.all_eq_true.mp (global_parts P).2.2.2.2.1) p hp
  rw [Nat.blt_eq] at h
  rw [← P.hn]
  exact h

private theorem osz_length : P.D.osz.length = P.D.obase.length := by
  have h := (global_parts P).2.2.2.2.2.1
  rw [Nat.beq_eq] at h
  exact h

private theorem K_length : P.D.K.length = P.D.obase.length := by
  have h := (global_parts P).2.2.2.2.2.2.1
  rw [Nat.beq_eq] at h
  exact h

theorem mw_length_pos : 0 < P.D.mw.length := by
  have h := (global_parts P).2.2.2.2.2.2.2.1
  rw [Nat.blt_eq] at h
  exact h

theorem mw_zero : P.D.mw.getD 0 [] = [] := by
  have h : P.D.mw.getD 0 [[0]] = [] := by
    have h := (global_parts P).2.2.2.2.2.2.2.2.1
    simpa using h
  rw [List.getD_eq_getElem?_getD] at h ⊢
  rw [List.getElem?_eq_getElem (by have := mw_length_pos P; omega)] at h ⊢
  simpa using h

private theorem Rc_pos : 0 < P.D.Rc.length := by
  have h := (global_parts P).2.2.2.2.2.2.2.2.2.2.1
  rw [Nat.blt_eq] at h
  exact h

private theorem csz_pos : 0 < P.D.csz := by
  have h := (global_parts P).2.2.2.2.2.2.2.2.2.2.2.1
  rw [Nat.blt_eq] at h
  exact h

theorem msum_length : P.D.msum.length = P.D.Rc.length := by
  have h := (global_parts P).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [Nat.beq_eq] at h
  exact h

theorem sum_msum : sumN P.D.msum = P.C.N := by
  have h := (global_parts P).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [Nat.beq_eq] at h
  exact h

private theorem n_le : P.C.n ≤ P.D.npc * P.D.pcz := by
  have h := (global_parts P).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [Nat.ble_eq] at h
  exact h

theorem joins_pairs : P.D.joins.map (fun e => (e.1, e.2.1)) = pairsL P.D.mw.length := by
  have h := (global_parts P).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simpa using h

theorem joins_ok : ∀ e ∈ P.D.joins, joinOK P.C P.D e = true := by
  have h := (global_parts P).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [List.all_eq_true] at h
  exact h

theorem sLet_fixes {i : ℕ} (hi : i < P.C.ns) :
    labF (P.C.L (Nat.add 2 i)) P.C.Δ = P.C.Δ := by
  have h := (global_parts P).2.2.2.1
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_range.mpr hi)
  simpa using h1

private theorem ptChunk_of_lt {i : ℕ} (hi : i < P.D.npc) : ptChunk P.C P.D i = true := by
  have h := (dc_check_parts P).2.1
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

theorem chunkOK_of_lt {i : ℕ} (hi : i < P.D.Rc.length) : chunkOK P.C P.D i = true := by
  have h := (dc_check_parts P).2.2.2
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

theorem orbOK_of_lt {j : ℕ} (hj : j < P.D.obase.length) : orbOKS P.C P.D P.s j = true := by
  have h := (dc_check_parts P).2.2.1
  rw [List.all_eq_true] at h
  exact h j (List.mem_range.mpr hj)

theorem obase_lt {j : ℕ} (hj : j < P.D.obase.length) : P.D.obase.getD j 0 < n := by
  have h := orbOK_of_lt P hj
  unfold orbOKS at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  have h1 := h.1.1.1
  rw [Nat.blt_eq] at h1
  have h2 := P.hn
  omega

theorem obase_oid {j : ℕ} (hj : j < P.D.obase.length) : oid P.D (P.D.obase.getD j 0) = j := by
  have h := orbOK_of_lt P hj
  unfold orbOKS at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  have h1 := h.1.1.2
  rw [Nat.beq_eq] at h1
  exact h1

theorem osz_eq_cntB {j : ℕ} (hj : j < P.D.obase.length) :
    P.D.osz.getD j 0 = cntB (fun p => Nat.beq (oid P.D p) j) (List.range n) := by
  have h := orbOK_of_lt P hj
  unfold orbOKS at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  have h1 := h.2
  rw [Nat.beq_eq] at h1
  rw [P.hn] at h1
  exact h1.symm

theorem osz_pos {j : ℕ} (hj : j < P.D.obase.length) : 0 < P.D.osz.getD j 0 := by
  rw [osz_eq_cntB P hj, cntB_eq_length_filter]
  have hmem : P.D.obase.getD j 0 ∈
      List.filter (fun p => Nat.beq (oid P.D p) j) (List.range n) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (obase_lt P hj), ?_⟩
    rw [obase_oid P hj]
    exact Nat.beq_refl j
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)

private theorem chunk0_pos : 0 < (P.D.Rc.getD 0 []).length := by
  have hch := chunkOK_of_lt P (Rc_pos P)
  unfold chunkOK at hch
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hch
  have hB : Nat.blt 0 (P.D.Rc.getD 0 []).length = true := hch.1.1.1.2
  rw [Nat.blt_eq] at hB
  exact hB

private theorem getD_mem_of_lt {α : Type} [Inhabited α] {l : List α} {i : ℕ} (h : i < l.length) :
    l.getD i default ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp

private theorem mem_refR_zero : refR P.D 0 ∈ P.D.Rc.getD 0 [] := by
  have hpos := chunk0_pos P
  have h0 : Nat.div 0 P.D.csz = 0 := Nat.zero_div _
  have h1 : Nat.mod 0 P.D.csz = 0 := Nat.zero_mod _
  unfold refR
  rw [h0, h1]
  exact getD_mem_of_lt hpos

private theorem obase_pos : 0 < P.D.obase.length := by
  have hch := chunkOK_of_lt P (Rc_pos P)
  unfold chunkOK at hch
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hch
  have hrep := (List.all_eq_true.mp hch.1.1.1.1) _ (mem_refR_zero P)
  unfold repOK at hrep
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hrep
  have horb := hrep.1.2
  unfold orbR at horb
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at horb
  have h1 : Nat.blt (Rep.j (refR P.D 0)) P.D.obase.length = true := horb.1.1.1.1.1
  rw [Nat.blt_eq] at h1
  omega

private theorem n_pos (hj : 0 < P.D.obase.length) : 0 < n := by
  have h := orbOK_of_lt P hj
  unfold orbOKS at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  have h1 : Nat.blt (P.D.obase.getD 0 0) P.C.n = true := h.1.1.1
  rw [Nat.blt_eq] at h1
  have h2 := P.hn
  omega

private theorem pcz_pos (hn : 0 < n) : 0 < P.D.pcz := by
  rcases Nat.eq_zero_or_pos P.D.pcz with h | h
  · have h1 := n_le P
    rw [h, Nat.mul_zero] at h1
    have h3 := P.hn
    omega
  · exact h

private theorem npc_pos (hn : 0 < n) : 0 < P.D.npc := by
  rcases Nat.eq_zero_or_pos P.D.npc with h | h
  · have h1 := n_le P
    rw [h, Nat.zero_mul] at h1
    have h3 := P.hn
    omega
  · exact h

private theorem ptOK_of_lt {p : ℕ} (hp : p < n) : ptOK P.C P.D p = true := by
  have hmem : p ∈ List.range' ((p / P.D.pcz) * P.D.pcz) P.D.pcz := by
    rw [List.mem_range']
    exact ⟨p % P.D.pcz, Nat.mod_lt p (pcz_pos P (n_pos P (obase_pos P))), by
      rw [Nat.one_mul, Nat.mul_comm (p / P.D.pcz) P.D.pcz]
      exact (Nat.div_add_mod p P.D.pcz).symm⟩
  have hi : p / P.D.pcz < P.D.npc := by
    rw [Nat.div_lt_iff_lt_mul (pcz_pos P (n_pos P (obase_pos P)))]
    have h := n_le P
    have h2 := P.hn
    omega
  have h := ptChunk_of_lt P hi
  unfold ptChunk at h
  rw [List.all_eq_true] at h
  have h2 := h p hmem
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · have hp' : p < P.C.n := by rw [P.hn]; exact hp
    have h3 : ¬ (p < P.C.n) := by
      rw [← Nat.blt_eq]
      exact Bool.eq_false_iff.mp (by simpa using h2)
    exact absurd hp' h3
  · exact h2

private theorem ptOK_parts {p : ℕ} (hp : p < n) :
    oid P.D p < P.D.obase.length ∧
    (∀ i < P.C.ng, oid P.D (P.C.L (Nat.add 2 i) p) = oid P.D p) ∧
    (tl P.D p < P.C.ns → dp P.D (P.C.L (Nat.add 2 (tl P.D p)) p) + 1 = dp P.D p) ∧
    (¬ tl P.D p < P.C.ns → P.D.obase.getD (oid P.D p) 0 = p) := by
  have h := ptOK_of_lt P hp
  unfold ptOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.blt_eq] at h
    exact h.1.1
  · intro i hi
    have h1 := h.1.2
    rw [List.all_eq_true] at h1
    have h2 := h1 i (List.mem_range.mpr hi)
    rw [Nat.beq_eq] at h2
    exact h2
  · intro hlt
    have hb : Nat.blt (tl P.D p) P.C.ns = true := by rwa [Nat.blt_eq]
    have h1 := h.2
    rw [hb, cond_true, Nat.beq_eq] at h1
    exact h1
  · intro hlt
    have hb : Nat.blt (tl P.D p) P.C.ns = false := by
      rw [Bool.eq_false_iff]
      show ¬ ((tl P.D p).blt P.C.ns = true)
      rw [Nat.blt_eq]
      exact hlt
    have h1 := h.2
    rw [hb, cond_false, Nat.beq_eq] at h1
    exact h1

theorem ptOK_oid_lt {p : ℕ} (hp : p < n) : oid P.D p < P.D.obase.length :=
  (ptOK_parts P hp).1

private theorem ptOK_gen {p i : ℕ} (hp : p < n) (hi : i < P.C.ng) :
    oid P.D (P.C.L (Nat.add 2 i) p) = oid P.D p :=
  (ptOK_parts P hp).2.1 i hi

private theorem ptOK_tree {p : ℕ} (hp : p < n) (hlt : tl P.D p < P.C.ns) :
    dp P.D (P.C.L (Nat.add 2 (tl P.D p)) p) + 1 = dp P.D p :=
  (ptOK_parts P hp).2.2.1 hlt

private theorem ptOK_base {p : ℕ} (hp : p < n) (hlt : ¬ tl P.D p < P.C.ns) :
    P.D.obase.getD (oid P.D p) 0 = p :=
  (ptOK_parts P hp).2.2.2 hlt

private def oidFix : Subgroup Γ where
  carrier := {g | ∀ p < n, oid P.D (act n g p) = oid P.D p}
  one_mem' := by intro p hp; rw [act_one hp]
  mul_mem' := by
    intro g h hg hh p hp
    rw [act_mul g h hp, hg _ (act_lt h hp), hh p hp]
  inv_mem' := by
    intro g hg p hp
    have h1 := hg (act n g⁻¹ p) (act_lt g⁻¹ hp)
    rw [← act_mul g g⁻¹ hp, mul_inv_cancel, act_one hp] at h1
    exact h1.symm

private theorem S_le_oidFix : P.S ≤ P.oidFix := by
  change Subgroup.closure {x | x ∈ P.sl.take P.C.ng} ≤ P.oidFix
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  have hng := ng_le_ns P
  have hi_ng : i < P.C.ng := by
    have h1 : i < (P.sl.take P.C.ng).length := hi
    have h2 : (P.sl.take P.C.ng).length ≤ P.C.ng := by
      rw [List.length_take]
      exact Nat.min_le_left ..
    omega
  have hx' : x = P.sl.getD i 1 := by
    rw [← hxi, List.getElem_take, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [P.hsl]; omega)]
    rfl
  intro p hp
  have h1 : act n x p = P.C.L (Nat.add 2 i) p := by
    rw [hx']
    have e : P.sl.getD i 1 = P.els.getD (Nat.add 2 i) 1 := by
      have h2 : Nat.add 2 i - 2 = i := Nat.add_sub_cancel_left 2 i
      rw [P.els_getD_sl (l := Nat.add 2 i) (Nat.le_add_right 2 i), h2]
    rw [e, P.act_letter (l := Nat.add 2 i) (Nat.add_lt_add_left (hi_ng.trans_le hng) 2) hp]
  rw [h1]
  exact ptOK_gen P hp hi_ng

theorem oid_inv {s : Γ} (hs : s ∈ P.S) {p : ℕ} (hp : p < n) :
    oid P.D (act n s p) = oid P.D p :=
  S_le_oidFix P hs p hp

private theorem sl_getD_mem_S {i : ℕ} (hi : i < P.C.ns) : P.sl.getD i 1 ∈ P.S := by
  apply P.hS
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [P.hsl]; exact hi)]
  simp only [Option.getD_some]
  exact List.mem_iff_getElem.mpr ⟨i, by rw [P.hsl]; exact hi, rfl⟩

theorem reach_base : ∀ d : ℕ, ∀ p : ℕ, p < n → dp P.D p = d →
    ∃ s ∈ P.S, act n s (P.D.obase.getD (oid P.D p) 0) = p := by
  intro d
  induction d with
  | zero =>
    intro p hp hdp
    rcases Nat.lt_or_ge (tl P.D p) P.C.ns with hlt | hge
    · have ht := ptOK_tree P hp hlt
      omega
    · have hb := ptOK_base P hp (by omega)
      exact ⟨1, P.S.one_mem, by rw [hb, act_one hp]⟩
  | succ d ih =>
    intro p hp hdp
    rcases Nat.lt_or_ge (tl P.D p) P.C.ns with hlt | hge
    · have ht := ptOK_tree P hp hlt
      have hqdp : dp P.D (P.C.L (Nat.add 2 (tl P.D p)) p) = d := by omega
      have hqn : P.C.L (Nat.add 2 (tl P.D p)) p < n :=
        P.letter_lt (Nat.add_lt_add_left hlt 2) hp
      obtain ⟨s, hs, hsp⟩ := ih _ hqn hqdp
      have hgS : P.sl.getD (tl P.D p) 1 ∈ P.S := sl_getD_mem_S P (by omega)
      have hgq : act n (P.sl.getD (tl P.D p) 1) p = P.C.L (Nat.add 2 (tl P.D p)) p := by
        have h2 : Nat.add 2 (tl P.D p) - 2 = tl P.D p := Nat.add_sub_cancel_left 2 _
        have e : P.sl.getD (tl P.D p) 1 = P.els.getD (Nat.add 2 (tl P.D p)) 1 := by
          rw [P.els_getD_sl (l := Nat.add 2 (tl P.D p)) (Nat.le_add_right 2 _), h2]
        rw [e, P.act_letter (l := Nat.add 2 (tl P.D p))
          (Nat.add_lt_add_left hlt 2) hp]
      have hoid : oid P.D (P.C.L (Nat.add 2 (tl P.D p)) p) = oid P.D p := by
        rw [← hgq]
        exact oid_inv P hgS hp
      have hbase_lt : P.D.obase.getD (oid P.D p) 0 < n :=
        obase_lt P (ptOK_oid_lt P hp)
      rw [hoid] at hsp
      refine ⟨(P.sl.getD (tl P.D p) 1)⁻¹ * s, P.S.mul_mem (P.S.inv_mem hgS) hs, ?_⟩
      rw [act_mul _ _ hbase_lt, hsp, ← hgq, ← act_mul _ _ hp, inv_mul_cancel, act_one hp]
    · have hb := ptOK_base P hp (by omega)
      exact ⟨1, P.S.one_mem, by rw [hb, act_one hp]⟩

private theorem card_filter_fin_eq_length_filter {n : ℕ} (f : ℕ → ℕ) (j : ℕ) :
    (Finset.univ.filter (fun p : Fin n => f p.val = j)).card
      = ((List.range n).filter (fun p => Nat.beq (f p) j)).length := by
  have himage : (Finset.univ.filter (fun p : Fin n => f p.val = j)).image Fin.val
      = ((List.range n).filter (fun p => Nat.beq (f p) j)).toFinset := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.isLt, by rw [hp]; exact Nat.beq_refl j⟩
    · rintro ⟨hqn, hq⟩
      have hq' : f q = j := by
        rw [← Nat.beq_eq]
        exact hq
      exact ⟨⟨q, hqn⟩, hq', rfl⟩
  calc (Finset.univ.filter (fun p : Fin n => f p.val = j)).card
      = ((Finset.univ.filter (fun p : Fin n => f p.val = j)).image Fin.val).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = (((List.range n).filter (fun p => Nat.beq (f p) j)).toFinset).card := by rw [himage]
    _ = _ := List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range)

private theorem fibre_eq_orbit {j : ℕ} (hj : j < P.D.obase.length) :
    (Finset.univ.filter (fun p : Fin n => oid P.D p.val = j) : Set (Fin n)) =
      MulAction.orbit P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n) := by
  ext p
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hpj
    rw [MulAction.mem_orbit_iff]
    obtain ⟨s, hs, hsp⟩ := reach_base P (dp P.D p.val) p.val p.isLt rfl
    refine ⟨Subtype.mk s hs, ?_⟩
    apply Fin.ext
    rw [hpj] at hsp
    rw [← act_eq]
    exact hsp
  · intro hp
    rw [MulAction.mem_orbit_iff] at hp
    obtain ⟨s, hs⟩ := hp
    have h1 : act n (s : Γ) (P.D.obase.getD j 0) = p.val := by
      have h2 := congrArg Fin.val hs
      rwa [← act_eq] at h2
    rw [← h1, oid_inv P s.2 (obase_lt P hj), obase_oid P hj]

private theorem osz_eq_natCard {j : ℕ} (hj : j < P.D.obase.length) :
    P.D.osz.getD j 0 = Nat.card {p : Fin n // oid P.D p.val = j} := by
  have h1 : ((List.range n).filter (fun p => Nat.beq (oid P.D p) j)).length
      = (Finset.univ.filter (fun p : Fin n => oid P.D p.val = j)).card :=
    (card_filter_fin_eq_length_filter (n := n) (fun p => oid P.D p) j).symm
  rw [osz_eq_cntB P hj, cntB_eq_length_filter, h1, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

private theorem osz_eq_card {j : ℕ} (hj : j < P.D.obase.length) :
    P.D.osz.getD j 0 =
      Nat.card (MulAction.orbit P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) := by
  rw [osz_eq_natCard P hj]
  refine (Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl (Fin n)) ?_)).symm
  intro p
  rw [← fibre_eq_orbit P hj]
  simp [Finset.mem_filter]

theorem S_card : Nat.card P.S = P.s := P.hk

theorem osz_mul_stab {j : ℕ} (hj : j < P.D.obase.length) :
    P.D.osz.getD j 0 *
        Nat.card (MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) =
      Nat.card P.S := by
  haveI : Fintype P.S := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.orbit P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) :=
    Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer P.S (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)) :=
    Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group P.S
    (⟨P.D.obase.getD j 0, obase_lt P hj⟩ : Fin n)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  rw [osz_eq_card P hj]
  exact h

end DcSoundCtx

end CFSG.KC.SLDc

end

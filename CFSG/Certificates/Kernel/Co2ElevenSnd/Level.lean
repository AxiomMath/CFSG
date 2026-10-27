module

public import CFSG.Certificates.Kernel.Co2ElevenSnd.Tree
import CFSG.Certificates.Kernel.Co2ElevenSnd.Replay
public import CFSG.Certificates.Kernel.Spor.PK.Congr

public section

namespace CFSG.KC.Co2Eleven.Snd

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.PK CFSG.KS.TW CFSG.KC.Co2Eleven
  CFSG.KC.Co2SmithS

theorem levelK_facts {LC : Nat → Nat} {NL : Nat} {bs : List Nat} {R : Nat → Nat} {i N : Nat}
    (h : levelK LC NL bs R i N = true) :
    0 < N ∧ N ≤ 2300 ∧ rf R i 4 N = N ∧
      (∀ k < N, orbRecK (fun j x => ap12 (LC ((lvK LC NL bs i).getD j 0)) x)
          (lvK LC NL bs i).length N (bs.getD i 0) (rf R i 0) (rf R i 1) (rf R i 6) (rf R i 4)
          (rf R i 5) (fun k j => rf R i (8 + j) k) k = true ∧
        rf R i 2 k = (if k = 0 then 0 else (lvK LC NL bs i).getD (rf R i 6 k) 0) ∧
        rf R i 3 (rf R i 0 k) = k) ∧
      ∀ x < 2300, rf R i 3 x = 4095 ∨ (rf R i 3 x < N ∧ rf R i 0 (rf R i 3 x) = x) := by
  unfold levelK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, fun k hk => ⟨(h4 k hk).1.1, (h4 k hk).1.2, (h4 k hk).2⟩, h5⟩

theorem lvK_eq (LC : Nat → Nat) (NL : Nat) (bs : List Nat) :
    ∀ i, lvK LC NL bs i = lvAt (fun l x => ap12 (LC l) x) NL bs i
  | 0 => rfl
  | i + 1 => by
    show (lvK LC NL bs i).filter _ = (lvAt _ NL bs i).filter _
    rw [lvK_eq LC NL bs i]
    apply List.filter_congr
    intro l _
    rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

theorem lvK_lt {LC : Nat → Nat} {NL : Nat} {bs : List Nat} {i : Nat} :
    ∀ l ∈ lvK LC NL bs i, l < NL := by
  intro l hl
  rw [lvK_eq] at hl
  exact lvAt_sub _ _ _ _ l hl

theorem rf_lt (R : Nat → Nat) (i t x : Nat) : rf R i t x < 4096 := by
  have h : rf R i t x = R (64 * i + t) / 2 ^ (12 * x) % 2 ^ 12 := pg_eq 12 _ _
  rw [h]
  have := Nat.mod_lt (R (64 * i + t) / 2 ^ (12 * x)) (Nat.two_pow_pos 12)
  simpa using this

theorem level_run {LC : Nat → Nat} {NL : Nat} {bs : List Nat} {R : Nat → Nat} {i N : Nat}
    {F : Nat → Nat → Nat}
    (hF : ∀ l ∈ lvK LC NL bs i, ∀ x < 2300, F l x = ap12 (LC l) x ∧ ap12 (LC l) x < 2300)
    (hr : bs.getD i 0 < 2300) (h : levelK LC NL bs R i N = true) :
    BS.run F (lvK LC NL bs i) 2300 (bs.getD i 0) =
      ⟨(List.range N).map (rf R i 0), (List.range N).map (rf R i 1),
        (List.range N).map (rf R i 2)⟩ := by
  obtain ⟨hN, hNn, hlast, hk, -⟩ := levelK_facts h
  rw [run_congr (G := fun l x => ap12 (LC l) x) hr
    (fun l hl x hx => by rw [(hF l hl x hx).1]; exact (hF l hl x hx).2)
    (fun l hl x hx => (hF l hl x hx).1)]
  refine run_of_rec (LA := rf R i 6) (M := rf R i 4) (S := rf R i 5)
    (TB := fun k j => rf R i (8 + j) k) hN hNn (fun k hk' => (hk k hk').1) hlast ?_
    (fun k hk' => (hk k hk').2.1)
  intro a ha b hb e
  have h1 := (hk a ha).2.2
  have h2 := (hk b hb).2.2
  rw [e] at h1
  omega

private theorem getD_map_range (g : Nat → Nat) {N k : Nat} (hk : k < N) :
    ((List.range N).map g).getD k 0 = g k := by
  simp [List.getD_eq_getElem?_getD, hk]

private theorem lt_of_mem_map_rf {R : Nat → Nat} {i t N l : Nat}
    (hl : l ∈ (List.range N).map (rf R i t)) : l < 2 ^ 32 := by
  rw [List.mem_map] at hl
  obtain ⟨a, -, rfl⟩ := hl
  exact Nat.lt_trans (rf_lt R i t a) (by decide)

private theorem idxOf_map_range {T : Nat → Nat} {N a : Nat} (ha : a < N)
    (hinj : ∀ b < N, T b = T a → b = a) : ((List.range N).map T).idxOf (T a) = a := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.idxOf_append]
    by_cases haN : a < N
    · have hm : T a ∈ (List.range N).map T := List.mem_map.2 ⟨a, List.mem_range.2 haN, rfl⟩
      rw [if_pos hm]
      exact ih haN fun b hb e => hinj b (by omega) e
    · have haN' : a = N := by omega
      subst haN'
      have hm : T a ∉ (List.range a).map T := by
        rw [List.mem_map]
        rintro ⟨b, hb, e⟩
        have := hinj b (by have := List.mem_range.1 hb; omega) e
        have := List.mem_range.1 hb
        omega
      rw [if_neg hm, List.length_map, List.length_range, List.map_singleton, List.idxOf_cons_self,
        Nat.zero_add]

theorem treeRec_of {LC : Nat → Nat} {NL : Nat} {bs : List Nat} {R : Nat → Nat} {i N : Nat}
    {letters : Array Table} (hNL : NL % 2 = 0) (hTR : ∀ l < NL, TR 2300 letters[l]! (ap12 (LC l)))
    (hr : bs.getD i 0 < 2300) (h : levelK LC NL bs R i N = true) :
    TreeRec (treeOf 2300 (BS.run (tabF letters) (lvK LC NL bs i) 2300 (bs.getD i 0)))
      letters LC R i N := by
  obtain ⟨hN, hNn, -, hk, hpos⟩ := levelK_facts h
  have hF : ∀ l ∈ lvK LC NL bs i, ∀ x < 2300,
      tabF letters l x = ap12 (LC l) x ∧ ap12 (LC l) x < 2300 :=
    fun l hl x hx => (hTR l (lvK_lt l hl)).2 x hx
  have hok := run_ok (n := 2300) (F := tabF letters) (lv := lvK LC NL bs i)
    (fun l hl x hx => by rw [(hF l hl x hx).1]; exact (hF l hl x hx).2) hr
  rw [level_run hF hr h] at hok ⊢
  have hinj : ∀ b < N, ∀ a < N, rf R i 0 b = rf R i 0 a → b = a := by
    intro b hb a ha e
    have h1 := (hk a ha).2.2
    have h2 := (hk b hb).2.2
    rw [e] at h2
    omega
  have hmem : ∀ x, x ∈ (List.range N).map (rf R i 0) → rf R i 3 x < N ∧
      ap (treeOf 2300 ⟨(List.range N).map (rf R i 0), (List.range N).map (rf R i 1),
        (List.range N).map (rf R i 2)⟩).pos x = rf R i 3 x := by
    intro x hx
    have hx' := hx
    rw [List.mem_map] at hx'
    obtain ⟨a, ha, rfl⟩ := hx'
    have ha' := List.mem_range.1 ha
    rw [(hk a ha').2.2, treeOf_ap_pos_mem (by simp; omega) (hok.lt _ hx) hx]
    exact ⟨ha', idxOf_map_range ha' fun b hb e => hinj b hb a ha' e⟩
  have hnmem : ∀ x < 2300, x ∉ (List.range N).map (rf R i 0) → ¬ rf R i 3 x < N := by
    intro x hx hm hlt
    rcases hpos x hx with e | ⟨-, e⟩
    · omega
    · exact hm (List.mem_map.2 ⟨rf R i 3 x, List.mem_range.2 hlt, e⟩)
  refine ⟨by rw [treeOf_size]; simp, hNn, fun x hx => ?_, fun x hx hlt => ?_, fun k hk' => ?_,
    fun k hk' => ?_, fun k hk' hk0 _ => ?_⟩
  · by_cases hm : x ∈ (List.range N).map (rf R i 0)
    · obtain ⟨h1, h2⟩ := hmem x hm
      rw [h2]
    · rw [treeOf_ap_pos_nmem hx hm]
      have := hnmem x hx hm
      constructor
      · intro h'
        omega
      · intro h'
        exact absurd h' this
  · by_cases hm : x ∈ (List.range N).map (rf R i 0)
    · exact (hmem x hm).2
    · exact absurd hlt (hnmem x hx hm)
  · rw [treeOf_ap_par (fun l hl => lt_of_mem_map_rf hl)]
    exact getD_map_range _ hk'
  · rw [treeOf_ap_lab (fun l hl => lt_of_mem_map_rf hl)]
    exact getD_map_range _ hk'
  · have hlab := hok.lab_mem k hk0 (by simpa using hk')
    simp only [getD_map_range _ hk'] at hlab
    have hlt := lvK_lt _ hlab
    have hinv : CFSG.KC.Co2Eleven.invL (rf R i 2 k) < NL := by
      unfold CFSG.KC.Co2Eleven.invL
      split <;> omega
    exact hTR _ hinv

theorem treeOK_of_level {LC : Nat → Nat} {NL : Nat} {bs : List Nat} {R : Nat → Nat} {i N : Nat}
    {letters : Array Table} (hTR : ∀ l < NL, TR 2300 letters[l]! (ap12 (LC l)))
    (hr : bs.getD i 0 < 2300) (h : levelK LC NL bs R i N = true) :
    CFSG.Perm.Native.treeOK 2300 (bs.getD i 0)
      (treeOf 2300 (BS.run (tabF letters) (lvK LC NL bs i) 2300 (bs.getD i 0))) letters
      (lvK LC NL bs i).toArray = true := by
  have hF : ∀ l ∈ lvK LC NL bs i, ∀ x < 2300,
      tabF letters l x = ap12 (LC l) x ∧ ap12 (LC l) x < 2300 :=
    fun l hl x hx => (hTR l (lvK_lt l hl)).2 x hx
  have hF' : ∀ l ∈ lvK LC NL bs i, ∀ x < 2300, tabF letters l x < 2300 :=
    fun l hl x hx => by rw [(hF l hl x hx).1]; exact (hF l hl x hx).2
  refine treeOK_of_run (by decide) (run_ok hF' hr) (run_closed hF' hr) ?_
  rw [level_run hF hr h]
  exact fun l hl => lt_of_mem_map_rf hl

end CFSG.KC.Co2Eleven.Snd

end

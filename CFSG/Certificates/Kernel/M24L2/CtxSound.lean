
module

public import CFSG.Certificates.Kernel.M24L2.BfsSound
public import CFSG.CGT.M24R.L2EnumBase

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R

private def lBFSG {α : Type} (N F : Nat) (key : Table → Nat) (lets : List α) (lt : α → Table)
    (X0 : Table) : Array (Option (List α)) := Id.run do
  let mut arr : Array (Option (List α)) := Array.replicate N none
  arr := arr.set! (key X0) (some [])
  let mut queue : Array (Table × List α) := #[(X0, [])]
  let mut i := 0
  for _ in [0:F] do
    if i < queue.size then
      let (X, w) := queue[i]!
      i := i + 1
      for l in lets do
        let Y := compT 16 X (lt l)
        let m := key Y
        if (arr[m]!).isNone then
          arr := arr.set! m (some (w ++ [l]))
          queue := queue.push (Y, w ++ [l])
  return arr

private theorem lBFS_G :
    lBFS () = lBFSG 65536 65536 (fun Y => codeOf Y / 16) xLetters letTab (idT 16) := rfl

private theorem lBFSG_eq {α : Type} (N F : Nat) (key : Table → Nat) (lets : List α)
    (lt : α → Table) (X0 : Table) : lBFSG N F key lets lt X0 = (bfsG N F key lets lt X0).1 := rfl

theorem lBFS_eq : lBFS () =
    (bfsG 65536 65536 (fun Y => codeOf Y / 16) xLetters letTab (idT 16)).1 :=
  lBFS_G.trans (lBFSG_eq _ _ _ _ _ _)

@[expose] noncomputable def keyL (c : Nat) : Nat := Nat.shiftRight c (nat_lit 4)

theorem keyL_eq (c : Nat) : keyL c = c / 16 := Nat.shiftRight_eq_div_pow c 4

@[expose] noncomputable def lTwin : BS (Fin 10 × Bool) := bfsT 65536 keyL lcC xLetters idC

theorem idC_lt : idC < 2 ^ 20 := by decide

theorem lBFS_twin :
    (lBFS ()).size = 65536 ∧ (∀ k < 65536, (lBFS ())[k]! = look keyL k lTwin.all.reverse) ∧
    (∀ e ∈ lTwin.all, Good lcC xLetters idC e) := by
  have h := bfsG_twin (α := Fin 10 × Bool) (N := 65536) (key := fun Y => codeOf Y / 16) (lets := xLetters)
    (lt := letTab) (lc := lcC) (keyN := keyL) (c0 := idC) 65536 letTab_tabC
    (fun c hc => by rw [codeOf_tabC hc, keyL_eq]) (fun c hc => by rw [keyL_eq]; omega) idC_lt
  rw [lBFS_eq, idT_tabC]
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.2⟩

theorem lcC_lin : ∀ l ∈ xLetters, lcC l % 16 = 0 := by
  decide +kernel

theorem mulC_mod16 (a b : Nat) : mulC a b % 16 = aff a (b % 16) := by
  rw [mulC_eq]
  have := aff_lt a (b % 16)
  omega

theorem aff_zero_lin {a : Nat} (ha : a % 16 = 0) : aff a 0 = 0 := by
  rw [aff_eq, ha, lap_zero]
  rfl

theorem foldl_lin (w : List (Fin 10 × Bool)) (hw : ∀ l ∈ w, l ∈ xLetters) :
    ∀ c, c % 16 = 0 → (w.foldl (fun c l => mulC c (lcC l)) c) % 16 = 0 := by
  induction w with
  | nil => intro c hc; exact hc
  | cons l w ih =>
    intro c hc
    rw [List.foldl_cons]
    refine ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ ?_
    rw [mulC_mod16, lcC_lin l (hw l List.mem_cons_self), aff_zero_lin hc]

theorem look_some {keyN : Nat → Nat} {k : Nat} {L : List (Nat × List (Fin 10 × Bool))}
    {w : List (Fin 10 × Bool)} (h : look keyN k L = some w) :
    ∃ e ∈ L, keyN e.1 = k ∧ e.2 = w := by
  unfold look at h
  rcases hf : L.find? (fun e => keyN e.1 == k) with _ | e
  · rw [hf] at h
    simp at h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨e, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

theorem ld_word {k : Nat} (hk : k < 65536) {w : List (Fin 10 × Bool)}
    (h : (lBFS ())[k]! = some w) : cwK w = 16 * k := by
  rw [lBFS_twin.2.1 k hk] at h
  obtain ⟨e, he, hkey, hw⟩ := look_some h
  rw [List.mem_reverse] at he
  obtain ⟨_, he1, hl⟩ := lBFS_twin.2.2 e he
  rw [hw] at he1 hl
  have h16 : cwK w % 16 = 0 := by rw [cwK_eq]; exact foldl_lin w hl idC (by decide)
  rw [keyL_eq, he1, ← cwK_eq] at hkey
  omega

@[expose] def ReachL (L : List Nat) : Prop :=
  ∀ k < 65536, ((lBFS ())[k]!).isSome = L.contains k

@[expose] noncomputable def tabK (L : List Nat) (c : Nat) : Nat :=
  if L.contains (c / 16) = true then c else c % 16 + 541200

theorem lap_id : ∀ x < 16, lap 33825 x = x := by decide +kernel

theorem mulC_trans {v m : Nat} (hv : v < 16) (hm : m < 65536) :
    mulC (v + 541200) (16 * m) = v + 16 * m := by
  rw [mulC_eq, aff_eq, show (16 * m) % 16 = 0 by omega, lap_zero, show (16 * m) / 16 = m by omega,
    show (v + 541200) / 16 = 33825 by omega, show (v + 541200) % 16 = v by omega,
    lap_id _ (nib_lt m 0), lap_id _ (nib_lt m 1), lap_id _ (nib_lt m 2), lap_id _ (nib_lt m 3),
    Nat.xor_zero]
  simp only [nib_eq]
  norm_num
  omega

theorem mulC_trans_id {v : Nat} (hv : v < 16) : mulC (v + 541200) idC = v + 541200 := by
  have h := mulC_trans hv (show 33825 < 65536 by norm_num)
  exact h

theorem ttC_eq : ∀ v < 16, cwK (tw v) = v + 541200 := by decide +kernel

theorem ctx_tt' {v : Nat} (hv : v < 16) : (mkCtx ()).tt[v]! = tabC (v + 541200) := by
  rw [ctx_tt hv, wTab_tabC, ttC_eq v hv]

theorem filter_length (p : Nat → Bool) : ∀ n : Nat,
    ((List.range (16 * n)).filter fun c => p (c / 16)).length =
      16 * ((List.range n).filter p).length
  | 0 => rfl
  | n + 1 => by
    rw [show 16 * (n + 1) = 16 * n + 16 by ring, List.range_add, List.filter_append,
      List.length_append, filter_length p n, List.range_succ (n := n), List.filter_append,
      List.length_append]
    have hblk : ((List.range 16).map (16 * n + ·)).filter (fun c => p (c / 16)) =
        if p n then (List.range 16).map (16 * n + ·) else [] := by
      have hd : ∀ i ∈ List.range 16, (16 * n + i) / 16 = n := by
        intro i hi
        rw [List.mem_range] at hi
        omega
      split
      · rw [List.filter_eq_self]
        intro c hc
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
        rw [hd i hi]
        assumption
      · rw [List.filter_eq_nil_iff]
        intro c hc
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
        rw [hd i hi]
        simpa using ‹¬p n = true›
    rw [hblk]
    split
    · simp [*]
      ring
    · simp [*]

section Reach

variable {L : List Nat} (hR : ReachL L)
include hR

theorem ctx_ld_size : (mkCtx ()).ld.size = 65536 := lBFS_twin.1

theorem ctx_lt' {k : Nat} (hk : k < 65536) :
    (mkCtx ()).lt[k]! = tabC (if L.contains k = true then 16 * k else idC) := by
  have hs : (mkCtx ()).ld.size = 65536 := lBFS_twin.1
  change ((lBFS ()).map fun o => wTab (o.getD []))[k]! = _
  rw [getElem!_map_of_lt _ _ (by rw [lBFS_twin.1]; exact hk)]
  have hr := hR k hk
  rcases h : (lBFS ())[k]! with _ | w
  · rw [h] at hr
    simp only [Option.isSome_none] at hr
    rw [← hr]
    simp only [Option.getD_none, Bool.false_eq_true, ↓reduceIte]
    rw [wTab_tabC]
    rfl
  · rw [h] at hr
    simp only [Option.isSome_some] at hr
    rw [← hr]
    simp only [Option.getD_some, ↓reduceIte]
    rw [wTab_tabC, ld_word hk h]

theorem tab_eq {c : Nat} (hc : c < 2 ^ 20) : (mkCtx ()).tab c = tabC (tabK L c) := by
  unfold Ctx8.tab tabK
  rw [ctx_tt' (Nat.mod_lt c (by norm_num)), ctx_lt' hR (by omega), compT_tabC]
  split
  · rw [mulC_trans (Nat.mod_lt c (by norm_num)) (by omega)]
    congr 1
    omega
  · rw [mulC_trans_id (Nat.mod_lt c (by norm_num))]

theorem valid_eq {c : Nat} (hc : c < 2 ^ 20) : (mkCtx ()).valid c = L.contains (c / 16) :=
  hR (c / 16) (by omega)

theorem mem_codes_iff {c : Nat} : c ∈ (mkCtx ()).codes ↔ c < 2 ^ 20 ∧ L.contains (c / 16) = true := by
  rw [Ctx8.codes, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← valid_eq hR h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [valid_eq hR h1]; exact h2⟩

theorem tab_of_mem {c : Nat} (hc : c ∈ (mkCtx ()).codes) : (mkCtx ()).tab c = tabC c := by
  obtain ⟨h1, h2⟩ := (mem_codes_iff hR).1 hc
  rw [tab_eq hR h1, tabK, if_pos h2]

theorem forall_codes {P : Nat → Prop} (hL : ∀ m ∈ L, m < 65536)
    (h : ∀ m ∈ L, ∀ v < 16, P (v + 16 * m)) : ∀ c ∈ (mkCtx ()).codes, P c := by
  intro c hc
  obtain ⟨h1, h2⟩ := (mem_codes_iff hR).1 hc
  have := h (c / 16) (List.contains_iff_mem.1 h2) (c % 16) (Nat.mod_lt c (by norm_num))
  rwa [Nat.mod_add_div] at this

theorem codes_length (hnd : L.Nodup) (hL : ∀ m ∈ L, m < 65536) (hlen : L.length = 20160) :
    (mkCtx ()).codes.length = 322560 := by
  have h1 : (mkCtx ()).codes = (List.range (16 * 65536)).filter fun c => L.contains (c / 16) := by
    rw [Ctx8.codes]
    apply List.filter_congr
    intro c hc
    rw [List.mem_range] at hc
    exact valid_eq hR hc
  rw [h1, filter_length]
  have h2 : ((List.range 65536).filter fun m => L.contains m).length = L.length := by
    apply List.Perm.length_eq
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd]
    intro m
    simp only [List.mem_filter, List.mem_range, List.contains_iff_mem]
    exact ⟨fun h => h.2, fun h => ⟨hL m h, h⟩⟩
  rw [h2, hlen]

theorem ctxCheck_of (hnd : L.Nodup) (hL : ∀ m ∈ L, m < 65536) (hlen : L.length = 20160) :
    ctxCheck (mkCtx ()) = true := by
  unfold ctxCheck
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨ctx_ld_size hR, codes_length hR hnd hL hlen⟩, fun c hc => ?_⟩
  rw [tab_of_mem hR hc, codeOf_tabC ((mem_codes_iff hR).1 hc).1]

end Reach

end CFSG.KC.M24L2

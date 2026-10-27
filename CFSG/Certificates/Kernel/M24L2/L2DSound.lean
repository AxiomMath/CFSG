
module

public import CFSG.Certificates.Kernel.M24L2.L2FbSound
public import Certificates.Data.Kernel.M24L2.D

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R CFSG.KC.Enum

theorem dT_eq (i : Fin 3) : dT i = tabC (dC i) := wTab_tabC _

theorem thT_eq (i : Fin 3) : thT i = tabC (thC i) := wTab_tabC _

theorem bList_eq : bList = [idC, b0C, b1C, b01C].map tabC := by
  unfold bList
  rw [idT_tabC, b0T_eq, b1T_eq, b01T_eq]
  simp only [List.map_cons, List.map_nil]

theorem normB_tabC (x : Nat) : normB (tabC x) = normBK x := by
  unfold normB normBK
  rw [bList_eq, b0T_eq, b1T_eq, normK_tabC]

theorem evT_foldl (u : Fin 3 → Nat) (w : List (Fin 3)) : ∀ c : Nat,
    w.foldl (fun X k => compT 16 X (tabC (u k))) (tabC c) =
      tabC (w.foldl (fun c k => mulC c (u k)) c) := by
  induction w with
  | nil => intro c; rfl
  | cons k w ih =>
    intro c
    rw [List.foldl_cons, List.foldl_cons, compT_tabC, ih]

theorem evT_tabC (u : Fin 3 → Nat) (w : List (Fin 3)) :
    evT (fun k => tabC (u k)) w = tabC (evK u w) := by
  unfold evT evK
  rw [idT_tabC, evT_foldl, foldL_eq]

theorem evK_lt (u : Fin 3 → Nat) (w : List (Fin 3)) : evK u w < 2 ^ 20 := by
  unfold evK
  rw [foldL_eq]
  exact foldl_mulC_lt _ w _ (by decide)

theorem dC_lt (i : Fin 3) : dC i < 2 ^ 20 := cwK_lt _

theorem thC_lt (i : Fin 3) : thC i < 2 ^ 20 := cwK_lt _

theorem evT_dT (w : List (Fin 3)) : evT dT w = tabC (evK dC w) := by
  rw [show dT = fun k => tabC (dC k) from funext dT_eq, evT_tabC]

theorem evT_thT (w : List (Fin 3)) : evT thT w = tabC (evK thC w) := by
  rw [show thT = fun k => tabC (thC k) from funext thT_eq, evT_tabC]

theorem dBFSq_eq : dBFSq () = bfsG 1048576 2048 codeOf (List.finRange 3) dT (idT 16) := rfl

theorem dBFSq_twin :
    (dBFSq ()).2.toList = dTwin.all.reverse.map entT ∧ (dBFSq ()).1.size = 1048576 ∧
    (∀ k < 1048576, (dBFSq ()).1[k]! = look (fun c => c) k dTwin.all.reverse) ∧
    ∀ e ∈ dTwin.all, Good dC (List.finRange 3) idC e := by
  have h := bfsG_twin (α := Fin 3) (N := 1048576) (key := codeOf) (lets := List.finRange 3)
    (lt := dT) (lc := dC) (keyN := fun c => c) (c0 := idC) 2048 dT_eq
    (fun c hc => codeOf_tabC hc) (fun c hc => hc) idC_lt
  rw [dBFSq_eq, idT_tabC]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

theorem thWord_eq (i : Fin 3) : thWord i = thWordK i := by
  unfold thWord thWordK
  rw [codeOf_tabC' (thT_eq i) (thC_lt i), dBFSq_twin.2.2.1 _ (thC_lt i)]
  rfl
where
  codeOf_tabC' {X : Table} {c : Nat} (h : X = tabC c) (hc : c < 2 ^ 20) : codeOf X = c := by
    rw [h, codeOf_tabC hc]

theorem dList_mem {c : Nat} : c ∈ (mkCtx ()).dList ↔
    c ∈ (mkCtx ()).codes ∧ normB ((mkCtx ()).tab c) = true := by
  unfold Ctx8.dList
  rw [List.mem_filter]

theorem dM_spec {m : Nat} (h : dM m = true) : ∀ v < 16, dBody (v + 16 * m) = true := by
  intro v hv
  unfold dM at h
  rcases hl : dLin m with _ | _
  · unfold dBody
    have : (!(commK (v + 16 * m) (dC 0)) || !(commK (v + 16 * m) (dC 1)) ||
        !(commK (v + 16 * m) (dC 2)) || Nat.beq (v + 16 * m) idC) = true := by
      rcases h0 : commK (v + 16 * m) (dC 0) with _ | _
      · rfl
      rcases h1 : commK (v + 16 * m) (dC 1) with _ | _
      · rfl
      rcases h2 : commK (v + 16 * m) (dC 2) with _ | _
      · rfl
      have k0 := commK_lin h0
      have k1 := commK_lin h1
      have k2 := commK_lin h2
      rw [show (v + 16 * m) / 16 = m by omega] at k0 k1 k2
      unfold dLin at hl
      change (commK (16 * m) (16 * (dC 0 >>> 4)) && commK (16 * m) (16 * (dC 1 >>> 4)) &&
        commK (16 * m) (16 * (dC 2 >>> 4))) = false at hl
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
        k0, k1, k2] at hl
      simp at hl
    rw [this]
    cases normBK (v + 16 * m) <;> rfl
  · rw [hl] at h
    change allN 16 _ = true at h
    rw [CFSG.KS.Raw.Orb.allN_iff] at h
    have := h v hv
    rw [letN_eq] at this
    exact this

theorem dCheck_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) (h1 : dPart1K = true)
    (h2 : ∀ m ∈ L, dM m = true) (h3 : dPart3K = true) : dCheck (mkCtx ()) = true := by
  unfold dCheck
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold dPart1K at h1
    rw [← h1]
    refine all_mem_congr fun i _ => ?_
    rw [dT_eq, thT_eq, normB_tabC, normB_tabC]
  · rw [List.all_eq_true]
    intro z hz
    obtain ⟨hzc, hzn⟩ := dList_mem.1 hz
    have hzl := ((mem_codes_iff hR).1 hzc).1
    have hb := forall_codes hR hL (P := fun c => dBody c = true)
      (fun m hm v hv => dM_spec (h2 m hm) v hv) z hzc
    rw [tab_of_mem hR hzc] at hzn ⊢
    rw [normB_tabC] at hzn
    unfold dBody at hb
    rw [hzn] at hb
    rw [dT_eq, dT_eq, dT_eq]
    show (!commT (tabC z) (tabC (dC 0)) || !commT (tabC z) (tabC (dC 1)) ||
      !commT (tabC z) (tabC (dC 2)) || tabC z == idT 16) = true
    rw [commT_tabC', commT_tabC', commT_tabC', idT_tabC, beq_tabC hzl (by decide)]
    exact hb
  · unfold dPart3K at h3
    rw [← h3]
    refine all_mem_congr fun i _ => ?_
    rw [thWord_eq, evT_dT, evT_thT, thT_eq, dT_eq, beq_tabC (evK_lt _ _) (thC_lt i),
      beq_tabC (evK_lt _ _) (dC_lt i)]

end CFSG.KC.M24L2

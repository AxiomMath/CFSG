
module

public import CFSG.Certificates.Kernel.M24L2.CtxSound
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CGT.M24R

theorem code_ext {a b : Nat} (ha : a < 2 ^ 20) (hb : b < 2 ^ 20)
    (h : ∀ x < 16, aff a x = aff b x) : a = b := by
  rw [← codeF_aff ha, ← codeF_aff hb, codeF_eq, codeF_eq, h 0 (by norm_num), h 1 (by norm_num),
    h 2 (by norm_num), h 4 (by norm_num), h 8 (by norm_num)]

theorem mulC_assoc (a b c : Nat) : mulC (mulC a b) c = mulC a (mulC b c) :=
  code_ext (mulC_lt _ _) (mulC_lt _ _) fun x _ => by simp only [aff_mulC]

theorem mulC_idC {a : Nat} (ha : a < 2 ^ 20) : mulC a idC = a :=
  code_ext (mulC_lt _ _) ha fun x hx => by rw [aff_mulC, aff_idC hx]

theorem idC_mulC {a : Nat} (ha : a < 2 ^ 20) : mulC idC a = a :=
  code_ext (mulC_lt _ _) ha fun x _ => by rw [aff_mulC, aff_idC (aff_lt _ _)]

theorem rep_tab {c : Nat} (hc : c < 2 ^ 20) :
    Rep 16 ((mkCtx ()).tab c) (FreeGroup.lift gPerm (FreeGroup.mk ((mkCtx ()).word c))) := by
  have h1 := ctx_tt (Nat.mod_lt c (by norm_num : 0 < 16))
  have h2 : (mkCtx ()).lt[c / 16]! = wTab (((mkCtx ()).ld[c / 16]!).getD []) := by
    change ((lBFS ()).map fun o => wTab (o.getD []))[c / 16]! = _
    exact getElem!_map_of_lt _ _ (by rw [lBFS_twin.1]; omega)
  unfold Ctx8.tab Ctx8.word
  rw [h1, h2, ← FreeGroup.mul_mk, map_mul]
  exact Rep.compT (rep_wTab _) (rep_wTab _)

theorem rep_invRev (w : List (Fin 10 × Bool)) :
    Rep 16 (wTab (FreeGroup.invRev w)) (FreeGroup.lift gPerm (FreeGroup.mk w))⁻¹ := by
  rw [← map_inv, FreeGroup.inv_mk]
  exact rep_wTab _

theorem inv_of_mem {L : List Nat} (hR : ReachL L) {c : Nat} (hc : c ∈ (mkCtx ()).codes) :
    ∃ i, i < 2 ^ 20 ∧ invT 16 (tabC c) = tabC i ∧ mulC c i = idC ∧ mulC i c = idC := by
  have hlt := ((mem_codes_iff hR).1 hc).1
  have hrep := rep_tab hlt
  rw [tab_of_mem hR hc] at hrep
  set w := (mkCtx ()).word c
  have hinv := CFSG.KS.Tbl.invT_rep (by norm_num) hrep
  have heq : invT 16 (tabC c) = tabC (cwK (FreeGroup.invRev w)) := by
    rw [← wTab_tabC]
    exact table_eq_of_rep hinv (rep_invRev w) (CFSG.KS.Tbl.invT_size _ _) (wTab_size _)
  refine ⟨cwK (FreeGroup.invRev w), cwK_lt _, heq, ?_, ?_⟩
  · apply tabC_inj (mulC_lt _ _) (by decide)
    rw [← compT_tabC, ← wTab_tabC, ← idT_tabC]
    exact table_eq_of_rep (by rw [← mul_inv_cancel]; exact hrep.compT (rep_invRev w))
      (Rep.idT (by norm_num)) (compT_size _ _) idT_size
  · apply tabC_inj (mulC_lt _ _) (by decide)
    rw [← compT_tabC, ← wTab_tabC, ← idT_tabC]
    exact table_eq_of_rep (by rw [← inv_mul_cancel]; exact (rep_invRev w).compT hrep)
      (Rep.idT (by norm_num)) (compT_size _ _) idT_size

@[expose] noncomputable def conjKey (n : Nat) (P : Table) : Nat :=
  codeOf (compT 16 (compT 16 (tabC n) P) (invT 16 (tabC n)))

theorem conjKey_eq {L : List Nat} (hR : ReachL L) {n p x : Nat} (hn : n ∈ (mkCtx ()).codes)
    (hp : p < 2 ^ 20) (hx : x < 2 ^ 20) : conjKey n (tabC p) = x ↔ mulC n p = mulC x n := by
  obtain ⟨i, hi, hinv, h1, h2⟩ := inv_of_mem hR hn
  have hnl := ((mem_codes_iff hR).1 hn).1
  unfold conjKey
  rw [hinv, compT_tabC, compT_tabC, codeOf_tabC (mulC_lt _ _)]
  constructor
  · intro h
    rw [← h, mulC_assoc, mulC_assoc, h2, mulC_idC hp]
  · intro h
    rw [h, mulC_assoc, h1, mulC_idC hx]

theorem foldSet_keep {key : Nat → Nat} {k : Nat} : ∀ (vc : List Nat) (A : Array Nat),
    (∀ c ∈ vc, key c ≠ k) → (vc.foldl (fun arr c => arr.set! (key c) c) A)[k]! = A[k]!
  | [], _, _ => rfl
  | c :: vc, A, h => by
    rw [List.foldl_cons, foldSet_keep vc _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')),
      Array.getElem!_set!_ne _ _ _ _ (h c List.mem_cons_self)]

theorem foldSet_get {key : Nat → Nat} {k : Nat} : ∀ (vc : List Nat) (A : Array Nat),
    k < A.size → (∃ c ∈ vc, key c = k) →
      ∃ c ∈ vc, key c = k ∧ (vc.foldl (fun arr c => arr.set! (key c) c) A)[k]! = c
  | [], _, _, ⟨_, hc, _⟩ => absurd hc (by simp)
  | c :: vc, A, hk, hex => by
    rw [List.foldl_cons]
    by_cases h : ∃ c' ∈ vc, key c' = k
    · obtain ⟨c', hc', h1, h2⟩ := foldSet_get vc (A.set! (key c) c) (by rw [Array.size_set!]; exact hk) h
      exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2⟩
    · push Not at h
      obtain ⟨c', hc', h1⟩ := hex
      have hck : key c = k := by
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact h1
        · exact absurd h1 (h c' hc')
      refine ⟨c, List.mem_cons_self, hck, ?_⟩
      rw [foldSet_keep vc _ h, ← hck, Array.getElem!_set!_self _ _ _ (by rw [hck]; exact hk)]

end CFSG.KC.M24L2

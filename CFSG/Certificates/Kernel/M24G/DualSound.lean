module

public import Certificates.Data.Kernel.M24G.Dual
public import CFSG.Certificates.Kernel.M24G.ListsSound

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem sextDualCheck_eq : Native.sextDualCheck () =
    dualCk (Native.sextTrios (Native.trioSexts ()) 0) (fun a => (Native.trioList ())[a]!)
      (Native.octsS (Native.sextList ())[0]!) := by
  simp only [Native.sextDualCheck, dualCk]

theorem sextTrios_trioSexts {q : Nat} (hq : q < Native.nSext) :
    Native.sextTrios (Native.trioSexts ()) q = (List.range Native.nTrio).filter
      fun p => Native.trioIn (Native.trioList ())[p]! (Native.sextList ())[q]! := by
  unfold Native.sextTrios
  refine List.filter_congr fun p hp => ?_
  rw [List.mem_range] at hp
  have e : (Native.trioSexts ())[p]! = (List.range Native.nSext).filter
      fun q => Native.trioIn (Native.trioList ())[p]! (Native.sextList ())[q]! := by
    unfold Native.trioSexts
    simp [hp]
  rw [e]
  simp [hq]

theorem filter_range_eq_of_allIdx {α : Type} [Inhabited α] {L : List α} {n : Nat}
    (hn : L.length = n) {f : α → Bool} {S : List Nat}
    (h : allIdx (fun i x => f x == S.contains i) L 0 = true) (hS : ascL S = true)
    (hsub : ∀ x ∈ S, x < n) :
    (List.range n).filter (fun p => f L.toArray[p]!) = S := by
  subst hn
  rw [allIdx_iff] at h
  have hf : ∀ p < L.length, f L.toArray[p]! = S.contains p := by
    intro p hp
    have := h p hp
    rw [Nat.zero_add, beq_iff_eq] at this
    rw [toArray_getElem!_eq_getD]
    exact this
  have hp : ∀ x < L.length, f L.toArray[x]! = true → x ∈ S := by
    intro x hx hx'
    rw [hf x hx] at hx'
    exact List.contains_iff_mem.1 hx'
  have e := filter_range_perm (ascL_nodup hS) hsub hp
  rw [List.filter_eq_self (l := S).2 fun x hx => by
    rw [hf x (hsub x hx)]
    exact List.contains_iff_mem.2 hx] at e
  refine e.eq_of_pairwise (le := (· < ·)) (fun a b _ _ h₁ h₂ => absurd h₁ (Nat.lt_asymm h₂))
    (List.pairwise_lt_range.filter _) (ascL_pairwise S hS)

theorem mem_of_mem_combs : ∀ (k : Nat) (L : List Nat) {D : List Nat}, D ∈ Native.combs k L →
    ∀ x ∈ D, x ∈ L
  | 0, _, D, hD, x, hx => by
    rw [Native.combs, List.mem_singleton] at hD
    subst hD
    exact absurd hx List.not_mem_nil
  | _ + 1, [], D, hD, _, _ => by
    rw [Native.combs] at hD
    exact absurd hD List.not_mem_nil
  | k + 1, a :: L, D, hD, x, hx => by
    rw [Native.combs, List.mem_append, List.mem_map] at hD
    rcases hD with ⟨D', hD', rfl⟩ | hD
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_combs k L hD' x hx)
    · exact List.mem_cons_of_mem _ (mem_of_mem_combs (k + 1) L hD x hx)

theorem all_congr_mem {β : Type} {l : List β} {p q : β → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h' x hx => h x hx ▸ h' x hx, fun h' x hx => (h x hx).symm ▸ h' x hx⟩

theorem any_congr_mem {β : Type} {l : List β} {p q : β → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, h'⟩ => ⟨x, hx, h x hx ▸ h'⟩, fun ⟨x, hx, h'⟩ => ⟨x, hx, (h x hx).symm ▸ h'⟩⟩

theorem dualCk_congr {LU : List Nat} {tr tr' : Nat → Nat × Nat × Nat}
    (h : ∀ a ∈ LU, tr a = tr' a) (O : List Nat) : dualCk LU tr O = dualCk LU tr' O := by
  have hc : ∀ k D, D ∈ Native.combs k LU → ∀ x ∈ D, tr x = tr' x :=
    fun k D hD x hx => h x (mem_of_mem_combs k LU hD x hx)
  have hSp : ((Native.combs 5 LU).filter fun D => D.all fun d => D.all fun k =>
        d == k || !(Native.meets (tr d) (tr k))) =
      (Native.combs 5 LU).filter fun D => D.all fun d => D.all fun k =>
        d == k || !(Native.meets (tr' d) (tr' k)) :=
    List.filter_congr fun D hD => all_congr_mem fun d hd => all_congr_mem fun k hk => by
      rw [hc 5 D hD d hd, hc 5 D hD k hk]
  unfold dualCk
  simp only
  rw [hSp]
  congr 1
  · congr 1
    · congr 1
      refine all_congr_mem fun D hD => all_congr_mem fun o _ => ?_
      have hD' := (List.mem_filter.1 hD).1
      have e : D.filter (fun k => (Native.octsT (tr k)).contains o) =
          D.filter (fun k => (Native.octsT (tr' k)).contains o) :=
        List.filter_congr fun k hk => by rw [hc 5 D hD' k hk]
      rw [e]
    · refine all_congr_mem fun c hc' => ?_
      have e₁ : (c.all fun a => c.all fun b => a == b || Native.meets (tr a) (tr b)) =
          c.all fun a => c.all fun b => a == b || Native.meets (tr' a) (tr' b) :=
        all_congr_mem fun a ha => all_congr_mem fun b hb => by
          rw [hc 3 c hc' a ha, hc 3 c hc' b hb]
      have e₂ : (O.any fun o => c.all fun k => (Native.octsT (tr k)).contains o) =
          O.any fun o => c.all fun k => (Native.octsT (tr' k)).contains o :=
        any_congr_mem fun o _ => all_congr_mem fun k hk => by rw [hc 3 c hc' k hk]
      rw [e₁, e₂]
  · exact all_congr_mem fun a ha => all_congr_mem fun b hb => by rw [h a ha, h b hb]

end CFSG.KC.M24G

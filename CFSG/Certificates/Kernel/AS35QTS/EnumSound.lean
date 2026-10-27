module

public import CFSG.Certificates.Kernel.AS35QTS.UnitSound

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd V3 M3 unitB f4s v3s gu3s)

theorem range_flatMap {α : Type} {n : Nat} (hn : 0 < n) (g : Nat → Nat → α) : ∀ m : Nat,
    (List.range m).flatMap (fun i => (List.range n).map (g i)) =
      (List.range (n * m)).map (fun k => g (k / n) (k % n))
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, range_flatMap hn g m, Nat.mul_succ, List.range_add,
      List.map_append, List.flatMap_singleton, List.map_map]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.1 hj
    simp only [Function.comp_apply]
    congr 1
    · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hj', Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj']

theorem e4_congr {x y : Nat} (h : x % 4 = y % 4) : e4 x = e4 y := by
  unfold e4
  simp only [h]

theorem f4s_eq : f4s = (List.range 4).map e4 := rfl

@[expose] def v3d (q : Nat) : V3 := ⟨e4 (q >>> 4), e4 (q >>> 2), e4 q⟩

theorem v3s_eq : v3s = (List.range 64).map v3d := by
  unfold v3s
  rw [f4s_eq]
  simp only [List.flatMap_map, List.map_map]
  have e1 : ∀ a : Nat, (List.range 4).flatMap (fun b => (List.range 4).map
      (fun c => (⟨e4 a, e4 b, e4 c⟩ : V3))) =
      (List.range 16).map (fun k => (⟨e4 a, e4 (k / 4), e4 (k % 4)⟩ : V3)) := fun a =>
    range_flatMap (n := 4) (by norm_num) (fun b c => (⟨e4 a, e4 b, e4 c⟩ : V3)) 4
  simp only [Function.comp_def, e1]
  rw [range_flatMap (n := 16) (by norm_num) (fun a k => (⟨e4 a, e4 (k / 4), e4 (k % 4)⟩ : V3)) 4]
  refine List.map_congr_left fun q _ => ?_
  unfold v3d
  simp only [Nat.shiftRight_eq_div_pow]
  congr 1 <;> exact e4_congr (by omega)

@[expose] def dmN (c : Nat) : M3 := (decN c).m

theorem mats_eq : (v3s.flatMap fun r0 => v3s.flatMap fun r1 => v3s.map fun r2 =>
    (⟨r0, r1, r2⟩ : M3)) = (List.range (2 ^ 18)).map dmN := by
  rw [v3s_eq]
  simp only [List.flatMap_map, List.map_map]
  have e1 : ∀ i : Nat, (List.range 64).flatMap (fun j => (List.range 64).map
      (fun l => (⟨v3d i, v3d j, v3d l⟩ : M3))) =
      (List.range 4096).map (fun k => (⟨v3d i, v3d (k / 64), v3d (k % 64)⟩ : M3)) := fun i =>
    range_flatMap (n := 64) (by norm_num) (fun j l => (⟨v3d i, v3d j, v3d l⟩ : M3)) 64
  simp only [Function.comp_def, e1]
  rw [range_flatMap (n := 4096) (by norm_num)
    (fun i k => (⟨v3d i, v3d (k / 64), v3d (k % 64)⟩ : M3)) 64]
  refine List.map_congr_left fun c _ => ?_
  unfold dmN decN v3d
  simp only [Nat.shiftRight_eq_div_pow]
  congr 2 <;> exact e4_congr (by omega)

theorem incB_go {N : Nat} : ∀ (L : List Nat) (lo : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun c _ ih lo => Bool.and' (Nat.ble lo c) (Bool.and' (Nat.blt c N) (ih (Nat.succ c)))) L lo =
        true →
    (∀ x ∈ L, lo ≤ x ∧ x < N) ∧ L.Pairwise (· < ·)
  | [], _, _ => by simp
  | c :: L, lo, h => by
    change Bool.and' (Nat.ble lo c) (Bool.and' (Nat.blt c N) _) = true at h
    rw [and'_eq, and'_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := incB_go L (Nat.succ c) h3
    refine ⟨fun x hx => ?_, List.Pairwise.cons (fun x hx => ?_) ih2⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨h1, h2⟩
      · have := ih1 x hx
        omega
    · have := ih1 x hx
      omega

theorem eq_of_pairwise_lt : ∀ {l₁ l₂ : List Nat}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) List.not_mem_nil
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with e | ha
      · exact e
      rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with e | hb
      · exact e.symm
      have := h₂.1 a ha
      have := h₁.1 b hb
      omega
    subst hab
    rw [eq_of_pairwise_lt h₁.2 h₂.2 fun x => ?_]
    constructor
    · intro hx
      have hne : x ≠ a := fun e => by have := h₁.1 x hx; omega
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | hx'
      · exact absurd e hne
      · exact hx'
    · intro hx
      have hne : x ≠ a := fun e => by have := h₂.1 x hx; omega
      rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | hx'
      · exact absurd e hne
      · exact hx'

theorem filter_range_eq {L : List Nat} {N : Nat} (p : Nat → Bool) (hinc : incB N L = true)
    (hmem : ∀ c < N, (p c = true ↔ c ∈ L)) : (List.range N).filter p = L := by
  obtain ⟨hb, hs⟩ := incB_go L 0 hinc
  have hs' : ((List.range N).filter p).Pairwise (· < ·) :=
    List.Pairwise.filter _ (List.pairwise_lt_range)
  have hm : ∀ x, x ∈ (List.range N).filter p ↔ x ∈ L := by
    intro x
    rw [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hx, hp⟩
      exact (hmem x hx).1 hp
    · intro hx
      have := (hb x hx).2
      exact ⟨this, (hmem x this).2 hx⟩
  exact eq_of_pairwise_lt hs' hs hm

theorem gu3s_eq {G : List Nat} (h : gOK G = true) : gu3s = G.map dmN := by
  obtain ⟨hinc, hmem⟩ := gOK_spec h
  unfold gu3s
  rw [mats_eq, List.filter_map]
  have e : (2 : Nat) ^ 18 = 262144 := by norm_num
  rw [e]
  exact congrArg (List.map dmN)
    (filter_range_eq (unitB ∘ dmN) hinc fun c hc => hmem c (by rw [e]; exact hc))

@[expose] def zb (k : Nat) : ZMod 2 := if k % 2 = 1 then 1 else 0

theorem zb_eq {c g : Nat} (hc : c < 82944) (hg : g < 2 ^ 18) :
    zb (c / 41472) = if (2 ^ 18 * (c / 648) + g).testBit 24 then 1 else 0 := by
  have h : (2 ^ 18 * (c / 648) + g) / 2 ^ 24 % 2 = c / 41472 % 2 := by omega
  rw [Nat.testBit_eq_decide_div_mod_eq, h]
  unfold zb
  simp

theorem map_getD_range {L : List Nat} {n : Nat} (hL : L.length = n) {β : Type} (f : Nat → β) :
    L.map f = (List.range n).map fun k => f (L.getD k 0) := by
  subst hL
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using h1), Option.getD_some]

theorem codes_eq {G : List Nat} (hG : G.length = 648) (hgu : gu3s = G.map dmN)
    (hGb : ∀ g ∈ G, g < 2 ^ 18) :
    CFSG.LargeExtraspecial.AS35QTS.codes =
      (List.range 82944).map fun c => decN (2 ^ 18 * (c / 648) + G.getD (c % 648) 0) := by
  unfold CFSG.LargeExtraspecial.AS35QTS.codes
  rw [hgu, v3s_eq, map_getD_range hG, show [(0 : ZMod 2), 1] = (List.range 2).map zb from rfl]
  simp only [List.flatMap_map, List.map_map]
  have e1 : ∀ e : ZMod 2, (List.range 64).flatMap (fun q => (List.range 648).map
      (fun k => (⟨e, v3d q, dmN (G.getD k 0)⟩ : Cd))) =
      (List.range 41472).map (fun k => (⟨e, v3d (k / 648), dmN (G.getD (k % 648) 0)⟩ : Cd)) :=
    fun e => range_flatMap (n := 648) (by norm_num)
      (fun q k => (⟨e, v3d q, dmN (G.getD k 0)⟩ : Cd)) 64
  simp only [Function.comp_def, e1]
  rw [range_flatMap (n := 41472) (by norm_num)
    (fun i k => (⟨zb i, v3d (k / 648), dmN (G.getD (k % 648) 0)⟩ : Cd)) 2]
  refine List.map_congr_left fun c hc => ?_
  have hc' := List.mem_range.1 hc
  have hg : G.getD (c % 648) 0 < 2 ^ 18 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : G[c % 648]? with
    | none => simp
    | some g => exact hGb g (List.mem_of_getElem? h)
  have hk : c % 41472 % 648 = c % 648 := by omega
  rw [hk]
  generalize G.getD (c % 648) 0 = g at hg ⊢
  unfold decN dmN decN v3d
  simp only [Nat.shiftRight_eq_div_pow]
  congr 1
  · exact zb_eq (by omega) hg
  · congr 1 <;> exact e4_congr (by omega)
  · congr 2 <;> exact e4_congr (by omega)

end CFSG.KC.AS35QTS

end

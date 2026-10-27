module

public import Certificates.Data.Kernel.M24G.C311
public import CFSG.Certificates.Kernel.M24G.DualSound

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem discsOvals_eq (Ts : Array (List Nat)) (q : Nat) : Native.discsOvals Ts q =
    discsOvalsT (Native.sextTrios Ts q) (fun a => (Native.trioList ())[a]!) := by
  simp only [Native.discsOvals, discsOvalsT]

theorem discsOvalsT_congr {LU : List Nat} {tr tr' : Nat → Nat × Nat × Nat}
    (h : ∀ a ∈ LU, tr a = tr' a) : discsOvalsT LU tr = discsOvalsT LU tr' := by
  unfold discsOvalsT
  simp only
  congr 1
  · exact List.map_congr_left fun d hd => List.filter_congr fun k hk => by
      simp only [h d hd, h k hk]
  · exact List.filter_congr fun D hD => all_congr_mem fun d hd => all_congr_mem fun k hk => by
      simp only [h d (mem_of_mem_combs 5 LU hD d hd), h k (mem_of_mem_combs 5 LU hD k hk)]

theorem mem_of_mem_discsOvalsT {LU : List Nat} {tr : Nat → Nat × Nat × Nat} {D : List Nat}
    (hD : D ∈ discsOvalsT LU tr) : ∀ d ∈ D, d ∈ LU := by
  unfold discsOvalsT at hD
  rcases List.mem_append.1 hD with hD | hD
  · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hD
    exact fun d hd => (List.mem_filter.1 hd).1
  · exact mem_of_mem_combs 5 LU (List.mem_filter.1 hD).1

theorem testBit_foldr_or {β : Type} (f : β → Nat) :
    ∀ (L : List β) (q : Nat), (L.foldr (fun x a => f x ||| a) 0).testBit q = true →
      ∃ x ∈ L, (f x).testBit q = true
  | [], q, h => by simp at h
  | x :: L, q, h => by
    rw [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨x, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, h⟩ := testBit_foldr_or f L q h
      exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem mem_of_testBit_rowMask {r : List Nat} {q : Nat} (h : (rowMask r).testBit q = true) :
    q ∈ r := by
  obtain ⟨x, hx, h⟩ := testBit_foldr_or (fun q => 2 ^ q) r q h
  rw [Nat.testBit_two_pow, decide_eq_true_iff] at h
  exact h ▸ hx

theorem mem_of_lookup {β : Type} :
    ∀ (l : List (Nat × β)) (a : Nat) (b : β), l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (x, y) :: l, a, b, h => by
    cases e : a == x with
    | true =>
      simp only [List.lookup, e, Option.some.injEq] at h
      rw [beq_iff_eq.1 e, ← h]
      exact List.mem_cons_self
    | false =>
      simp only [List.lookup, e] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup l a b h)

theorem getElem!_toArray_of_lt {α : Type} [Inhabited α] {L : List α} {i : Nat}
    (h : i < L.length) : L.toArray[i]! = L[i] := by
  rw [toArray_getElem!_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    Option.getD_some]

set_option exponentiation.threshold 2000 in
theorem stmt311Check_of {TL : List (Nat × Nat × Nat)} {TS : List (List Nat)} {LU : List Nat}
    {TU : List (Nat × Nat × Nat)} {RU DS NB : List (List Nat)} {MS : List Nat}
    (hT : Native.trioList () = TL.toArray) (hTs : Native.trioSexts () = TS.toArray)
    (hTL : TL.length = 3795) (hTSl : TS.length = 3795)
    (hLU : Native.sextTrios TS.toArray 0 = LU)
    (htu : ∀ a ∈ LU, TL.toArray[a]! = tabLU LU TU a)
    (hru : ∀ a ∈ LU, TS.toArray[a]! = tabRow LU RU a)
    (hDS : discsOvalsT LU (tabLU LU TU) = DS) (hlen : DS.length = 21)
    (hA : (TL.zip TS).all (c311A DS (tabRow LU RU) (tabLU LU TU)) = true)
    (hN : nbsOK TS LU NB MS = true)
    (hB : c311B DS (fun d => (tabNM LU NB MS d).2) = true) :
    Native.stmt311Check () = true := by
  have hD : Native.discsOvals TS.toArray 0 = DS := by
    rw [discsOvals_eq, hLU, hT, discsOvalsT_congr htu, hDS]
  have hsub : ∀ D ∈ DS, ∀ d ∈ D, d ∈ LU := fun D hD' => by
    rw [← hDS] at hD'
    exact mem_of_mem_discsOvalsT hD'
  simp only [Native.stmt311Check]
  rw [hTs, hT, hD]
  simp only [Bool.and_eq_true]
  refine ⟨⟨by simp [hlen], ?_⟩, ?_⟩
  · rw [range_all_iff]
    intro l hl
    have h1 : l < TL.length := by rw [hTL]; exact hl
    have h2 : l < TS.length := by rw [hTSl]; exact hl
    have hmem : (TL[l], TS[l]) ∈ TL.zip TS := by
      have hlt : l < (TL.zip TS).length := by simp [h1, h2]
      have := List.getElem_mem hlt
      rwa [List.getElem_zip] at this
    have hx := List.all_eq_true.1 hA _ hmem
    refine Eq.trans ?_ hx
    unfold c311A Native.coplanar
    refine all_congr_mem fun D hD' => any_congr_mem fun d hd => ?_
    simp only [getElem!_toArray_of_lt h1, getElem!_toArray_of_lt h2, hru d (hsub D hD' d hd),
      htu d (hsub D hD' d hd)]
  · rw [range_all_iff]
    intro q hq
    rw [List.all_eq_true]
    intro D hD'
    have hc := beq_iff_eq.1 (List.all_eq_true.1 hB D hD')
    have hq' : (D.foldr (fun d a => (tabNM LU NB MS d).2 ||| a) 0).testBit q = true := by
      rw [hc, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
      exact hq
    obtain ⟨d, hd, hbit⟩ := testBit_foldr_or _ D q hq'
    unfold tabNM at hbit
    cases hl : (LU.zip (NB.zip MS)).lookup d with
    | none => simp [hl] at hbit
    | some NM =>
      rw [hl, Option.getD_some] at hbit
      have hok := List.all_eq_true.1 hN _ (mem_of_lookup _ _ _ hl)
      simp only [nbOK, Bool.and_eq_true, beq_iff_eq] at hok
      rw [← hok.2] at hbit
      obtain ⟨k, hk, hkq⟩ := testBit_foldr_or _ NM.1 q hbit
      have hkq' := mem_of_testBit_rowMask hkq
      have hkd := List.all_eq_true.1 hok.1 k hk
      rw [Bool.and_eq_true, decide_eq_true_iff] at hkd
      refine List.any_eq_true.2 ⟨d, hd, List.any_eq_true.2 ⟨k, ?_, ?_⟩⟩
      · unfold Native.sextTrios
        refine List.mem_filter.2 ⟨List.mem_range.2 hkd.1, ?_⟩
        rw [toArray_getElem!_eq_getD]
        exact List.contains_iff_mem.2 hkq'
      · unfold Native.coplanar
        rw [toArray_getElem!_eq_getD, toArray_getElem!_eq_getD]
        exact hkd.2

end CFSG.KC.M24G

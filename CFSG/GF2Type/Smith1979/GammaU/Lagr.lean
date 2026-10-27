module

public import CFSG.GF2Type.Smith1979.GammaU.SpanList
public import CFSG.GF2Type.Smith1979.GammaU.Group

public section

namespace CFSG.GF2Type.Smith1979.GammaU

open Module

@[expose] def f0b (m n : ℕ) : Bool :=
  (List.range 6).foldl
    (fun acc i => acc ^^ ((m.testBit i && n.testBit (6 + i)) ^^ (m.testBit (6 + i) && n.testBit i)))
    false

theorem prod_term (p q r s : Bool) :
    ((if p then 1 else 0 : ZMod 2) * (if q then 1 else 0) +
        (if r then 1 else 0) * if s then 1 else 0) =
      if ((p && q) ^^ (r && s)) then 1 else 0 := by
  cases p <;> cases q <;> cases r <;> cases s <;> decide

theorem f0_vecOf (m n : ℕ) : f0 (vecOf m) (vecOf n) = if f0b m n then 1 else 0 := by
  simp only [f0, vecOf, Fin.sum_univ_six, f0b, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil, Bool.false_xor, prod_term, ite_add_ite]
  rfl

theorem f0_eq_zero_of_mem {D : Submodule (ZMod 2) V12} (hsing : ∀ x ∈ D, q0 x = 0) {x y : V12}
    (hx : x ∈ D) (hy : y ∈ D) : f0 x y = 0 := by
  rw [← polar_q0, QuadraticMap.polar, hsing _ (D.add_mem hx hy), hsing x hx, hsing y hy, sub_zero,
    sub_zero]

theorem eq_false_of_ite {b : Bool} (h : (if b then 1 else 0 : ZMod 2) = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

@[expose] def lagrCand (a0 : ℕ) : List ℕ :=
  (List.range 4096).filter fun n => n != 0 && n != a0 && !q0b n && !f0b n a0

@[expose] def lagrDFS : ℕ → List ℕ → List ℕ → List (List ℕ)
  | 0, vs, _ => [vs]
  | k + 1, vs, cands =>
    let S := spanList vs
    cands.flatMap fun v =>
      if v ∉ S ∧ ∀ s ∈ S, v ≤ v ^^^ s then
        lagrDFS k (v :: vs) (cands.filter fun w => decide (v < w) && !f0b w v)
      else []

section Complete

variable {D : Submodule (ZMod 2) V12} (hsing : ∀ x ∈ D, q0 x = 0)
  (hdim : finrank (ZMod 2) D = 6)
include hsing hdim

theorem spanOf_le {vs : List ℕ} (hD : ∀ v ∈ vs, vecOf v ∈ D) : spanOf vs ≤ D :=
  Submodule.span_le.2 fun _ ⟨v, hv, hx⟩ => hx ▸ hD v hv

theorem lagr_step : ∀ (k : ℕ) (vs cands : List ℕ), (∀ v ∈ vs, v < 4096) →
    (∀ v ∈ vs, vecOf v ∈ D) → finrank (ZMod 2) (spanOf vs) + k = 6 →
    (∀ n < 4096, vecOf n ∈ D → vecOf n ∉ spanOf vs → n ∈ cands) →
    ∃ ws ∈ lagrDFS k vs cands, spanOf ws = D ∧ ∀ v ∈ ws, v < 4096
  | 0, vs, cands, hlt, hD, hk, _ =>
    ⟨vs, List.mem_singleton_self _,
      Submodule.eq_of_le_of_finrank_eq (spanOf_le hsing hdim hD) (by rw [hdim]; omega), hlt⟩
  | k + 1, vs, cands, hlt, hD, hk, hc => by
    have hle := spanOf_le hsing hdim hD
    have hne : spanOf vs ≠ D := fun h => by rw [h, hdim] at hk; omega
    obtain ⟨x, hxD, hxS⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
    have hex : ∃ n, n < 4096 ∧ vecOf n ∈ D ∧ vecOf n ∉ spanOf vs :=
      ⟨codeOf x, codeOf_lt x, by rwa [vecOf_codeOf], by rwa [vecOf_codeOf]⟩
    classical
    set v := Nat.find hex with hvdef
    obtain ⟨hv4, hvD, hvS⟩ := Nat.find_spec hex
    have hmin : ∀ m, m < 4096 → vecOf m ∈ D → vecOf m ∉ spanOf vs → v ≤ m := fun m h1 h2 h3 =>
      Nat.find_min' hex ⟨h1, h2, h3⟩
    have hcond : v ∉ spanList vs ∧ ∀ s ∈ spanList vs, v ≤ v ^^^ s := by
      refine ⟨fun h => hvS ((mem_spanList_iff hlt hv4).1 h), fun s hs => ?_⟩
      have hs4 := spanList_lt hlt s hs
      have hsS := (mem_spanList_iff hlt hs4).1 hs
      refine hmin _ (xor_lt hv4 hs4) (by rw [vecOf_xor]; exact D.add_mem hvD (hle hsS))
        fun h => hvS ?_
      rw [vecOf_xor] at h
      simpa using (spanOf vs).sub_mem h hsS
    have hv' : vecOf v ∈ spanOf (v :: vs) := mem_spanOf_of_mem List.mem_cons_self
    have hsub : spanOf vs ≤ spanOf (v :: vs) :=
      Submodule.span_mono fun _ ⟨w, hw, hx⟩ => ⟨w, List.mem_cons_of_mem v hw, hx⟩
    obtain ⟨ws, hws, hwsD, hwslt⟩ := lagr_step k (v :: vs)
      (cands.filter fun w => decide (v < w) && !f0b w v)
      (fun w hw => by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hv4
        · exact hlt w hw)
      (fun w hw => by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hvD
        · exact hD w hw)
      (by rw [finrank_spanOf_cons hvS]; omega)
      (fun n hn hnD hnS => by
        have hnS' : vecOf n ∉ spanOf vs := fun h => hnS (hsub h)
        rw [List.mem_filter]
        refine ⟨hc n hn hnD hnS', ?_⟩
        have hvn : v < n := lt_of_le_of_ne (hmin n hn hnD hnS') fun h => hnS (h ▸ hv')
        have hf : f0b n v = false :=
          eq_false_of_ite (by rw [← f0_vecOf]; exact f0_eq_zero_of_mem hsing hnD hvD)
        simp [hvn, hf])
    refine ⟨ws, ?_, hwsD, hwslt⟩
    simp only [lagrDFS, List.mem_flatMap]
    exact ⟨v, hc v hv4 hvD hvS, by rw [if_pos hcond]; exact hws⟩

theorem exists_mem_lagrDFS {a0 : ℕ} (ha0 : a0 < 4096) (ha00 : a0 ≠ 0) (haD : vecOf a0 ∈ D) :
    ∃ vs ∈ lagrDFS 5 [a0] (lagrCand a0), spanOf vs = D ∧ ∀ v ∈ vs, v < 4096 := by
  have hnil : vecOf a0 ∉ spanOf [] := by
    rw [spanOf_nil, Submodule.mem_bot, vecOf_eq_zero ha0]
    exact ha00
  refine lagr_step hsing hdim 5 [a0] (lagrCand a0) (by simpa using ha0) (by simpa using haD)
    (by rw [finrank_spanOf_cons hnil, spanOf_nil, finrank_bot]) fun n hn hnD hnS => ?_
  have ha' : vecOf a0 ∈ spanOf [a0] := mem_spanOf_of_mem List.mem_cons_self
  have hn0 : n ≠ 0 := fun h => hnS (h ▸ vecOf_zero ▸ Submodule.zero_mem _)
  have hna : n ≠ a0 := fun h => hnS (h ▸ ha')
  have hq : q0b n = false := eq_false_of_ite (by rw [← q0_vecOf]; exact hsing _ hnD)
  have hf : f0b n a0 = false :=
    eq_false_of_ite (by rw [← f0_vecOf]; exact f0_eq_zero_of_mem hsing hnD haD)
  simp [lagrCand, hn, hn0, hna, hq, hf]

end Complete

end CFSG.GF2Type.Smith1979.GammaU

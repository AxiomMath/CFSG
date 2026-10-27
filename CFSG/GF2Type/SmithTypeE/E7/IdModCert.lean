module

public import CFSG.GF2Type.SmithTypeE.DMod.Basic
public import Certificates.Certificate38750

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

theorem idQaCheck_holds : id7ChkQa = true :=
  Certificates.certificate38750

theorem bit_smul (b : Bool) (v : V) : bit b • v = if b then v else 0 := by
  cases b <;> simp [bit]

theorem decode32_foldl_xor (p : ℕ → Bool) (f : ℕ → ℕ) (n : ℕ) :
    decode32 ((List.range n).foldl (fun acc t => if p t then acc ^^^ f t else acc) 0) =
      ∑ t ∈ Finset.range n, bit (p t) • decode32 (f t) := by
  induction n with
  | zero => simp [decode32_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil, bit_smul]
    split_ifs
    · rw [decode32_xor]
    · rw [add_zero]

theorem foldl_xor_lt32 {p : ℕ → Bool} {f : ℕ → ℕ} {n : ℕ} (hf : ∀ t < n, f t < 2 ^ 32) :
    (List.range n).foldl (fun acc t => if p t then acc ^^^ f t else acc) 0 < 2 ^ 32 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have h := ih fun t ht => hf t (by omega)
    split_ifs
    · exact Nat.xor_lt_two_pow h (hf n (by omega))
    · exact h

theorem getElem!_map_of_lt' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {a : Array α}
    {k : ℕ} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by rwa [Array.size_map]), Array.getElem_map,
    getElem!_pos a k hk]

theorem getElem!_mem' {α : Type} [Inhabited α] {a : Array α} {k : ℕ} (hk : k < a.size) :
    a[k]! ∈ a := by
  rw [getElem!_pos a k hk]
  exact Array.getElem_mem hk

theorem qa_parts :
    id7QaGens.size = 16 ∧ id7QaDual.size = 16 ∧ (∀ g ∈ id7QaGens, id7QaGenOK g = true) ∧
      (∀ s < 16, ∀ t < 16, fB id7QaVecs[s]! id7QaDual[t]! = (s == t)) ∧
      ∀ j < 75735, adjW 0 j = (id7Proj (wt j) == wt j) := by
  have h := idQaCheck_holds
  simp only [id7ChkQa, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, fun s hs t ht => by simpa using h4 s hs t ht,
    fun j hj => by simpa using h5 j hj⟩

section Qa

theorem qaVecs_get {s : ℕ} (hs : s < 16) : id7QaVecs[s]! = id7QaVec id7QaGens[s]! := by
  rw [id7QaVecs, getElem!_map_of_lt' _ (by rw [(qa_parts).1]; exact hs)]

theorem dec12_mem_planeSub_zero {c : ℕ} (hc : c &&& 63 = 0) : dec12 c ∈ planeSub 0 := by
  rw [planeSub, pbArr_zero, mem_planeSpan_fBasis_iff, fst_dec12_eq_zero_iff]
  intro i hi
  have h := testBit_and_63 c i
  rw [hc, Nat.zero_testBit] at h
  simpa [hi] using h.symm

theorem qaVecs_spec {s : ℕ} (hs : s < 16) :
    ∃ p : ℕ, p < 365211 ∧ (∀ x ∈ lineSet p, x ∈ planeSub 0) ∧ ∃ k : ℕ, k < 75735 ∧
      fB (wt 0) (wt k) = false ∧ id7QaVecs[s]! = applyCols (tvCols p) (wt k) ^^^ wt k := by
  obtain ⟨h1, -, h3, -, -⟩ := qa_parts
  have hs' : s < id7QaGens.size := by rw [h1]; exact hs
  have hg := h3 _ (getElem!_mem' hs')
  set g := id7QaGens[s]! with hgdef
  simp only [id7QaGenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨⟨hu4096, hw4096⟩, hu63⟩, hw63⟩, hp⟩, hk⟩, hfB⟩ := hg
  refine ⟨lineIdx g.1 g.2.1, hp, ?_, g.2.2, hk, hfB, ?_⟩
  · have hpair := linePair_lineIdx hu4096 hw4096 hp
    intro x hx
    rw [lineSet_eq, hpair] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact dec12_mem_planeSub_zero hu63
    · exact dec12_mem_planeSub_zero hw63
    · rw [dec12_xor]
      exact Submodule.add_mem _ (dec12_mem_planeSub_zero hu63) (dec12_mem_planeSub_zero hw63)
  · rw [qaVecs_get hs, id7QaVec]

theorem qaVecs_lt {s : ℕ} (hs : s < 16) : id7QaVecs[s]! < 2 ^ 32 := by
  obtain ⟨p, hp, -, k, hk, -, he⟩ := qaVecs_spec hs
  rw [he]
  exact Nat.xor_lt_two_pow (applyCols_lt (size_tvCols p) (fun c hc => tvCols_lt p hc) _)
    (wt_lt hk)

theorem fModel_qa (s t : Fin 16) :
    fModel (decode32 id7QaVecs[s.val]!) (decode32 id7QaDual[t.val]!) = if s = t then 1 else 0 := by
  rw [fModel_decode, (qa_parts).2.2.2.1 s s.2 t t.2]
  by_cases h : s = t
  · subst h
    simp [bit]
  · have h' : (s.val == t.val) = false := by simpa [Fin.ext_iff] using h
    simp [h', h, bit]

theorem linearIndependent_qa :
    LinearIndependent (ZMod 2) fun s : Fin 16 => decode32 id7QaVecs[s.val]! := by
  refine Fintype.linearIndependent_iff.2 fun c hc t => ?_
  have h := congrArg (fun w => fModel w (decode32 id7QaDual[t.val]!)) hc
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_zero,
    LinearMap.zero_apply, fModel_qa, mul_ite, mul_one, mul_zero] at h
  simpa using h

theorem decode32_proj (w : ℕ) :
    decode32 (id7Proj w) = ∑ t : Fin 16,
      fModel (decode32 w) (decode32 id7QaDual[t.val]!) • decode32 id7QaVecs[t.val]! := by
  rw [id7Proj, decode32_foldl_xor, ← Fin.sum_univ_eq_sum_range
    (fun t => bit (fB w id7QaDual[t]!) • decode32 id7QaVecs[t]!) 16]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [fModel_decode]

theorem proj_eq_of_mem {w : V}
    (hw : w ∈ Submodule.span (ZMod 2) (Set.range fun s : Fin 16 => decode32 id7QaVecs[s.val]!)) :
    ∑ t : Fin 16, fModel w (decode32 id7QaDual[t.val]!) • decode32 id7QaVecs[t.val]! = w := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hw
  have key : ∀ t : Fin 16, fModel (∑ s : Fin 16, c s • decode32 id7QaVecs[s.val]!)
      (decode32 id7QaDual[t.val]!) = c t := by
    intro t
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      fModel_qa, mul_ite, mul_one, mul_zero]
    simp
  simp only [key]

theorem exists_qaBasis :
    ∃ v : Fin 16 → V, LinearIndependent (ZMod 2) v ∧
      (∀ s, ∃ p : Fin 365211, (∀ x ∈ lineSet p.val, x ∈ planeSub 0) ∧ ∃ k : Fin 75735,
        ¬ Opp 0 k.val ∧ v s = tvEquiv p.val (wtV k.val) + wtV k.val) ∧
      ∀ j : Fin 75735, wtV j.val ∈ Submodule.span (ZMod 2) (Set.range v) ↔
        adjW 0 j.val = true := by
  refine ⟨fun s => decode32 id7QaVecs[s.val]!, linearIndependent_qa, fun s => ?_, fun j => ?_⟩
  · obtain ⟨p, hp, hline, k, hk, hfB, he⟩ := qaVecs_spec s.2
    refine ⟨⟨p, hp⟩, hline, ⟨k, hk⟩, fun ho => ?_, ?_⟩
    · have h1 := fModel_wtV_zero hk
      rw [wtV, wtV, fModel_decode, hfB] at h1
      simp [ho, bit] at h1
    · simp only
      rw [he, decode32_xor, wtV, tvEquiv_decode hp]
  · rw [(qa_parts).2.2.2.2 j j.2, beq_iff_eq]
    have hsum : decode32 (id7Proj (wt j.val)) =
        ∑ t : Fin 16, fModel (wtV j.val) (decode32 id7QaDual[t.val]!) •
          decode32 id7QaVecs[t.val]! := decode32_proj _
    constructor
    · intro hmem
      have hlt : id7Proj (wt j.val) < 2 ^ 32 := by
        unfold id7Proj
        exact foldl_xor_lt32 fun t ht => qaVecs_lt (by omega)
      refine eq_of_decode32_eq hlt (wt_lt j.2) ?_
      rw [hsum]
      exact proj_eq_of_mem hmem
    · intro he
      rw [wtV, ← he, hsum]
      exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

end Qa

end CFSG.GF2Type.SmithTypeE.E7

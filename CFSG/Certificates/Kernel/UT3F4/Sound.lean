module

public import Certificates.Data.Kernel.UT3F4.Check
public import CFSG.GH74.Uniqueness.SU.KI1r4QAutInputs

public section

namespace CFSG.Certificates.Kernel.UT3F4

open CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.K.R4.Q64 CFSG.GH74.GLS.Bg.TwoGroups

theorem orB_eq (x y : Bool) : orB x y = (x || y) := by cases x <;> rfl

theorem andB_eq (x y : Bool) : andB x y = (x && y) := by cases x <;> rfl

theorem notB_eq (x : Bool) : notB x = !x := by cases x <;> rfl

theorem letN_eq (v : Nat) (k : Nat → Bool) : letN v k = k v := by cases v <;> rfl

theorem allL_eq (L : List Nat) (f : Nat → Bool) : allL L f = L.all f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change andB (f x) (allL L f) = (x :: L).all f
    rw [andB_eq, ih, List.all_cons]

theorem anyL_eq (L : List Nat) (f : Nat → Bool) : anyL L f = L.any f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change orB (f x) (anyL L f) = (x :: L).any f
    rw [orB_eq, ih, List.any_cons]

theorem cntL_eq (L : List Nat) (f : Nat → Bool) : cntL L f = L.countP f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change Bool.rec (cntL L f) (Nat.succ (cntL L f)) (f x) = (x :: L).countP f
    rw [List.countP_cons, ih]
    cases f x <;> simp

@[expose] def fc : F4c → Nat
  | .z0 => 0
  | .z1 => 1
  | .w => 2
  | .w2 => 3

@[expose] def enc (g : L34Syl) : Nat := fc g.a + 4 * fc g.b + 16 * fc g.c

theorem enc_mul : ∀ g h : L34Syl, enc (g * h) = mulN (enc g) (enc h) := by decide +kernel

theorem enc_one : enc 1 = 0 := by decide +kernel

theorem enc_inj : ∀ g h : L34Syl, enc g = enc h → g = h := by decide +kernel

theorem enc_a : ∀ g : L34Syl, Nat.land (enc g) 3 = fc g.a := by decide +kernel

theorem enc_b : ∀ g : L34Syl, Nat.land (Nat.shiftRight (enc g) 2) 3 = fc g.b := by decide +kernel

theorem enc_z : ∀ g : L34Syl,
    Nat.xor (Nat.shiftRight (enc g) 4) (fmN (fc g.a) (fc g.b)) = fc (g.c + g.a * g.b) := by
  decide +kernel

theorem allP_map : allP.map enc = allPN := by decide +kernel

theorem involList_map : involList.map enc = invN := by decide +kernel

theorem mem_allP' : ∀ g : L34Syl, g ∈ allP := by decide +kernel

theorem prod_wordOf' : ∀ g : L34Syl, ((wordOf g).map gen).prod = g := by decide +kernel

theorem wordOf_one' : wordOf 1 = [] := by decide

theorem wordOf_gen' : ∀ i, wordOf (gen i) = [i] := by decide

theorem enc_gen : enc (gen 0) = 1 ∧ enc (gen 1) = 2 ∧ enc (gen 2) = 4 ∧ enc (gen 3) = 8 := by
  decide +kernel

theorem enc_phi : enc (phiFun (gen 0)) = 4 ∧ enc (phiFun (gen 1)) = 12 ∧
    enc (phiFun (gen 2)) = 1 ∧ enc (phiFun (gen 3)) = 3 := by
  decide +kernel

theorem beq_enc (g h : L34Syl) : Nat.beq (enc g) (enc h) = decide (g = h) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
  exact ⟨enc_inj g h, congrArg enc⟩

theorem evalT_eq (t : Fin 4 → L34Syl) (g : L34Syl) : evalT wordOf t g =
    ((wordA g.a).map t).prod * ((wordB g.b).map t).prod *
      ((wordZ (g.c + g.a * g.b)).map t).prod := by
  simp only [evalT, wordOf, List.map_append, List.prod_append]

theorem enc_wordA (t : Fin 4 → L34Syl) (a : F4c) :
    enc ((wordA a).map t).prod = eA (enc (t 0)) (enc (t 1)) (fc a) := by
  cases a <;> simp only [wordA, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, enc_mul, enc_one] <;> rfl

theorem enc_wordB (t : Fin 4 → L34Syl) (b : F4c) :
    enc ((wordB b).map t).prod = eA (enc (t 2)) (enc (t 3)) (fc b) := by
  cases b <;> simp only [wordB, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, enc_mul, enc_one] <;> rfl

theorem enc_wordZ (t : Fin 4 → L34Syl) (z : F4c) :
    enc ((wordZ z).map t).prod = eZ (enc (t 0)) (enc (t 1)) (enc (t 2)) (fc z) := by
  cases z <;> simp only [wordZ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, enc_mul, enc_one] <;> rfl

theorem enc_evalT (t : Fin 4 → L34Syl) (g : L34Syl) :
    enc (evalT wordOf t g) = evalN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) (enc g) := by
  rw [evalT_eq, enc_mul, enc_mul, enc_wordA, enc_wordB, enc_wordZ, evalN, enc_a, enc_b, enc_z]

theorem fin4 {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ i, P i := by
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3]

theorem mem_involList' (g : L34Syl) (h : g * g = 1) : g ∈ involList :=
  List.mem_filter.2 ⟨mem_allP' g, decide_eq_true h⟩

theorem countP_enc (p : L34Syl → Prop) [DecidablePred p] (f : Nat → Bool)
    (hf : ∀ g, f (enc g) = decide (p g)) : allPN.countP f = (allP.filter p).length := by
  rw [← allP_map, List.countP_map, List.countP_eq_length_filter]
  congr 1
  exact List.filter_congr fun g _ => hf g

theorem gen_rels : (gen 0 * gen 1 = gen 1 * gen 0) ∧ (gen 2 * gen 3 = gen 3 * gen 2) ∧
    (gen 0 * gen 2 ≠ gen 2 * gen 0) ∧
    ((gen 1 * gen 2) * (gen 1 * gen 2) = (gen 0 * gen 3) * (gen 0 * gen 3)) ∧
    ((gen 1 * gen 3) * (gen 1 * gen 3) =
      ((gen 0 * gen 2) * (gen 0 * gen 2)) * ((gen 0 * gen 3) * (gen 0 * gen 3))) ∧
    (∀ i, gen i * gen i = 1) := by
  decide

theorem quad_of_aut (t : Fin 4 → L34Syl) (β : MulAut L34Syl) (ht : ∀ i, t i = β (gen i)) :
    (∀ i, enc (t i) ∈ invN) ∧ commN (enc (t 0)) (enc (t 1)) = true ∧
      commN (enc (t 0)) (enc (t 2)) = false ∧ commN (enc (t 2)) (enc (t 3)) = true ∧
      relN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) = true := by
  obtain ⟨r01, r23, r02, r3, r4, rsq⟩ := gen_rels
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [← involList_map]
    exact List.mem_map_of_mem (mem_involList' _ (by rw [ht, ← map_mul, rsq, map_one]))
  · rw [commN, ← enc_mul, ← enc_mul, beq_enc, ht, ht, ← map_mul, ← map_mul, r01]
    exact decide_eq_true rfl
  · rw [commN, ← enc_mul, ← enc_mul, beq_enc, ht, ht, ← map_mul, ← map_mul]
    exact decide_eq_false fun h => r02 (β.injective h)
  · rw [commN, ← enc_mul, ← enc_mul, beq_enc, ht, ht, ← map_mul, ← map_mul, r23]
    exact decide_eq_true rfl
  · simp only [relN, sqN, andB_eq, ← enc_mul, beq_enc, ht, ← map_mul, r3, r4, decide_true,
      Bool.and_self]

theorem key_of_checkN (hc : checkN = true) : ∀ t ∈ candList,
    (∀ i, evalT wordOf t (evalT wordOf t (gen i)) = gen i) →
    IsAutT allP gen wordOf t →
    (allP.filter (fun g => evalT wordOf t g = g)).length = 8 →
    (allP.filter (fun g => evalT wordOf t g = g ∧ g * g = 1)).length = 2 →
    ∃ p ∈ pairList, IsAutT allP gen wordOf (mkS t p) ∧
      ∀ i, evalT wordOf (mkS t p) (phiFun (gen i)) = evalT wordOf t (mkS t p i) := by
  intro t _ h1 hA hf hq
  obtain ⟨β, hβ⟩ := exists_autEquiv gen wordOf prod_wordOf' wordOf_one' allP mem_allP' t hA
  have evalT_gen : ∀ i, evalT wordOf t (gen i) = t i := fun i => by
    simp only [evalT, wordOf_gen', List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
  have ht : ∀ i, t i = β (gen i) := fun i => by rw [hβ, evalT_gen]
  obtain ⟨hinv, hc01, hc02, hc23, hrel⟩ := quad_of_aut t β ht
  obtain ⟨eg0, eg1, eg2, eg3⟩ := enc_gen
  have he : ∀ g, enc (evalT wordOf t g) =
      evalN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) (enc g) := enc_evalT t
  have hh1 : h1N (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) = true := by
    have e : ∀ i, evalN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) (enc (t i)) =
        enc (gen i) := fun i => by rw [← he, ← evalT_gen i, h1 i]
    rw [h1N, andB_eq, andB_eq, andB_eq, e 0, e 1, e 2, e 3, eg0, eg1, eg2, eg3]
    rfl
  have hfix : fixN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) = true := by
    rw [fixN, cntL_eq, countP_enc (fun g => evalT wordOf t g = g) _ (fun g => by
      rw [← he, beq_enc]), hf]
    rfl
  have hq8 : q8N (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) = true := by
    rw [q8N, cntL_eq, countP_enc (fun g => evalT wordOf t g = g ∧ g * g = 1) _ (fun g => by
      rw [andB_eq, ← he, beq_enc, ← enc_mul, ← enc_one, beq_enc, Bool.decide_and]), hq]
    rfl
  have htest : testN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) = true := by
    rw [checkN, allL_eq, List.all_eq_true] at hc
    have h0 := hc _ (hinv 0)
    rw [allL_eq, List.all_eq_true] at h0
    have h1' := h0 _ (hinv 1)
    rw [hc01, notB_eq, Bool.not_true, orB_eq, Bool.false_or, allL_eq, List.all_eq_true] at h1'
    have h2 := h1' _ (hinv 2)
    rw [hc02, orB_eq, Bool.false_or, allL_eq, List.all_eq_true] at h2
    have h3 := h2 _ (hinv 3)
    simpa only [hc23, hrel, notB_eq, Bool.not_true, orB_eq, Bool.false_or] using h3
  rw [testN, hh1, hfix, hq8] at htest
  simp only [notB_eq, Bool.not_true, orB_eq, Bool.false_or] at htest
  rw [witN, anyL_eq, List.any_eq_true] at htest
  obtain ⟨p, hp, hp'⟩ := htest
  rw [anyL_eq, List.any_eq_true] at hp'
  obtain ⟨q, hq', hpq⟩ := hp'
  rw [andB_eq, letN_eq, letN_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hpq
  obtain ⟨hcpq, haut, hint⟩ := hpq
  rw [← involList_map] at hp hq'
  obtain ⟨gp, hgp, rfl⟩ := List.mem_map.1 hp
  obtain ⟨gq, hgq, rfl⟩ := List.mem_map.1 hq'
  rw [commN, ← enc_mul, ← enc_mul, beq_enc] at hcpq
  refine ⟨(gp, gq), List.mem_flatMap.2 ⟨gp, hgp, List.mem_map.2
    ⟨gq, List.mem_filter.2 ⟨hgq, hcpq⟩, rfl⟩⟩, ?_⟩
  have m3 : mkS t (gp, gq) 3 = evalT wordOf t gp * evalT wordOf t gq := rfl
  have hs3 : enc (mkS t (gp, gq) 3) = mulN
      (evalN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) (enc gp))
      (evalN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) (enc gq)) := by
    rw [m3, enc_mul, he, he]
  have m2 : mkS t (gp, gq) 2 = evalT wordOf t gp := rfl
  have hs2 : enc (mkS t (gp, gq) 2) =
      evalN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) (enc gp) := by
    rw [m2, he]
  have hs1 : enc (mkS t (gp, gq) 1) = enc gq := rfl
  have hs0 : enc (mkS t (gp, gq) 0) = enc gp := rfl
  have hs : ∀ g, enc (evalT wordOf (mkS t (gp, gq)) g) = evalN (enc gp) (enc gq)
      (evalN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) (enc gp))
      (mulN (evalN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) (enc gp))
        (evalN (enc (t 0)) (enc (t 1)) (enc (t 2)) (enc (t 3)) (enc gq))) (enc g) := by
    intro g
    rw [enc_evalT, hs0, hs1, hs2, hs3]
  rw [autN, andB_eq, Bool.and_eq_true, allL_eq, allL_eq, List.all_eq_true, List.all_eq_true]
    at haut
  obtain ⟨haut1, haut2⟩ := haut
  refine ⟨⟨fun g _ => ?_, fun g _ hg => ?_⟩, ?_⟩
  · have hg := haut1 (enc g) (by rw [← allP_map]; exact List.mem_map_of_mem (mem_allP' g))
    simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at hg
    obtain ⟨k0, k1, k2, k3⟩ := hg
    refine fin4 ?_ ?_ ?_ ?_ <;> apply enc_inj <;> rw [hs, enc_mul, enc_mul, hs]
    · rw [eg0, k0, hs0]
    · rw [eg1, k1, hs1]
    · rw [eg2, k2, hs2]
    · rw [eg3, k3, hs3]
  · apply enc_inj
    have hg' := haut2 (enc g) (by rw [← allP_map]; exact List.mem_map_of_mem (mem_allP' g))
    rw [← hs, hg, enc_one, orB_eq, notB_eq] at hg'
    rw [enc_one]
    simpa using hg'
  · simp only [intN, andB_eq, Bool.and_eq_true, Nat.beq_eq] at hint
    obtain ⟨k0, k1, k2, k3⟩ := hint
    obtain ⟨p0, p1, p2, p3⟩ := enc_phi
    refine fin4 ?_ ?_ ?_ ?_ <;> apply enc_inj <;> rw [hs, he]
    · rw [p0, hs0, k0]
    · rw [p1, hs1, k1]
    · rw [p2, hs2, k2]
    · rw [p3, hs3, k3]

end CFSG.Certificates.Kernel.UT3F4

end

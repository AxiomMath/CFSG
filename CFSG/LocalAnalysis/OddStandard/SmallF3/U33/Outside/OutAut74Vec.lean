module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.GH74.GLS.Bg.TwoGroups.L23

abbrev V4 : Type := F4c × F4c

@[expose] def sqF (v : V4) : F4c := v.1 * v.2

@[expose] def omg : F4c := ⟨0, 1⟩

@[expose] def sigOf (s : F4c × F4c) (c : F4c) : F4c :=
  (if c.a = 0 then 0 else s.1) + (if c.b = 0 then 0 else s.2)

@[expose] def linOf (t : V4 × V4 × V4 × V4) (v : V4) : V4 :=
  (if v.1.a = 0 then 0 else t.1) + (if v.1.b = 0 then 0 else t.2.1) +
    (if v.2.a = 0 then 0 else t.2.2.1) + (if v.2.b = 0 then 0 else t.2.2.2)

@[expose] def tupOf (g : V4 → V4) : V4 × V4 × V4 × V4 :=
  (g (1, 0), g (omg, 0), g (0, 1), g (0, omg))

@[expose] def allF : List F4c := [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]

@[expose] def allV : List V4 := allF.flatMap (fun x => allF.map (fun y => (x, y)))

@[expose] def nzV : List V4 := allV.filter (fun v => decide (sqF v = 0 ∧ v ≠ 0))

@[expose] def s0 (t : V4 × V4 × V4 × V4) : F4c × F4c :=
  (sqF (linOf t (1, 1)), sqF (linOf t (omg, 1)))

@[expose] def goodB (t : V4 × V4 × V4 × V4) : Bool :=
  decide ((allV.map (linOf t)).Nodup) &&
    allV.all (fun v => decide (sqF (linOf t v) = sigOf (s0 t) (sqF v)))

@[expose] def goodTuples : List (V4 × V4 × V4 × V4) :=
  (nzV.flatMap fun t1 => nzV.flatMap fun t2 => nzV.flatMap fun t3 => nzV.map fun t4 =>
    (t1, t2, t3, t4)).filter goodB

@[expose] def oneTuples : List (V4 × V4 × V4 × V4) :=
  goodTuples.filter (fun t => decide (s0 t = (1, omg)))

theorem mem_allV : ∀ v : V4, v ∈ allV := by decide +kernel

theorem allV_nodup : allV.Nodup := by decide +kernel

private lemma addHom_ite_zero {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) (p : Prop) [Decidable p] (x : M) :
    (if p then 0 else f x) = f (if p then 0 else x) := by
  split_ifs <;> simp [map_zero]

private lemma addHom_add_four {g : V4 →+ V4} (a b c d : V4) :
    g a + g b + g c + g d = g (a + b + c + d) := by
  simp [map_add]

private lemma mem_nzV_iff (v : V4) : v ∈ nzV ↔ sqF v = 0 ∧ v ≠ 0 := by
  rw [nzV, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_allV v, h⟩⟩

private lemma gen_mem_nzV (g : V4 →+ V4) (σ : F4c →+ F4c)
    (hinj : Function.Injective g) (hq : ∀ v, sqF (g v) = σ (sqF v))
    (e : V4) (he0 : sqF e = 0) (hene : e ≠ 0) : g e ∈ nzV := by
  rw [mem_nzV_iff]
  refine ⟨?_, ?_⟩
  · rw [hq, he0, map_zero]
  · exact fun h => hene (hinj (by rw [h, map_zero]))

theorem linOf_tupOf (g : V4 →+ V4) (v : V4) : linOf (tupOf g) v = g v := by
  have hpt : (if v.1.a = 0 then 0 else (1, 0)) + (if v.1.b = 0 then 0 else (omg, 0)) +
      (if v.2.a = 0 then 0 else (0, 1)) + (if v.2.b = 0 then 0 else (0, omg)) = v := by
    revert v
    decide +kernel
  rw [linOf, tupOf]
  rw [addHom_ite_zero g, addHom_ite_zero g, addHom_ite_zero g, addHom_ite_zero g]
  rw [addHom_add_four, hpt]

theorem sigOf_apply (σ : F4c →+ F4c) (c : F4c) : sigOf (σ 1, σ omg) c = σ c := by
  have hpt : (if c.a = 0 then 0 else (1 : F4c)) + (if c.b = 0 then 0 else omg) = c := by
    revert c
    decide +kernel
  rw [sigOf]
  rw [addHom_ite_zero σ, addHom_ite_zero σ]
  rw [← map_add, hpt]

theorem tupOf_injective {g g' : V4 →+ V4} (h : tupOf g = tupOf g') : g = g' := by
  apply AddMonoidHom.ext
  intro v
  rw [← linOf_tupOf g v, ← linOf_tupOf g' v, h]

theorem tupOf_mem_goodTuples (g : V4 →+ V4) (σ : F4c →+ F4c) (hinj : Function.Injective g)
    (hq : ∀ v, sqF (g v) = σ (sqF v)) : tupOf g ∈ goodTuples := by
  have hlin : ∀ v, linOf (tupOf g) v = g v := linOf_tupOf g
  have hs0 : s0 (tupOf g) = (σ 1, σ omg) := by
    simp only [s0, hlin, hq]
    simp [sqF, omg]
  have h1 : (tupOf g).1 ∈ nzV :=
    gen_mem_nzV g σ hinj hq (1, 0) (by decide +kernel) (by decide +kernel)
  have h2 : (tupOf g).2.1 ∈ nzV :=
    gen_mem_nzV g σ hinj hq (omg, 0) (by decide +kernel) (by decide +kernel)
  have h3 : (tupOf g).2.2.1 ∈ nzV :=
    gen_mem_nzV g σ hinj hq (0, 1) (by decide +kernel) (by decide +kernel)
  have h4 : (tupOf g).2.2.2 ∈ nzV :=
    gen_mem_nzV g σ hinj hq (0, omg) (by decide +kernel) (by decide +kernel)
  have hgood : goodB (tupOf g) = true := by
    rw [goodB, Bool.and_eq_true]
    constructor
    · rw [decide_eq_true_eq, List.map_congr_left (fun v _ => hlin v)]
      exact allV_nodup.map hinj
    · rw [List.all_eq_true]
      intro v hv
      rw [decide_eq_true_eq, hlin v, hq v, hs0, sigOf_apply]
  rw [goodTuples, List.mem_filter]
  refine ⟨?_, hgood⟩
  refine List.mem_flatMap.2 ⟨(tupOf g).1, h1, ?_⟩
  refine List.mem_flatMap.2 ⟨(tupOf g).2.1, h2, ?_⟩
  refine List.mem_flatMap.2 ⟨(tupOf g).2.2.1, h3, ?_⟩
  refine List.mem_map.2 ⟨(tupOf g).2.2.2, h4, ?_⟩
  rfl

theorem tupOf_mem_oneTuples (g : V4 →+ V4) (hinj : Function.Injective g)
    (hq : ∀ v, sqF (g v) = sqF v) : tupOf g ∈ oneTuples := by
  have hgood : tupOf g ∈ goodTuples :=
    tupOf_mem_goodTuples g (AddMonoidHom.id F4c) hinj (fun v => by simpa using hq v)
  have hs0 : s0 (tupOf g) = (1, omg) := by
    simp only [s0, linOf_tupOf, hq]
    simp [sqF, omg]
  rw [oneTuples, List.mem_filter]
  exact ⟨hgood, by rw [decide_eq_true_eq, hs0]⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBH4All

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8
open CFSG.ComponentClassification.HSFLit.Sec8

namespace MB
open CFSG.ComponentClassification.HSFLit.Sec8.MB

@[expose] def E0L : List MB := [1, z, y, z * y, k, z * k, y * k, z * y * k]

@[expose] def Z2L : List MB := [1, z, y, z * y, w₁ * k, w₁ * y * k, w₁ * z * k, w₁ * z * y * k]

@[expose] def AL : List MB := (allBits 6).map (nfProd [w₂, w₁, t * v, z, y, k])

@[expose] def gensT2 (p : ℕ × ℕ) : List (List MB) := gens.map conjQ1 ++ [cQ p.1, g0Q p]

@[expose] def inZ (x : MB) : Bool := x == 1 || x == z

@[expose] def innerT (τ : MB × Bool × Bool) : Bool := !τ.2.1 && !τ.2.2 && inQ1 τ.1

@[expose] def sylCheck (φ : List MB) (τ : MB × Bool × Bool) : Bool :=
  (!(gensQ1.all fun g => inZ (applyQ1 φ g * g⁻¹)) || innerT τ) &&
  (Z2L.all fun x => inZ (applyQ1 φ x * x⁻¹)) &&
  (!(Z2L.all fun x => applyQ1 φ x == x) || AL.any fun a => compQ1 φ φ == conjQ1 a) &&
  (!(E0L.all fun e => applyQ1 φ e == e) || innerT τ) &&
  (E0L.all fun e => inE0 (applyQ1 φ e))

@[expose] def stabL (p : ℕ × ℕ) (b : MB) : List ((MB × Bool × Bool) × List MB) :=
  (H4Zof p).filter fun e => inE0 (applyQ1 e.2 (b * t) * (b * t)⁻¹)

@[expose] def E0tau : Fin 8 → MB × Bool × Bool
  | 0 => (1, false, false) | 1 => (1, true, false) | 2 => (1, false, true)
  | 3 => (1, true, true) | 4 => (u, false, false) | 5 => (u, true, false)
  | 6 => (u, true, true) | 7 => (u, false, true)

@[expose] def E0y (i : Fin 8) : MB := if i.val < 4 then y else z * y

@[expose] def E0k : Fin 8 → MB
  | 0 => k | 1 => z * k | 2 => y * k | 3 => z * y * k
  | 4 => k | 5 => z * k | 6 => y * k | 7 => z * y * k

@[expose] def ar0 : Fin 4 → MB | 0 => 1 | 1 => w₂ | 2 => w₁ | 3 => w₂ * w₁

@[expose] def ar1 : Fin 4 → MB
  | 0 => t * v | 1 => w₂ * (t * v) | 2 => w₁ * (t * v) | 3 => w₂ * w₁ * (t * v)

@[expose] def g0tau : Fin 4 → MB × Bool × Bool
  | 0 => (1, false, false) | 1 => (1, false, true) | 2 => (1, true, false)
  | 3 => (1, true, true)

@[expose] def arep (b : MB) : MB := nfProd [w₂, w₁, t * v] [bit b 0, bit b 2, bit b 3]

theorem mem_E0L : ∀ e : MB, inE0 e = true ↔ e ∈ E0L := by decide +kernel

theorem E0L_sq : ∀ e ∈ E0L, e * e = 1 := by decide +kernel

theorem Z2L_inQC : ∀ x ∈ Z2L, inQC x = true := by decide +kernel

theorem Z2L_E0 : ∀ x ∈ Z2L, inE0 x = true → x ∈ [1, z, y, z * y] := by decide +kernel

theorem E0_comm_Q1 : ∀ x : MB, inQ1 x = true → ∀ e ∈ E0L, x * e = e * x := by decide +kernel

theorem AL_inQC : ∀ a ∈ AL, inQC a = true := by decide +kernel

theorem sq_AL : ∀ e ∈ E0L, ∃ a ∈ AL, a * a = e := by decide +kernel

theorem inE0_of_sq : ∀ a : MB, inQC a = true → a * a = 1 → inE0 a = true := by decide +kernel

theorem inQC_of_comm_Z2 : ∀ x : MB, inQ1 x = true → (∀ w ∈ Z2L, x * w = w * x) →
    inQC x = true := by decide +kernel

theorem inQC_mul_t : ∀ x : MB, inQ1 x = true → inQC x = false → inQC (x * t⁻¹) = true := by
  decide +kernel

theorem t_not_inQC : inQC t = false := by decide +kernel

theorem arep_spec : ∀ b : MB, inQC b = true → inE0 ((arep b)⁻¹ * b) = true := by decide +kernel

theorem arep_cases : ∀ b : MB, (∃ i : Fin 4, arep b = ar0 i) ∨ ∃ i : Fin 4, arep b = ar1 i := by
  decide +kernel

theorem E0_cover : ∀ y' ∈ [y, z * y], ∀ k' ∈ [k, z * k, y * k, z * y * k],
    ∃ i : Fin 8, E0y i = y' ∧ E0k i = k' := by decide +kernel

theorem gensT2_z : ∀ p ∈ goodIdx, ∀ g ∈ gensT2 p, applyQ1 g z = z := by decide +kernel

theorem gensT2_move : ∀ p ∈ goodIdx, ∀ e ∈ E0L, e ≠ 1 → e ≠ z →
    ∃ g ∈ gensT2 p, applyQ1 g e ≠ e := by decide +kernel

theorem Z2_of_gens_1 : ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 (0, 2), inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by decide +kernel

theorem Z2_of_gens_2 : ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 (0, 10), inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by decide +kernel

theorem Z2_of_gens_3 : ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 (1, 0), inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by decide +kernel

theorem Z2_of_gens_4 : ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 (1, 8), inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by decide +kernel

theorem Z2_of_gens_5 : ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 (2, 2), inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by decide +kernel

theorem Z2_of_gens_6 : ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 (2, 10), inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by decide +kernel

theorem Z2_of_gens_7 : ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 (3, 0), inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by decide +kernel

theorem Z2_of_gens_8 : ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 (3, 8), inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by decide +kernel

theorem Z2_of_gens : ∀ p ∈ goodIdx, ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 p, inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by
  intro p hp
  simp only [goodIdx, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Z2_of_gens_1, Z2_of_gens_2, Z2_of_gens_3, Z2_of_gens_4, Z2_of_gens_5, Z2_of_gens_6,
    Z2_of_gens_7, Z2_of_gens_8]

theorem syl_facts_1 : (H4Zof (0, 2)).all (fun e => sylCheck e.2 e.1) = true := by decide +kernel

theorem syl_facts_2 : (H4Zof (0, 10)).all (fun e => sylCheck e.2 e.1) = true := by decide +kernel

theorem syl_facts_3 : (H4Zof (1, 0)).all (fun e => sylCheck e.2 e.1) = true := by decide +kernel

theorem syl_facts_4 : (H4Zof (1, 8)).all (fun e => sylCheck e.2 e.1) = true := by decide +kernel

theorem syl_facts_5 : (H4Zof (2, 2)).all (fun e => sylCheck e.2 e.1) = true := by decide +kernel

theorem syl_facts_6 : (H4Zof (2, 10)).all (fun e => sylCheck e.2 e.1) = true := by decide +kernel

theorem syl_facts_7 : (H4Zof (3, 0)).all (fun e => sylCheck e.2 e.1) = true := by decide +kernel

theorem syl_facts_8 : (H4Zof (3, 8)).all (fun e => sylCheck e.2 e.1) = true := by decide +kernel

theorem syl_facts : ∀ p ∈ goodIdx, (H4Zof p).all (fun e => sylCheck e.2 e.1) = true := by
  intro p hp
  simp only [goodIdx, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [syl_facts_1, syl_facts_2, syl_facts_3, syl_facts_4, syl_facts_5, syl_facts_6,
    syl_facts_7, syl_facts_8]

theorem stab_facts_1 : ∀ i : Fin 4, 64 ≤ (stabL (0, 2) (ar1 i)).length := by decide +kernel

theorem stab_facts_2 : ∀ i : Fin 4, 64 ≤ (stabL (0, 10) (ar1 i)).length := by decide +kernel

theorem stab_facts_3 : ∀ i : Fin 4, 64 ≤ (stabL (1, 0) (ar1 i)).length := by decide +kernel

theorem stab_facts_4 : ∀ i : Fin 4, 64 ≤ (stabL (1, 8) (ar1 i)).length := by decide +kernel

theorem stab_facts_5 : ∀ i : Fin 4, 64 ≤ (stabL (2, 2) (ar1 i)).length := by decide +kernel

theorem stab_facts_6 : ∀ i : Fin 4, 64 ≤ (stabL (2, 10) (ar1 i)).length := by decide +kernel

theorem stab_facts_7 : ∀ i : Fin 4, 64 ≤ (stabL (3, 0) (ar1 i)).length := by decide +kernel

theorem stab_facts_8 : ∀ i : Fin 4, 64 ≤ (stabL (3, 8) (ar1 i)).length := by decide +kernel

theorem stab_facts : ∀ p ∈ goodIdx, ∀ i : Fin 4, 64 ≤ (stabL p (ar1 i)).length := by
  intro p hp
  simp only [goodIdx, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [stab_facts_1, stab_facts_2, stab_facts_3, stab_facts_4, stab_facts_5, stab_facts_6,
    stab_facts_7, stab_facts_8]

theorem H4Zof_nodup_1 : ((H4Zof (0, 2)).map Prod.snd).Nodup := by decide +kernel

theorem H4Zof_nodup_2 : ((H4Zof (0, 10)).map Prod.snd).Nodup := by decide +kernel

theorem H4Zof_nodup_3 : ((H4Zof (1, 0)).map Prod.snd).Nodup := by decide +kernel

theorem H4Zof_nodup_4 : ((H4Zof (1, 8)).map Prod.snd).Nodup := by decide +kernel

theorem H4Zof_nodup_5 : ((H4Zof (2, 2)).map Prod.snd).Nodup := by decide +kernel

theorem H4Zof_nodup_6 : ((H4Zof (2, 10)).map Prod.snd).Nodup := by decide +kernel

theorem H4Zof_nodup_7 : ((H4Zof (3, 0)).map Prod.snd).Nodup := by decide +kernel

theorem H4Zof_nodup_8 : ((H4Zof (3, 8)).map Prod.snd).Nodup := by decide +kernel

theorem H4Zof_nodup : ∀ p ∈ goodIdx, ((H4Zof p).map Prod.snd).Nodup := by
  intro p hp
  simp only [goodIdx, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [H4Zof_nodup_1, H4Zof_nodup_2, H4Zof_nodup_3, H4Zof_nodup_4, H4Zof_nodup_5,
    H4Zof_nodup_6, H4Zof_nodup_7, H4Zof_nodup_8]

theorem E0tau_facts : ∀ p ∈ goodIdx, ∀ i : Fin 8,
    applyQ1 (H4elt p (E0tau i).1 (E0tau i).2.1 (E0tau i).2.2) y = E0y i ∧
      applyQ1 (H4elt p (E0tau i).1 (E0tau i).2.1 (E0tau i).2.2) k = E0k i := by decide +kernel

theorem g0tau_facts : ∀ p ∈ goodIdx, ∀ i : Fin 4,
    inE0 (applyQ1 (H4elt p (g0tau i).1 (g0tau i).2.1 (g0tau i).2.2) (ar0 i * t) * t⁻¹) = true := by
  decide +kernel

end MB

end Sec8

end CFSG.OddStandard.SmallF3.L33.KD

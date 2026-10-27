module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
public import Certificates.Data.Fi24Moore
public import CFSG.Sporadic.SchreierLemmas.MooreChain
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeTables

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Moore

open CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi24 (R J JR jR cls)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem moore_of_chainD24 {w : CFSG.Sporadic.Fi24.J} {k : ℕ} (hk : 2 ≤ k) (s : Fin k → R)
    (hs : ∀ i, s i ∈ CFSG.Sporadic.Fi24.D24 ∧ s i * jR w = jR w * s i)
    (hnc : ∀ i j : Fin k, i.val + 1 = j.val → s i ≠ s j ∧ s i * s j ≠ s j * s i)
    (hc : ∀ i j : Fin k, i.val + 2 ≤ j.val → s i * s j = s j * s i) :
    ∃ m : ℕ → CFSG.Sporadic.Fi24.J, CFSG.Sporadic.SchreierLemmas.IsMooreFamily (k - 1) m ∧ m 1 ≠ 1 ∧
      ∀ j, 1 ≤ j → j < k → m j * w = w * m j := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : Set (GL (Fin 781) (ZMod 3)),
      ∀ x, x ∈ D ↔ ∃ y ∈ CFSG.Sporadic.Fi24.D24, (y : GL (Fin 781) (ZMod 3)) = x :=
    ⟨{x | ∃ y ∈ CFSG.Sporadic.Fi24.D24, (y : GL (Fin 781) (ZMod 3)) = x}, fun _ => Iff.rfl⟩
  let s' : ℕ → GL (Fin 781) (ZMod 3) := fun i => if h : i < k then (s ⟨i, h⟩ : GL (Fin 781) (ZMod 3))
    else 1
  have hs' : ∀ i (h : i < k), s' i = (s ⟨i, h⟩ : GL (Fin 781) (ZMod 3)) := fun i h => dif_pos h
  have hsqD : ∀ x ∈ D, x * x = 1 := by
    intro x hxD
    obtain ⟨y, hy, rfl⟩ := (hD x).1 hxD
    simpa using congrArg Subtype.val (D24_mul_self hy)
  have hcubeD : ∀ x ∈ D, ∀ y ∈ D, x * y ≠ y * x → (x * y) ^ 3 = 1 := by
    intro x' hxD y' hyD hxy
    obtain ⟨x, hx, rfl⟩ := (hD x').1 hxD
    obtain ⟨y, hy, rfl⟩ := (hD y').1 hyD
    have h := D24_cube hx hy (fun e => hxy (by simpa using congrArg Subtype.val e))
    rw [pow_three']
    simpa using congrArg Subtype.val h
  have hconjD : ∀ x ∈ D, ∀ y ∈ D, y * x * y⁻¹ ∈ D := by
    intro x' hxD y' hyD
    obtain ⟨x, hx, rfl⟩ := (hD x').1 hxD
    obtain ⟨y, hy, rfl⟩ := (hD y').1 hyD
    exact (hD _).2 ⟨y * x * y⁻¹, D24_conj hx y, by simp⟩
  have hsD : ∀ i < k, s' i ∈ D := fun i hi => (hD _).2 ⟨s ⟨i, hi⟩, (hs _).1, (hs' i hi).symm⟩
  have hncD : ∀ i, i + 1 < k → s' i * s' (i + 1) ≠ s' (i + 1) * s' i := by
    intro i hi h
    apply (hnc ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl).2
    apply Subtype.ext
    rw [hs' i (by omega), hs' (i + 1) hi] at h
    simpa using h
  have hcD : ∀ i j, i + 2 ≤ j → j < k → s' i * s' j = s' j * s' i := by
    intro i j hij hj
    rw [hs' i (by omega), hs' j hj]
    simpa using congrArg Subtype.val (hc ⟨i, by omega⟩ ⟨j, hj⟩ hij)
  have hM := @CFSG.Sporadic.SchreierLemmas.moore_of_chain (GL (Fin 781) (ZMod 3)) inferInstance D
    hsqD hcubeD hconjD k hk s' hsD hncD hcD
  have hmem : ∀ j, j < k → CFSG.Sporadic.SchreierLemmas.mooreOfChain s' j ∈ J := by
    intro j hj
    unfold CFSG.Sporadic.SchreierLemmas.mooreOfChain
    have h0 := (hs ⟨0, by omega⟩).1
    obtain ⟨a, ha⟩ := CFSG.Sporadic.Fi24.exists_cls h0
    split_ifs with h1
    · obtain ⟨b, hb⟩ := CFSG.Sporadic.Fi24.exists_cls (hs ⟨1, by omega⟩).1
      rw [hs' 0 (by omega), hs' 1 (by omega), ← ha, ← hb]
      have := (CFSG.Sporadic.Fi24.mem_JR_iff _).1 (cls_mul_cls_mem_JR a b)
      simpa using this
    · obtain ⟨b, hb⟩ := CFSG.Sporadic.Fi24.exists_cls (hs ⟨j, hj⟩).1
      rw [hs' 0 (by omega), hs' j hj, ← ha, ← hb]
      have := (CFSG.Sporadic.Fi24.mem_JR_iff _).1 (cls_mul_cls_mem_JR a b)
      simpa using this
  let m : ℕ → J := fun j => if h : j < k then ⟨_, hmem j h⟩ else 1
  have hm : ∀ j (h : j < k),
      (m j : GL (Fin 781) (ZMod 3)) = CFSG.Sporadic.SchreierLemmas.mooreOfChain s' j := by
    intro j h
    simp only [m, dif_pos h]
  refine ⟨m, ⟨?_, fun j h2 hj => ?_, fun j h2 hj => ?_, fun i j hi hij hj => ?_⟩, ?_, ?_⟩
  · apply Subtype.ext
    change (m 1 : GL (Fin 781) (ZMod 3)) ^ 3 = 1
    rw [hm 1 (by omega)]
    exact hM.cube_one
  · apply Subtype.ext
    change (m j : GL (Fin 781) (ZMod 3)) ^ 2 = 1
    rw [hm j (by omega)]
    exact hM.sq_eq_one j h2 hj
  · apply Subtype.ext
    change ((m (j - 1) : GL (Fin 781) (ZMod 3)) * m j) ^ 3 = 1
    rw [hm (j - 1) (by omega), hm j (by omega)]
    exact hM.cube_adjacent j h2 hj
  · apply Subtype.ext
    change ((m i : GL (Fin 781) (ZMod 3)) * m j) ^ 2 = 1
    rw [hm i (by omega), hm j (by omega)]
    exact hM.sq_distant i j hi hij hj
  · intro h1
    apply CFSG.Sporadic.SchreierLemmas.mooreOfChain_one_ne (s := s') (fun e => (hnc ⟨0, by omega⟩
      ⟨1, by omega⟩ rfl).2 (Subtype.ext (by
        rw [hs' 0 (by omega), hs' 1 (by omega)] at e
        simpa using e)))
    rw [← hm 1 (by omega), h1]
    rfl
  · intro j hj1 hjk
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hm j hjk]
    have h0 : (s ⟨0, by omega⟩ : GL (Fin 781) (ZMod 3)) * w = w * s ⟨0, by omega⟩ := by
      simpa [CFSG.Sporadic.Fi24.coe_jR] using congrArg Subtype.val (hs ⟨0, by omega⟩).2
    have hcomm : ∀ i (hi : i < k), s' i * w = w * s' i := fun i hi => by
      rw [hs' i hi]
      simpa [CFSG.Sporadic.Fi24.coe_jR] using congrArg Subtype.val (hs ⟨i, hi⟩).2
    unfold CFSG.Sporadic.SchreierLemmas.mooreOfChain
    split_ifs with hj1'
    · calc s' 0 * s' 1 * w = s' 0 * (s' 1 * w) := by group
        _ = s' 0 * (w * s' 1) := by rw [hcomm 1 (by omega)]
        _ = (s' 0 * w) * s' 1 := by group
        _ = w * (s' 0 * s' 1) := by rw [hcomm 0 (by omega)]; group
    · calc s' 0 * s' j * w = s' 0 * (s' j * w) := by group
        _ = s' 0 * (w * s' j) := by rw [hcomm j hjk]
        _ = (s' 0 * w) * s' j := by group
        _ = w * (s' 0 * s' j) := by rw [hcomm 0 (by omega)]; group

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Moore

module

public import CFSG.Certificates.Kernel.BabyMonster.DyConjSound
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.BM.Ln

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Pkt
open scoped Matrix

@[expose] def LabInj (x : ℕ) : Prop :=
  LabOK x ∧ ∀ u v : ℕ, u < 4371 → v < 4371 → fld x u % 8192 = fld x v % 8192 → u = v

theorem labInj_labels : LabInj (labels 0 8192) :=
  ⟨labOK_labels, fun u v hu hv h => by
    rw [labels_lo (by omega), labels_lo (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h
    exact h⟩

theorem labInj_letter {Ms : List ℕ} {T NM : ℕ} (hM : MonoOK Ms T NM) {x : ℕ} (hx : LabInj x) :
    LabInj (cjLetter Ms NM x) := by
  obtain ⟨hn, hv, hal⟩ := hM
  obtain ⟨P, Pi, hP, h1, h2, hT, hhi⟩ := mono_net shifts_dyDs hal hn hv
  refine ⟨(labMat_letter ⟨hn, hv, hal⟩ hx.1).1, fun u v hu hv' h => ?_⟩
  have hP43 : ∀ u < 4371, P u < 4371 := by
    intro u hu
    let f : Fin 4371 → Fin 4371 := fun t => ⟨Pi t, (hT t t.2).1⟩
    have hinj : Function.Injective f := fun a b hab => by
      have : Pi a = Pi b := congrArg Fin.val hab
      apply Fin.ext
      rw [← h1 a, ← h1 b, this]
    obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨u, hu⟩
    have : Pi t = u := congrArg Fin.val ht
    rw [← this, h1]
    exact t.2
  have hN := (andB_true (andB_true hn).1).2
  obtain ⟨hNal, hNhi⟩ := negMask_facts hN
  have hmod : ∀ u < 4371, fld (cjLetter Ms NM x) u % 8192 = fld x (P u) % 8192 := by
    intro u hu
    change fld (benes Ms dyDs x ^^^ Nat.land NM (rep 8192 16 4371)) u % 8192 = _
    rw [fld_xor, hP]
    have hxP := (hx.1 (P u) (hP43 u hu)).1
    have hm : fld (Nat.land NM (rep 8192 16 4371)) u = 0 ∨ fld (Nat.land NM (rep 8192 16 4371)) u = 8192 := by
      have hv : fld (Nat.land NM (rep 8192 16 4371)) u = fld NM u &&& (if u < 4371 then 8192 else 0) := by
        change fld (NM &&& rep 8192 16 4371) u = _
        rw [fld_land, fld_rep (by decide)]
      rw [hv]
      rcases hNal u with h0 | h0
      · left
        rw [h0, Nat.zero_and]
      · rw [h0, ite_eq_left (show u < 4371 from hu)]
        right
        decide
    rcases hm with h0 | h0
    · rw [h0, Nat.xor_zero]
    · rw [h0]
      exact (xor_8192 hxP).1
  rw [hmod u hu, hmod v hv'] at h
  have := hx.2 _ _ (hP43 u hu) (hP43 v hv') h
  rw [← h2 u, ← h2 v, this]

theorem labInj_word : ∀ (L : List (List ℕ × ℕ × ℕ)), (∀ l ∈ L, MonoOK l.1 l.2.2 l.2.1) →
    ∀ x, LabInj x → LabInj (cjWord (L.map (·.1)) (L.map (·.2.1)) x)
  | [], _, x, hx => hx
  | l :: L, hL, x, hx => by
    have e : cjWord ((l :: L).map (·.1)) ((l :: L).map (·.2.1)) x =
        cjWord (L.map (·.1)) (L.map (·.2.1)) (cjLetter l.1 l.2.1 x) := by
      change forceB (cjLetter l.1 l.2.1 x) (fun x' => cjWord (L.map (·.1)) (L.map (·.2.1)) x') = _
      rw [forceB_apply]
    rw [e]
    exact labInj_word L (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')) _
      (labInj_letter (hL l (List.mem_cons_self ..)) hx)

theorem labMat_mul_transpose {x : ℕ} (hx : LabInj x) : labMat x * (labMat x)ᵀ = 1 := by
  obtain ⟨hok, hinj⟩ := hx
  let f : Fin 4371 → Fin 4371 := fun u => ⟨fld x u % 8192, (hok u u.2).2⟩
  have hfinj : Function.Injective f := fun a b hab => Fin.ext (hinj a b a.2 b.2 (congrArg Fin.val hab))
  have hfsurj := Finite.injective_iff_surjective.1 hfinj
  ext t t'
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨u0, hu0⟩ := hfsurj t
  have hu0' : fld x u0 % 8192 = t := congrArg Fin.val hu0
  rw [Finset.sum_eq_single u0]
  · simp only [Matrix.transpose_apply]
    unfold labMat
    rw [ite_eq_left hu0']
    by_cases htt : t = t'
    · subst htt
      rw [ite_eq_left hu0', ite_eq_left rfl]
      split <;> norm_num
    · rw [ite_eq_right (fun h => htt (Fin.ext (hu0'.symm.trans h))), ite_eq_right htt, mul_zero]
  · intro u _ hu
    simp only [Matrix.transpose_apply]
    unfold labMat
    rw [ite_eq_right (fun h => hu (hfinj (Fin.ext (h.trans hu0'.symm)))), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] noncomputable def labOf (φ : Fin 4371 → Fin 16384) : Matrix (Fin 4371) (Fin 4371) ℚ := fun t u =>
  if (φ u : ℕ) % 8192 = t then (if (φ u : ℕ) / 8192 = 1 then -1 else 1) else 0

theorem labMat_mem {x : ℕ} (hx : LabOK x) : labMat x ∈ Set.range labOf :=
  ⟨fun u => ⟨fld x u, (hx u u.2).1⟩, rfl⟩

theorem prod_flatten_replicate (L : List (List ℕ × ℕ × ℕ)) (k : ℕ) :
    ((List.replicate k L).flatten.map (fun l => mkMat l.2.2)).prod = ((L.map (fun l => mkMat l.2.2)).prod) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append, ih, pow_succ']

theorem word_pow_eq_one {L : List (List ℕ × ℕ × ℕ)} (hL : ∀ l ∈ L, MonoOK l.1 l.2.2 l.2.1) :
    ∃ k, 1 ≤ k ∧ ((L.map (fun l => mkMat l.2.2)).prod) ^ k = 1 := by
  set U := (L.map (fun l => mkMat l.2.2)).prod
  have hpow : ∀ k, U ^ k = labMat (cjWord ((List.replicate k L).flatten.map (·.1))
      ((List.replicate k L).flatten.map (·.2.1)) (labels 0 8192)) := by
    intro k
    have hk : ∀ l ∈ (List.replicate k L).flatten, MonoOK l.1 l.2.2 l.2.1 := by
      intro l hl
      obtain ⟨M, hM, hl⟩ := List.mem_flatten.1 hl
      rw [(List.eq_of_mem_replicate hM)] at hl
      exact hL l hl
    rw [(labMat_word _ hk _ labOK_labels).2, labMat_labels, Matrix.one_mul, prod_flatten_replicate]
  have hfin : (Set.range labOf).Finite := Set.finite_range labOf
  have hmem : ∀ k, U ^ k ∈ Set.range labOf := fun k => by
    rw [hpow k]
    refine labMat_mem (labMat_word _ ?_ _ labOK_labels).1
    intro l hl
    obtain ⟨M, hM, hl⟩ := List.mem_flatten.1 hl
    rw [(List.eq_of_mem_replicate hM)] at hl
    exact hL l hl
  have : Finite (Set.range labOf) := hfin.to_subtype
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨U ^ k, hmem k⟩ : Set.range labOf))
  have he' : U ^ a = U ^ b := congrArg Subtype.val he
  have hU : IsUnit U := by
    have hinj := labInj_word L hL _ labInj_labels
    have h1 := labMat_mul_transpose hinj
    rw [(labMat_word L hL _ labOK_labels).2, labMat_labels, Matrix.one_mul] at h1
    exact ⟨⟨U, Uᵀ, h1, mul_eq_one_comm.mp h1⟩, rfl⟩
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · refine ⟨b - a, by omega, ?_⟩
    have : U ^ a * U ^ (b - a) = U ^ a * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, he']
    exact (hU.pow a).mul_left_cancel this
  · refine ⟨a - b, by omega, ?_⟩
    have : U ^ b * U ^ (a - b) = U ^ b * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, he']
    exact (hU.pow b).mul_left_cancel this

end CFSG.KC.BM.Ln

end

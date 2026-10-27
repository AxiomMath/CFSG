
module

public import CFSG.Certificates.Kernel.L34Cov.CovSound

public section

namespace CFSG.Certificates.L34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.Fischer
open CFSG.Certificates.CosetEnumeration CFSG.CosetTable CFSG.ComponentClassification.GrSLit.L34Facts
open Subgroup

@[expose] def expOf (j : Fin 2) (w : List (Fin 2 × Bool)) : ℤ :=
  (w.map fun l => if l.1 = j then (if l.2 then (1 : ℤ) else -1) else 0).sum

theorem expOf_cons (j : Fin 2) (l : Fin 2 × Bool) (w : List (Fin 2 × Bool)) :
    expOf j (l :: w) = (if l.1 = j then (if l.2 then (1 : ℤ) else -1) else 0) + expOf j w := by
  rw [expOf, expOf, List.map_cons, List.sum_cons]

variable {G : Type*} [Group G]

theorem zpow_comm_of_mem_center {z : G} (hz : z ∈ center G) (k : ℤ) (g : G) :
    z ^ k * g = g * z ^ k :=
  (mem_center_iff.1 (zpow_mem hz k) g).symm

theorem rearr {z₀ z₁ : G} (h₀ : z₀ ∈ center G) (h₁ : z₁ ∈ center G) (u L : G) (s₀ s₁ a b : ℤ) :
    u * z₀ ^ s₀ * z₁ ^ s₁ * (L * z₀ ^ a * z₁ ^ b) = u * L * z₀ ^ (s₀ + a) * z₁ ^ (s₁ + b) := by
  calc u * z₀ ^ s₀ * z₁ ^ s₁ * (L * z₀ ^ a * z₁ ^ b) =
      u * (z₀ ^ s₀ * (z₁ ^ s₁ * L)) * z₀ ^ a * z₁ ^ b := by simp only [mul_assoc]
    _ = u * (L * z₀ ^ s₀ * z₁ ^ s₁) * z₀ ^ a * z₁ ^ b := by
      rw [zpow_comm_of_mem_center h₁ s₁ L, ← mul_assoc (z₀ ^ s₀) L (z₁ ^ s₁),
        zpow_comm_of_mem_center h₀ s₀ L]
    _ = u * L * z₀ ^ s₀ * (z₁ ^ s₁ * z₀ ^ a) * z₁ ^ b := by simp only [mul_assoc]
    _ = u * L * z₀ ^ s₀ * (z₀ ^ a * z₁ ^ s₁) * z₁ ^ b := by
      rw [← zpow_comm_of_mem_center h₀ a (z₁ ^ s₁)]
    _ = _ := by group

theorem comm_of_inv_mul_mem_center {x y : G} (h : x⁻¹ * y ∈ center G) : x * y = y * x := by
  have e := mem_center_iff.1 h x
  rw [mul_inv_cancel_left] at e
  calc x * y = x * (x⁻¹ * y * x) := congrArg (x * ·) e
    _ = y * x := by group

theorem inv_eq_conj_of_comm {x y : G} (h : x * y = y * x) : y⁻¹ = x⁻¹ * (y⁻¹ * x) := by
  have hc : x * y⁻¹ = y⁻¹ * x := (Commute.inv_right (show Commute x y from h)).eq
  calc y⁻¹ = x⁻¹ * (x * y⁻¹) := by group
    _ = x⁻¹ * (y⁻¹ * x) := by rw [hc]

theorem lift_eq_corr (x y : Fin 2 → G) (h₀ : (x 0)⁻¹ * y 0 ∈ center G)
    (h₁ : (x 1)⁻¹ * y 1 ∈ center G) (w : List (Fin 2 × Bool)) :
    FreeGroup.lift y (FreeGroup.mk w) = FreeGroup.lift x (FreeGroup.mk w) *
      ((x 0)⁻¹ * y 0) ^ expOf 0 w * ((x 1)⁻¹ * y 1) ^ expOf 1 w := by
  induction w with
  | nil => simp [expOf]
  | cons l w ih =>
    have hm : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := by
      rw [FreeGroup.mul_mk]
      rfl
    have hl : FreeGroup.lift y (FreeGroup.mk [l]) = FreeGroup.lift x (FreeGroup.mk [l]) *
        ((x 0)⁻¹ * y 0) ^ (if l.1 = 0 then (if l.2 then (1 : ℤ) else -1) else 0) *
        ((x 1)⁻¹ * y 1) ^ (if l.1 = 1 then (if l.2 then (1 : ℤ) else -1) else 0) := by
      obtain ⟨j, b⟩ := l
      have hof : ∀ (f : Fin 2 → G), FreeGroup.lift f (FreeGroup.mk [(j, b)]) =
          if b then f j else (f j)⁻¹ := by
        intro f
        cases b
        · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv,
            FreeGroup.lift_apply_of]
          rfl
        · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl, FreeGroup.lift_apply_of]
          rfl
      rw [hof, hof]
      have c₀ := comm_of_inv_mul_mem_center h₀
      have c₁ := comm_of_inv_mul_mem_center h₁
      fin_cases j <;> cases b <;> simp (config := { decide := true }) only [Fin.zero_eta,
        Fin.mk_one, Fin.isValue, ↓reduceIte, Bool.false_eq_true, zpow_zero, mul_one,
        zpow_one, zpow_neg_one, mul_inv_rev, inv_inv, mul_inv_cancel_left]
      all_goals first
        | exact inv_eq_conj_of_comm c₀
        | exact inv_eq_conj_of_comm c₁
        | group
    rw [hm, map_mul, map_mul, hl, ih, expOf_cons, expOf_cons]
    exact rearr h₀ h₁ _ _ _ _ _ _

theorem lift_eq_of_mem_commutator (x y : Fin 2 → G) (h : ∀ j, (x j)⁻¹ * y j ∈ center G)
    {f : FreeGroup (Fin 2)} (hf : f ∈ commutator (FreeGroup (Fin 2))) :
    FreeGroup.lift y f = FreeGroup.lift x f := by
  refine eq_of_mem_commutator_of_central (QuotientGroup.mk' (center G)) ?_ _ _ ?_ hf
  · rw [QuotientGroup.ker_mk']
  · refine FreeGroup.ext_hom _ _ fun j => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have e := inv_mem (h j)
    rwa [mul_inv_rev, inv_inv] at e

theorem mem_center_of_rowsOK {V : ℕ} (hV : vtOK V = true)
    {w : List (Fin 2 × Bool)} {c : ℕ} (h : rowsOK V (w.map letterCode) (lamC c) = true) :
    cv w ∈ center Cover := by
  have hP := pSL_cv_of_rowsOK hV h
  have hk : cv w * (z₃ ^ c)⁻¹ ∈ center Cover := by
    apply ker_piX_le_center
    apply ker_pSL_le_ker_piX
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hP, mul_inv_cancel]
  have e : cv w = cv w * (z₃ ^ c)⁻¹ * z₃ ^ c := by group
  rw [e]
  exact mul_mem hk (pow_mem z₃_mem_center c)

theorem lift_cv_getD (hs : List (List (Fin 2 × Bool))) (w : List (Fin 2 × Bool)) :
    FreeGroup.lift (fun j : Fin 2 => cv (hs.getD j [])) (FreeGroup.mk w) = cv (substWord hs w) :=
  lift_substWord hs w

theorem exists_alphaHom (uA uB : List (Fin 2 × Bool))
    (hA : (cv uA)⁻¹ * cv ((autWs uA uB).getD 0 []) ∈ center Cover)
    (hB : (cv uB)⁻¹ * cv ((autWs uA uB).getD 1 []) ∈ center Cover)
    (hR : ∀ r ∈ rels, cv (substWord [uA, uB] r) ∈ center Cover)
    (hX : ∀ e ∈ extraWs, cv (substWord [uA, uB] e) *
      ((cv uA)⁻¹ * cv ((autWs uA uB).getD 0 [])) ^ expOf 0 e *
      ((cv uB)⁻¹ * cv ((autWs uA uB).getD 1 [])) ^ expOf 1 e = 1) :
    ∃ α : Cover →* Cover, (∀ w, α (cv w) = cv (substWord (autWs uA uB) w)) ∧
      ∀ w, α (cv w) = cv (substWord [uA, uB] w) *
        ((cv uA)⁻¹ * cv ((autWs uA uB).getD 0 [])) ^ expOf 0 w *
        ((cv uB)⁻¹ * cv ((autWs uA uB).getD 1 [])) ^ expOf 1 w := by
  set x : Fin 2 → Cover := fun j => cv ([uA, uB].getD j []) with hx
  set y : Fin 2 → Cover := fun j => cv ((autWs uA uB).getD j []) with hy
  have hc : ∀ j, (x j)⁻¹ * y j ∈ center Cover := by
    intro j
    fin_cases j
    · exact hA
    · exact hB
  have hcorr : ∀ w, FreeGroup.lift y (FreeGroup.mk w) = cv (substWord [uA, uB] w) *
      ((cv uA)⁻¹ * cv ((autWs uA uB).getD 0 [])) ^ expOf 0 w *
      ((cv uB)⁻¹ * cv ((autWs uA uB).getD 1 [])) ^ expOf 1 w := by
    intro w
    rw [lift_eq_corr x y (hc 0) (hc 1) w, hx, lift_cv_getD [uA, uB] w]
    rfl
  have hrel : ∀ r ∈ wordSet coverWs, FreeGroup.lift y r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hw
        obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hi
        rw [mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        have hz : FreeGroup.lift y (FreeGroup.mk r') ∈ center Cover := by
          rw [hcorr]
          refine mul_mem (mul_mem (hR r' hr') (zpow_mem hA _)) (zpow_mem hB _)
        exact mem_center_iff.1 hz _
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hw
        have hi : substWord [uA, uB] (commWords (coverPairs i)) = (autWs uA uB).getD i [] := by
          fin_cases i <;> rfl
        rw [← List.singleton_append, ← FreeGroup.mul_mk, map_mul,
          lift_eq_of_mem_commutator x y hc (mk_commWords_mem_commutator _), hx,
          lift_cv_getD [uA, uB] (commWords (coverPairs i)), hi,
          show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of]
        exact inv_mul_cancel _
    · rw [hcorr]
      exact hX w hw
  refine ⟨PresentedGroup.toGroup hrel, fun w => ?_, fun w => ?_⟩
  · change FreeGroup.lift y (FreeGroup.mk w) = _
    rw [hy, lift_cv_getD (autWs uA uB) w]
  · change FreeGroup.lift y (FreeGroup.mk w) = _
    exact hcorr w

end CFSG.Certificates.L34Cov

end

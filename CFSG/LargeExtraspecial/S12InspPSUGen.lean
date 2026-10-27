module

public import CFSG.Fischer.Classification.Unitary.Model
import all CFSG.Fischer.F4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

namespace S12InspPSU

open CFSG.Fischer CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

namespace Gen4

def pt (a b c d : Fin 4) : Fin 4 → F4 := ![⟨a⟩, ⟨b⟩, ⟨c⟩, ⟨d⟩]

def hF (x y : Fin 4 → F4) : F4 :=
  x 0 * x 0 * y 0 + x 1 * x 1 * y 1 + x 2 * x 2 * y 2 + x 3 * x 3 * y 3

def tvF (a x : Fin 4 → F4) : Fin 4 → F4 := fun i => x i + hF a x * a i

def fnz (v : Fin 4 → F4) : F4 :=
  if v 0 ≠ 0 then v 0 else if v 1 ≠ 0 then v 1 else if v 2 ≠ 0 then v 2 else v 3

def nf (v : Fin 4 → F4) : Fin 4 → F4 := fun i => fnz v * fnz v * v i

def P : Fin 45 → Fin 4 → F4 := ![pt 1 1 0 0, pt 0 0 1 1, pt 1 1 1 1, pt 0 0 1 2,
  pt 0 1 1 0, pt 1 0 1 0, pt 0 0 1 3, pt 0 1 0 1, pt 1 1 3 2, pt 0 1 0 2, pt 1 0 0 1,
  pt 1 0 0 2, pt 1 1 2 3, pt 0 1 2 0, pt 1 3 1 2, pt 0 1 3 0, pt 0 1 0 3, pt 1 0 0 3,
  pt 1 2 2 3, pt 1 2 3 1, pt 1 0 2 0, pt 1 0 3 0, pt 1 3 2 3, pt 1 3 2 1, pt 1 2 3 2,
  pt 1 2 1 3, pt 1 3 3 2, pt 1 3 0 0, pt 1 2 0 0, pt 1 3 2 2, pt 1 3 3 3, pt 1 2 1 1,
  pt 1 2 2 2, pt 1 2 3 3, pt 1 3 1 1, pt 1 3 1 3, pt 1 1 3 3, pt 1 1 2 1, pt 1 1 2 2,
  pt 1 2 2 1, pt 1 3 3 1, pt 1 1 1 2, pt 1 1 3 1, pt 1 1 1 3, pt 1 2 1 2]

def par : Fin 45 → Fin 45 × Fin 45 := ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
  (0, 4), (1, 3), (1, 4), (2, 3), (3, 4), (0, 7), (0, 9), (1, 8), (1, 9), (2, 9), (3, 7),
  (4, 6), (5, 6), (5, 8), (7, 8), (0, 13), (0, 15), (0, 19), (1, 14), (1, 18), (1, 19),
  (2, 17), (5, 13), (5, 15), (5, 19), (6, 14), (6, 18), (6, 19), (10, 14), (11, 12),
  (11, 19), (13, 18), (14, 17), (17, 19), (0, 35), (1, 35), (1, 37), (2, 37), (3, 38),
  (4, 38)]

set_option maxRecDepth 4000 in
theorem check_par : ∀ k : Fin 45, 5 ≤ k.val →
    (par k).1 < k ∧ (par k).2 < k ∧ tvF (P (par k).1) (P (par k).2) ≠ 0 ∧
      nf (tvF (P (par k).1) (P (par k).2)) = P k := by
  decide

set_option maxRecDepth 4000 in
theorem check_P : ∀ k : Fin 45, P k ≠ 0 ∧ hF (P k) (P k) = 0 := by
  decide

set_option maxRecDepth 4000 in
theorem check_complete : ∀ a b c d : F4, ![a, b, c, d] ≠ 0 →
    hF ![a, b, c, d] ![a, b, c, d] = 0 → ∃ k : Fin 45, nf ![a, b, c, d] = P k := by
  decide

set_option maxRecDepth 4000 in
theorem check_nf : ∀ a b c d : F4, ![a, b, c, d] ≠ 0 →
    fnz ![a, b, c, d] ≠ 0 ∧ ∀ i, fnz ![a, b, c, d] * nf ![a, b, c, d] i = ![a, b, c, d] i := by
  decide

theorem check_orth : ∀ i j : Fin 45, i.val < 3 → j.val < 3 → hF (P i) (P j) = 0 := by
  decide

theorem eta (v : Fin 4 → F4) : v = ![v 0, v 1, v 2, v 3] := by
  funext i
  fin_cases i <;> rfl

noncomputable def toK (x : Fin 4 → F4) : Fin 4 → K := fun i => eF4 (x i)

theorem herm_toK (x y : Fin 4 → F4) : herm frob (toK x) (toK y) = eF4 (hF x y) := by
  rw [herm_def, Fin.sum_univ_four]
  simp only [toK, frob_eF4, hF, map_add, map_mul, sq]

theorem toK_ne_zero {x : Fin 4 → F4} (hx : x ≠ 0) : toK x ≠ 0 := by
  intro h
  apply hx
  funext i
  have := congrFun h i
  simp only [toK, Pi.zero_apply] at this
  rw [Pi.zero_apply, ← eF4.injective.eq_iff, this, map_zero]

theorem toK_smul (c : F4) (x : Fin 4 → F4) : toK (fun i => c * x i) = eF4 c • toK x := by
  funext i
  simp [toK]

theorem tvU_toK {a : Fin 4 → F4} (ha : hF a a = 0) (x : Fin 4 → F4) :
    tvU (toK a) • toK x = toK (tvF a x) := by
  have ha' : herm frob (toK a) (toK a) = 0 := by rw [herm_toK, ha, map_zero]
  rw [tvU_smul ha', herm_toK]
  funext i
  simp [toK, tvF]

theorem tq_toK_nf {v : Fin 4 → F4} (hv0 : v ≠ 0) (hv : hF v v = 0) :
    tq (toK (nf v)) = tq (toK v) := by
  rw [eta v] at hv0 hv ⊢
  obtain ⟨h0, h1⟩ := check_nf _ _ _ _ hv0
  have e : toK ![v 0, v 1, v 2, v 3] = eF4 (fnz ![v 0, v 1, v 2, v 3]) •
      toK (nf ![v 0, v 1, v 2, v 3]) := by
    rw [← toK_smul]
    exact congrArg toK (funext fun i => (h1 i).symm)
  have hnf : herm frob (toK (nf ![v 0, v 1, v 2, v 3])) (toK (nf ![v 0, v 1, v 2, v 3])) = 0 := by
    have h2 : herm frob (toK ![v 0, v 1, v 2, v 3]) (toK ![v 0, v 1, v 2, v 3]) = 0 := by
      rw [herm_toK, hv, map_zero]
    rw [e, herm_smul_left, herm_smul_right] at h2
    have hc : eF4 (fnz ![v 0, v 1, v 2, v 3]) ≠ 0 := by
      rw [Ne, ← map_zero eF4, eF4_inj]
      exact h0
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (frob_ne_zero hc))).resolve_left hc
  rw [e, tq, tq, tvU_smul_vec hnf]
  rw [Ne, ← map_zero eF4, eF4_inj]
  exact h0

end Gen4

open Gen4

noncomputable def gen4 (i : Fin 5) : Fin 4 → K := toK (P (Fin.castLE (by norm_num) i))

theorem gen4_ne_zero (i : Fin 5) : gen4 i ≠ 0 := toK_ne_zero (check_P _).1

theorem herm_gen4_self (i : Fin 5) : herm frob (gen4 i) (gen4 i) = 0 := by
  rw [gen4, herm_toK, (check_P _).2, map_zero]

theorem herm_gen4_gen4 {i j : Fin 5} (hi : i.val < 3) (hj : j.val < 3) :
    herm frob (gen4 i) (gen4 j) = 0 := by
  rw [gen4, gen4, herm_toK, check_orth _ _ hi hj, map_zero]

theorem tq_P_mem (k : Fin 45) :
    tq (toK (P k)) ∈ Subgroup.closure (Set.range fun i => tq (gen4 i)) := by
  set H := Subgroup.closure (Set.range fun i => tq (gen4 i)) with hH
  suffices h : ∀ n (hn : n < 45), tq (toK (P ⟨n, hn⟩)) ∈ H from h k.val k.2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  by_cases h5 : n < 5
  · exact Subgroup.subset_closure ⟨⟨n, h5⟩, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := check_par ⟨n, hn⟩ (by simp only; omega)
  set i := (par ⟨n, hn⟩).1
  set j := (par ⟨n, hn⟩).2
  have hi : tq (toK (P i)) ∈ H := ih i.val h1 i.2
  have hj : tq (toK (P j)) ∈ H := ih j.val h2 j.2
  have hPi := (check_P i).2
  have hPj := (check_P j).2
  have hiso : hF (tvF (P i) (P j)) (tvF (P i) (P j)) = 0 := by
    have e := herm_smul_smul frob (tvU (toK (P i))) (toK (P j)) (toK (P j))
    rw [tvU_toK hPi, herm_toK, herm_toK, hPj, eF4_inj] at e
    exact e
  rw [← h4, tq_toK_nf h3 hiso, ← tvU_toK hPi,
    ← tq_mul_tq_mul_tq (by rw [herm_toK, hPi, map_zero]) (by rw [herm_toK, hPj, map_zero])]
  exact H.mul_mem (H.mul_mem hi hj) hi

theorem closure_gen4 :
    Subgroup.closure (Set.range fun i => tq (gen4 i)) = (⊤ : Subgroup (PG 4)) := by
  rw [eq_top_iff, ← closure_DG le_rfl, Subgroup.closure_le]
  rintro _ ⟨v, hv0, hv, rfl⟩
  set v' : Fin 4 → F4 := fun i => eF4.symm (v i) with hv'
  have hvv : toK v' = v := funext fun i => eF4.apply_symm_apply (v i)
  have hv'0 : v' ≠ 0 := by
    rintro h
    apply hv0
    rw [← hvv, h]
    funext i
    simp [toK]
  have hv'iso : hF v' v' = 0 := by
    have := hv
    rw [← hvv, herm_toK, ← map_zero eF4, eF4_inj] at this
    exact this
  have hv'0' := hv'0
  rw [eta v'] at hv'0' hv'iso
  obtain ⟨k, hk⟩ := check_complete _ _ _ _ hv'0' hv'iso
  rw [← eta v'] at hk hv'iso
  rw [← hvv, ← tq_toK_nf hv'0 hv'iso, hk]
  exact tq_P_mem k

end S12InspPSU

end CFSG.LargeExtraspecial

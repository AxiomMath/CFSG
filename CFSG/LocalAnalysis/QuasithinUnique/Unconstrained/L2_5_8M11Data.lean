module

public import CFSG.Sporadic.Schreier.M11Data
public meta import CFSG.Sporadic.Schreier.M11Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8M11DataInputs
public import Certificates.Certificate4154

public section

namespace CFSG.QuasithinUnique.Unc25M11

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

theorem pw_eq (l : List ℕ) :
    pw l = (l.map fun i => if i = 0 then m11gA else m11gB).prod :=
  tab_eq _

theorem pw_mem (l : List ℕ) : pw l ∈ CFSG.Blueprint.NativeSporadic.M11 := by
  rw [pw_eq]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact m11a.2
  · exact m11b.2

theorem mem_P0L_iff {x : Equiv.Perm (Fin 11)} :
    x ∈ P0L ↔ ∃ i < 8, ∃ j < 2, x = sa ^ i * sb ^ j := by
  simp only [P0L, List.mem_flatMap, List.mem_range, List.mem_map, tab_eq]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩

theorem sa_pow : sa ^ 8 = 1 := by decide +kernel

theorem sa_pow_four_ne : sa ^ 4 ≠ 1 := by decide +kernel

theorem sb_sq : sb * sb = 1 := by decide +kernel

theorem sb_conj : sb * sa * sb⁻¹ = sa ^ 3 := by decide +kernel

theorem P0L_nodup : P0L.Nodup := by decide +kernel

theorem P0L_length : P0L.length = 16 := by decide +kernel

theorem one_mem_P0L : (1 : Equiv.Perm (Fin 11)) ∈ P0L := by decide +kernel

theorem mul_mem_P0L_check : P0L.all (fun x => P0L.all fun y => decide (x * y ∈ P0L)) = true := by
  decide +kernel

theorem inv_mem_P0L_check : P0L.all (fun x => decide (x⁻¹ ∈ P0L)) = true := by decide +kernel

theorem mul_mem_P0L : ∀ x ∈ P0L, ∀ y ∈ P0L, x * y ∈ P0L := fun x hx y hy =>
  of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp mul_mem_P0L_check x hx) y hy)

theorem inv_mem_P0L : ∀ x ∈ P0L, x⁻¹ ∈ P0L := fun x hx =>
  of_decide_eq_true (List.all_eq_true.mp inv_mem_P0L_check x hx)

theorem sa_mem_P0L : sa ∈ P0L := by decide +kernel

theorem sb_mem_P0L : sb ∈ P0L := by decide +kernel

@[expose] def W3 : List (Equiv.Perm (Fin 11)) :=
  [pw [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    pw [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]]

theorem W3_mem : ∀ w ∈ W3, w ∈ CFSG.Blueprint.NativeSporadic.M11 := by
  intro w hw
  simp only [W3, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> exact pw_mem _

theorem W3_check_bool : invsP0.all (fun t => invsP0.all fun s =>
    decide (t ≠ s → t * s = s * t → W3.any (fun w => decide (w ^ 3 = 1 ∧ w ≠ 1 ∧
      w * t * w⁻¹ ∈ [1, t, s, t * s] ∧ w * s * w⁻¹ ∈ [1, t, s, t * s])) = true)) = true := by
  decide +kernel

theorem W3_check : ∀ t ∈ invsP0, ∀ s ∈ invsP0, t ≠ s → t * s = s * t →
    ∃ w ∈ W3, w ^ 3 = 1 ∧ w ≠ 1 ∧ w * t * w⁻¹ ∈ [1, t, s, t * s] ∧
      w * s * w⁻¹ ∈ [1, t, s, t * s] := by
  intro t ht s hs hts hcomm
  have h := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp W3_check_bool t ht) s hs)
    hts hcomm
  obtain ⟨w, hw, hw'⟩ := List.any_eq_true.mp h
  exact ⟨w, hw, of_decide_eq_true hw'⟩

theorem normProp_check :
    m11Elements.all (fun g => decide (NormProp g)) = true :=
  Certificates.certificate4154.1

@[expose] def CentProp (g : Equiv.Perm (Fin 11)) : Prop :=
  ∀ t ∈ invsP0, ∀ s ∈ invsP0, g * t = t * g → g * s = s * g → t ≠ s → t * s = s * t →
    g = 1 ∨ g = t ∨ g = s ∨ g = t * s

theorem centProp_of_centB {g : Equiv.Perm (Fin 11)} (h : centB g = true) : CentProp g := by
  intro t ht s hs h1 h2 h3 h4
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h t ht) s hs) h1 h2 h3 h4

theorem centB_check : m11Elements.all centB = true :=
  Certificates.certificate4154.2

end CFSG.QuasithinUnique.Unc25M11

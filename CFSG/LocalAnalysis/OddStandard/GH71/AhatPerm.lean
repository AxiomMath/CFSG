module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataPerm
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.OddStandard.GH71.AhatB

open Equiv Equiv.Perm Subgroup CFSG.OddStandard.Solomon75.AhatData

@[expose] def g1 : Perm (Fin 11) := swap 6 7 * swap 8 9

@[expose] def g2 : Perm (Fin 11) := swap 4 6 * swap 5 7

@[expose] def g3 : Perm (Fin 11) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

@[expose] def u0 : Perm (Fin 11) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def e2 : Perm (Fin 11) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7

@[expose] def t3 : Perm (Fin 11) := swap 8 9 * swap 9 10

@[expose] def h23 : Perm (Fin 11) := swap 2 3 * swap 8 9

@[expose] def sB : Perm (Fin 11) := swap 0 1 * swap 4 6 * swap 5 7 * swap 8 9

@[expose] def d02 : Perm (Fin 11) := swap 0 2 * swap 1 3

@[expose] def d01 : Perm (Fin 11) := swap 0 1 * swap 2 3

@[expose] def h01 : Perm (Fin 11) := swap 0 1 * swap 8 9

@[expose] def h45 : Perm (Fin 11) := swap 4 5 * swap 8 9

@[expose] def xo : Fin 8 → Perm (Fin 11) :=
  ![1, u0, e2, u0 * e2, g3, u0 * g3, e2 * g3, u0 * e2 * g3]

theorem g1_mem : g1 ∈ P0 11 := by
  refine subset_closure (show g1 ∈ genPerms 11 from ?_)
  rw [show g1 = swapsPerm 11 [(6, 7), (8, 9)] by decide]
  exact List.mem_map_of_mem (by decide)

theorem g2_mem : g2 ∈ P0 11 := by
  refine subset_closure (show g2 ∈ genPerms 11 from ?_)
  rw [show g2 = swapsPerm 11 [(4, 6), (5, 7)] by decide]
  exact List.mem_map_of_mem (by decide)

theorem g3_mem : g3 ∈ P0 11 := by
  refine subset_closure (show g3 ∈ genPerms 11 from ?_)
  rw [show g3 = swapsPerm 11 [(0, 4), (1, 5), (2, 6), (3, 7)] by decide]
  exact List.mem_map_of_mem (by decide)

theorem h23_mem : h23 ∈ P0 11 := by
  rw [show h23 = g3 * g1 * g3 by decide]
  exact mul_mem (mul_mem g3_mem g1_mem) g3_mem

theorem h01_mem : h01 ∈ P0 11 := by
  rw [show h01 = g3 * g2 * g1 * g2 * g3 by decide]
  exact mul_mem (mul_mem (mul_mem (mul_mem g3_mem g2_mem) g1_mem) g2_mem) g3_mem

theorem h45_mem : h45 ∈ P0 11 := by
  rw [show h45 = g2 * g1 * g2 by decide]
  exact mul_mem (mul_mem g2_mem g1_mem) g2_mem

theorem d02_mem : d02 ∈ P0 11 := by
  rw [show d02 = g3 * g2 * g3 by decide]
  exact mul_mem (mul_mem g3_mem g2_mem) g3_mem

theorem d01_mem : d01 ∈ P0 11 := by
  rw [show d01 = h01 * h23 by decide]
  exact mul_mem h01_mem h23_mem

theorem u0_mem : u0 ∈ P0 11 := by
  rw [show u0 = h01 * h23 * h45 * g1 by decide]
  exact mul_mem (mul_mem (mul_mem h01_mem h23_mem) h45_mem) g1_mem

theorem e2_mem : e2 ∈ P0 11 := by
  rw [show e2 = d02 * g2 by decide]
  exact mul_mem d02_mem g2_mem

theorem sB_mem : sB ∈ P0 11 := by
  rw [show sB = h01 * g2 by decide]
  exact mul_mem h01_mem g2_mem

theorem xo_mem (k : Fin 8) : xo k ∈ P0 11 := by
  fin_cases k
  · exact one_mem _
  · exact u0_mem
  · exact e2_mem
  · exact mul_mem u0_mem e2_mem
  · exact g3_mem
  · exact mul_mem u0_mem g3_mem
  · exact mul_mem e2_mem g3_mem
  · exact mul_mem (mul_mem u0_mem e2_mem) g3_mem

theorem comm_u0_of_mem {p : Perm (Fin 11)} (hp : p ∈ P0 11) : p * u0 = u0 * p := by
  have hle : P0 11 ≤ centralizer ({u0} : Set (Perm (Fin 11))) := by
    rw [P0, closure_le]
    intro σ hσ
    obtain ⟨sw, hsw, rfl⟩ := List.mem_map.1 (show σ ∈ genPerms 11 from hσ)
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    revert sw
    decide
  exact mem_centralizer_singleton_iff.1 (hle hp)

theorem xo_zero (k : Fin 8) : xo k 0 = Fin.castLE (by norm_num) k := by
  revert k
  decide

theorem fix_u0 : ∀ y : Fin 11, u0 y = y → y = 8 ∨ y = 9 ∨ y = 10 := by decide

theorem lt_of_u0_ne : ∀ y : Fin 11, u0 y ≠ y → y.val < 8 := by decide

theorem u0_ne_of_lt : ∀ y : Fin 11, y.val < 8 → u0 y ≠ y := by decide

theorem sign_u0 : sign u0 = 1 := by decide

theorem isoI_u0 : IsoI u0 := by
  unfold IsoI
  decide

theorem e8_witness :
    ∃ a b c : Perm (Fin 11), IsoI a ∧ IsoI b ∧ IsoI c ∧ Indep2 a b ∧ Indep3 a b c := by
  refine ⟨u0, e2, g3, ?_⟩
  unfold IsoI Indep2 Indep3 IsoI
  decide

theorem xo_isoI : ∀ k : Fin 8, 2 ≤ k.val →
    IsoI (xo k) ∧ IsoI (xo k * u0) ∧ xo k * u0 = u0 * xo k := by
  unfold IsoI
  decide

theorem xo_ne : ∀ k : Fin 8, k ≠ 0 → ∀ y : Fin 11, y.val < 8 → xo k y ≠ y := by decide

theorem xo_sq : ∀ k : Fin 8, xo k * xo k = 1 := by decide

theorem xo_self : ∀ k : Fin 8, xo k (Fin.castLE (by norm_num) k) = 0 := by decide

end CFSG.OddStandard.GH71.AhatB

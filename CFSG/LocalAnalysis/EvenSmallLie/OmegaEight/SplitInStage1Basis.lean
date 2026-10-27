module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1Comm

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1
open CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

namespace SetupX

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}
  {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hZ : ∀ v, v ∈ Zset t Q ψ)
include hS hZ

@[expose] noncomputable def dB [Finite G] (j : ℕ) : G :=
  Classical.choose (hS.tauD_surjective hZ (basisVec j))

theorem dB_mem [Finite G] (j : ℕ) : hS.dB hZ j ∈ Dsub t Q :=
  (Classical.choose_spec (hS.tauD_surjective hZ (basisVec j))).1

theorem tauD_dB [Finite G] (j : ℕ) : tauD t ψ (hS.dB hZ j) = basisVec j :=
  (Classical.choose_spec (hS.tauD_surjective hZ (basisVec j))).2

@[expose] noncomputable def dV [Finite G] (v : V6) : G :=
  ((List.finRange 6).map fun j => if v j = 1 then hS.dB hZ j else 1).prod

theorem tauD_list_prod {l : List G} (hl : ∀ x ∈ l, x ∈ Dsub t Q) :
    l.prod ∈ Dsub t Q ∧ tauD t ψ l.prod = (l.map (tauD t ψ)).sum := by
  induction l with
  | nil =>
    exact ⟨one_mem _, by simpa using (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _)⟩
  | cons x l ih =>
    have hx := hl x List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    refine ⟨by rw [List.prod_cons]; exact mul_mem hx h1, ?_⟩
    rw [List.prod_cons, hS.tauD_mul hZ hx h1, h2, List.map_cons, List.sum_cons]

theorem dV_mem [Finite G] (v : V6) : hS.dV hZ v ∈ Dsub t Q := by
  refine (hS.tauD_list_prod hZ fun x hx => ?_).1
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact hS.dB_mem hZ j
  · exact one_mem _

theorem tauD_dV [Finite G] (v : V6) : tauD t ψ (hS.dV hZ v) = v := by
  rw [dV, (hS.tauD_list_prod hZ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    split_ifs
    · exact hS.dB_mem hZ j
    · exact one_mem _).2, List.map_map, ← Fin.sum_univ_def]
  conv_rhs => rw [eq_sum_basisVec v]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (v j) with h | h
  · simp only [h, zero_smul, show ¬ (0 : ZMod 2) = 1 by decide, ite_false]
    exact (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _)
  · simp only [h, one_smul, ite_true, hS.tauD_dB hZ]

theorem kap_list_left {l : List G} (hl : ∀ x ∈ l, x ∈ Dsub t Q) {y : G} (hy : y ∈ Dsub t Q) :
    kap l.prod y = (l.map fun x => kap x y).prod := by
  induction l with
  | nil => simp [kap]
  | cons x l ih =>
    have hx := hl x List.mem_cons_self
    have hl' : ∀ z ∈ l, z ∈ Dsub t Q := fun z hz => hl z (List.mem_cons_of_mem _ hz)
    rw [List.prod_cons, hS.kap_mul_left hZ hx (hS.tauD_list_prod hZ hl').1 hy, ih hl',
      List.map_cons, List.prod_cons]

theorem dV_list_mem [Finite G] (v : V6) :
    ∀ x ∈ (List.finRange 6).map (fun j => if v j = 1 then hS.dB hZ j else 1), x ∈ Dsub t Q := by
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact hS.dB_mem hZ j
  · exact one_mem _

theorem coord_kap_dV_left [Finite G] (u : V6) {z : G} (hz : z ∈ Dsub t Q) :
    coord ψ (kap (hS.dV hZ u) z) = ∑ x : Fin 6, u x • coord ψ (kap (hS.dB hZ x) z) := by
  have hl : ∀ y ∈ ((List.finRange 6).map (fun j => if u j = 1 then hS.dB hZ j else 1)).map
      (fun x => kap x z), y ∈ Q := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hS.kap_mem_Q hZ (hS.dV_list_mem hZ u x hx) hz
  rw [dV, hS.kap_list_left hZ (hS.dV_list_mem hZ u) hz, (hS.rad.coord_list_prod hl).2,
    List.map_map, List.map_map, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (u j) with h | h
  · simp only [h, zero_smul, show ¬ (0 : ZMod 2) = 1 by decide, ite_false]
    rw [Setup.kap_Q_left (one_mem _) hz, hS.rad.coord_one]
  · simp only [h, one_smul, ite_true]

theorem coord_kap_dV_right [Finite G] (u : V6) {z : G} (hz : z ∈ Dsub t Q) :
    coord ψ (kap z (hS.dV hZ u)) = ∑ y : Fin 6, u y • coord ψ (kap z (hS.dB hZ y)) := by
  rw [hS.kap_symm hZ (hS.dV_mem hZ u) hz, hS.coord_kap_dV_left hZ u hz]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hS.kap_symm hZ hz (hS.dB_mem hZ y)]

theorem coord_kap_dV [Finite G] (u u' : V6) :
    coord ψ (kap (hS.dV hZ u) (hS.dV hZ u')) =
      ∑ x : Fin 6, ∑ y : Fin 6, (u x * u' y) • coord ψ (kap (hS.dB hZ x) (hS.dB hZ y)) := by
  rw [hS.coord_kap_dV_left hZ u (hS.dV_mem hZ u')]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hS.coord_kap_dV_right hZ u' (hS.dB_mem hZ x), Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_smul]

end SetupX

end CFSG.EvenSmallLie.OmegaEight.SplitIn

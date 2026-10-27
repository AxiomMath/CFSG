module

public import CFSG.LocalAnalysis.OddStandard.ONanFusBase
public import CFSG.LocalAnalysis.OddStandard.ONanFusThompson

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem inClass_fus {i j : Fin 7} {x y : G} (hx : D.InClass i x) (hy : D.InClass j y) (g : G)
    (hg : g⁻¹ * x * g = y) : D.Fus i j := by
  obtain ⟨c, -, rfl⟩ := hx
  obtain ⟨c', -, rfl⟩ := hy
  refine ⟨c * g * c'⁻¹, ?_⟩
  calc (c * g * c'⁻¹)⁻¹ * invRep v1 v2 v3 s t i * (c * g * c'⁻¹)
      = c' * (g⁻¹ * (c⁻¹ * invRep v1 v2 v3 s t i * c) * g) * c'⁻¹ := by group
    _ = c' * (c'⁻¹ * invRep v1 v2 v3 s t j * c') * c'⁻¹ := by rw [hg]
    _ = invRep v1 v2 v3 s t j := by group

theorem not_two_dvd_index_P : ¬ 2 ∣ (alpP v1 v2 v3 s t).index := by
  rw [← D.hP]
  exact D.P.not_dvd_index

theorem rep_sq (i : Fin 7) : invRep v1 v2 v3 s t i * invRep v1 v2 v3 s t i = 1 :=
  (AlpEmb.invRep_sq D.E D.hF i).1

theorem rep_ne_one (i : Fin 7) : invRep v1 v2 v3 s t i ≠ 1 :=
  (AlpEmb.invRep_sq D.E D.hF i).2

theorem orderOf_rep (i : Fin 7) : orderOf (invRep v1 v2 v3 s t i) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact D.rep_sq i) (D.rep_ne_one i)

theorem thompson_row (r i : Fin 7) : ∃ j : Fin 7, maxTable r j = true ∧ D.Fus i j := by
  have hcard : Nat.card (alpP v1 v2 v3 s t) =
      Nat.card (closure {g : G | g ∈ genMax v1 v2 v3 s t r}) * 2 ^ 1 := by
    rw [AlpEmb.card_alpP D.E, AlpEmb.card_genMax D.E D.hF r]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_mem_of_cyclic_complement
    D.noIdx D.not_two_dvd_index_P (r := invRep v1 v2 v3 s t i) (k := 1)
    le_rfl (by rw [pow_one]; exact D.orderOf_rep i) hcard
  rw [Nat.sub_self, pow_zero, pow_one] at hg
  set u := g⁻¹ * invRep v1 v2 v3 s t i * g with hu
  have hu2 : u * u = 1 := by
    rw [hu]
    calc g⁻¹ * invRep v1 v2 v3 s t i * g * (g⁻¹ * invRep v1 v2 v3 s t i * g)
        = g⁻¹ * (invRep v1 v2 v3 s t i * invRep v1 v2 v3 s t i) * g := by group
      _ = 1 := by rw [D.rep_sq i]; group
  have hu1 : u ≠ 1 := by
    intro h
    apply D.rep_ne_one i
    calc invRep v1 v2 v3 s t i = g * u * g⁻¹ := by rw [hu]; group
      _ = 1 := by rw [h]; group
  have huP : u ∈ alpP v1 v2 v3 s t := AlpEmb.genMax_le D.E r hg
  obtain ⟨j, hj⟩ := D.exists_inClass huP hu2 hu1
  refine ⟨j, ?_, D.inClass_fus (D.inClass_rep i) hj g rfl⟩
  rw [← AlpEmb.max_table_alpP D.E D.hF r j]
  obtain ⟨c, hc, hcu⟩ := hj
  exact ⟨u, hg, c, hc, hcu⟩

end FusCtx

end CFSG.OddStandard.ONanRec

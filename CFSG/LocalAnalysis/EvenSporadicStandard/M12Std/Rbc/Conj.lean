module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.M12Std

variable {P : Type*} [Group P]

theorem map_conj_centralizer (d : P) (s : Set P) :
    (centralizer s).map (MulAut.conj d).toMonoidHom = centralizer ((MulAut.conj d) '' s) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hz
    intro w hw
    rcases hw with ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc d * v * d⁻¹ * (d * z * d⁻¹) = d * (v * z) * d⁻¹ := by group
      _ = d * (z * v) * d⁻¹ := by rw [hz v hv]
      _ = d * z * d⁻¹ * (d * v * d⁻¹) := by group
  · intro hy
    refine ⟨d⁻¹ * y * d, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h := hy ((MulAut.conj d) v) ⟨v, hv, rfl⟩
      simp only [MulAut.conj_apply] at h
      calc v * (d⁻¹ * y * d) = d⁻¹ * (d * v * d⁻¹ * y) * d := by group
        _ = d⁻¹ * (y * (d * v * d⁻¹)) * d := by rw [h]
        _ = (d⁻¹ * y * d) * v := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem map_conj_self {D : Subgroup P} {d : P} (hd : d ∈ D) :
    D.map (MulAut.conj d).toMonoidHom = D := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact D.mul_mem (D.mul_mem hd hx) (D.inv_mem hd)
  · intro hy
    refine ⟨d⁻¹ * y * d, ?_, ?_⟩
    · exact D.mul_mem (D.mul_mem (D.inv_mem hd) hy) hd
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem map_conj_inf_centralizer_singleton {D : Subgroup P} {d : P} (hd : d ∈ D) (x : P) :
    (D ⊓ centralizer ({x} : Set P)).map (MulAut.conj d).toMonoidHom =
      D ⊓ centralizer ({d * x * d⁻¹} : Set P) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj d).injective, map_conj_self hd,
    map_conj_centralizer, Set.image_singleton, MulAut.conj_apply]

theorem map_conj_inf_centralizer_subgroup {D : Subgroup P} {d : P} (hd : d ∈ D) (H : Subgroup P) :
    (D ⊓ centralizer (H : Set P)).map (MulAut.conj d).toMonoidHom =
      D ⊓ centralizer ((H.map (MulAut.conj d).toMonoidHom : Subgroup P) : Set P) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj d).injective, map_conj_self hd,
    map_conj_centralizer, Subgroup.coe_map, MulEquiv.coe_toMonoidHom]

theorem map_conj_jOf {D : Subgroup P} {d : P} (hd : d ∈ D) (x : P) :
    (jOf D x).map (MulAut.conj d).toMonoidHom = jOf D (d * x * d⁻¹) := by
  unfold jOf
  rw [Subgroup.map_commutator, map_conj_inf_centralizer_singleton hd]

private theorem map_conj_inv_map_conj (Q : Subgroup P) (d : P) :
    (Q.map (MulAut.conj d⁻¹).toMonoidHom).map (MulAut.conj d).toMonoidHom = Q := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj d).toMonoidHom.comp (MulAut.conj d⁻¹).toMonoidHom =
      MonoidHom.id P := by
    ext y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

structure IsTwoA (D : Subgroup P) (x : P) : Prop where
  mem : x ∈ D
  orderOf_eq : orderOf x = 2
  card_cent : Nat.card ↥(D ⊓ centralizer ({x} : Set P)) = 240
  cent_jOf : D ⊓ centralizer (jOf D x : Set P) = zpowers x

structure Perf2A (D : Subgroup P) (x : P) : Prop extends IsTwoA D x where
  perfect : ∀ Q ≤ D ⊓ centralizer ({x} : Set P), ⁅Q, Q⁆ = Q → Q = ⊥ ∨ Q = jOf D x

@[expose] def GoodPerf (D H : Subgroup P) : Prop :=
  ∀ Q ≤ D ⊓ H, ⁅Q, Q⁆ = Q → Q = ⊥ ∨ ∃ x, IsTwoA D x ∧ Q = jOf D x

theorem IsTwoA.conj {D : Subgroup P} {x : P} (h : IsTwoA D x) {d : P} (hd : d ∈ D) :
    IsTwoA D (d * x * d⁻¹) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.mul_mem (D.mul_mem hd h.mem) (D.inv_mem hd)
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_eq]
  · rw [← map_conj_inf_centralizer_singleton hd x,
      Subgroup.card_map_of_injective (MulAut.conj d).injective, h.card_cent]
  · rw [← map_conj_jOf hd x, ← map_conj_inf_centralizer_subgroup hd (jOf D x),
      h.cent_jOf, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem Perf2A.conj {D : Subgroup P} {x : P} (h : Perf2A D x) {d : P} (hd : d ∈ D) :
    Perf2A D (d * x * d⁻¹) := by
  refine ⟨h.toIsTwoA.conj hd, ?_⟩
  intro Q hQ hQperf
  have hd' : d⁻¹ ∈ D := D.inv_mem hd
  have hstep : (D ⊓ centralizer ({d * x * d⁻¹} : Set P)).map (MulAut.conj d⁻¹).toMonoidHom
      = D ⊓ centralizer ({x} : Set P) := by
    rw [map_conj_inf_centralizer_singleton hd' (d * x * d⁻¹),
      show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group]
  have hmap : (Q.map (MulAut.conj d⁻¹).toMonoidHom) ≤ D ⊓ centralizer ({x} : Set P) :=
    hstep ▸ Subgroup.map_mono (f := (MulAut.conj d⁻¹).toMonoidHom) hQ
  have hperf : ⁅Q.map (MulAut.conj d⁻¹).toMonoidHom,
      Q.map (MulAut.conj d⁻¹).toMonoidHom⁆ = Q.map (MulAut.conj d⁻¹).toMonoidHom := by
    rw [← Subgroup.map_commutator, hQperf]
  have hQ' : Q = (Q.map (MulAut.conj d⁻¹).toMonoidHom).map
      (MulAut.conj d).toMonoidHom := (map_conj_inv_map_conj Q d).symm
  rcases h.perfect (Q.map (MulAut.conj d⁻¹).toMonoidHom) hmap hperf with hbot | hj
  · left
    rw [hQ', hbot, Subgroup.map_bot]
  · right
    rw [hQ', hj, map_conj_jOf hd x]

end CFSG.EvenSporadicStandard.M12Std.Rbc

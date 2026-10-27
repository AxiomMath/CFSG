module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Layer3

open Subgroup

theorem exists_conj_mem_sylow_two {X : Type*} [Group X] [Finite X] (S : Sylow 2 X) {s : X}
    (hs : orderOf s = 2) : ∃ g : X, g * s * g⁻¹ ∈ (S : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q S
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def]
  exact ⟨s, hQ (Subgroup.mem_zpowers s), by simp⟩

theorem nonempty_centralizer_mulEquiv_of_isConj {X : Type*} [Group X] {a b : X} (h : IsConj a b) :
    Nonempty (centralizer ({a} : Set X) ≃* centralizer ({b} : Set X)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨
    { toFun := fun z => ⟨c * z.1 * c⁻¹, ?_⟩
      invFun := fun z => ⟨c⁻¹ * z.1 * c, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }⟩
  · have hz := mem_centralizer_singleton_iff.1 z.2
    rw [mem_centralizer_singleton_iff, ← hc]
    calc c * z.1 * c⁻¹ * (c * a * c⁻¹) = c * (z.1 * a) * c⁻¹ := by group
      _ = c * (a * z.1) * c⁻¹ := by rw [hz]
      _ = c * a * c⁻¹ * (c * z.1 * c⁻¹) := by group
  · have hz := mem_centralizer_singleton_iff.1 z.2
    rw [mem_centralizer_singleton_iff]
    have hb : b = c * a * c⁻¹ := hc.symm
    subst hb
    calc c⁻¹ * z.1 * c * a = c⁻¹ * (z.1 * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * z.1) * c := by rw [hz]
      _ = a * (c⁻¹ * z.1 * c) := by group
  · intro z; ext; simp [mul_assoc]
  · intro z; ext; simp [mul_assoc]
  · intro z w; ext; simp only [Subgroup.coe_mul]; group

theorem card_centralizer_eq_of_isConj {X : Type*} [Group X] {a b : X} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set X)) = Nat.card (centralizer ({b} : Set X)) :=
  Nat.card_congr (nonempty_centralizer_mulEquiv_of_isConj h).some.toEquiv

theorem orderOf_eq_of_isConj' {X : Type*} [Group X] {a b : X} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  exact (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

theorem isConj_map_iff {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {a b : X} :
    IsConj (e a) (e b) ↔ IsConj a b :=
  ⟨fun h => by simpa using (e.symm.toMonoidHom).map_isConj h,
    fun h => (e.toMonoidHom).map_isConj h⟩

end CFSG.GH74.GLS.Layer3

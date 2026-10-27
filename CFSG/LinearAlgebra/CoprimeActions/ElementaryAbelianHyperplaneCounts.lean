module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.FixedSpace
public import CFSG.LinearAlgebra.CoprimeActions.FiniteFieldHyperplaneCount

public section

namespace CFSG.LinearAlgebra

namespace CoprimeActions

namespace ElementaryAbelianHyperplaneCounts

open CFSG.LinearAlgebra.CoprimeActions.FiniteFieldHyperplaneCount
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations

theorem coatom_iff_index {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (H : Submodule (ZMod p) V) :
    IsCoatom H ↔ H.toAddSubgroup.index = p := by
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  rw [← isSimpleModule_iff_isCoatom, isSimpleModule_iff_finrank_eq_one]
  have h1 : Nat.card V = Nat.card H * Nat.card (V ⧸ H) :=
    Submodule.card_eq_card_quotient_mul_card H
  have h2 : H.toAddSubgroup.index * Nat.card H.toAddSubgroup = Nat.card V :=
    AddSubgroup.index_mul_card H.toAddSubgroup
  have h3 : Nat.card H.toAddSubgroup = Nat.card H := rfl
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h4 : H.toAddSubgroup.index = Nat.card (V ⧸ H) := by
    rw [h3] at h2
    have : Nat.card H * H.toAddSubgroup.index = Nat.card H * Nat.card (V ⧸ H) := by
      rw [mul_comm, h2, h1]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h5 : Nat.card (V ⧸ H) = p ^ Module.finrank (ZMod p) (V ⧸ H) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  rw [h4, h5]
  constructor
  · intro h; rw [h, pow_one]
  · intro h
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (by simpa using h)

section Abstract

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommGroup B] [Finite B]

set_option warn.classDefReducibility false in
@[expose] noncomputable def moduleOf (hB : ∀ x : B, x ^ p = 1) : Module (ZMod p) (Additive B) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    simpa [toMul_nsmul] using hB (Additive.toMul x))

@[expose] noncomputable def subgroupEquiv (hB : ∀ x : B, x ^ p = 1) :
    letI := moduleOf hB
    Subgroup B ≃o Submodule (ZMod p) (Additive B) :=
  letI := moduleOf hB
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)

theorem natCard_hyperplanes_abstract (hB : ∀ x : B, x ^ p = 1) {n : ℕ} (hn : Nat.card B = p ^ n) :
    Nat.card {D : Subgroup B // D.index = p} = ∑ i ∈ Finset.range n, p ^ i := by
  letI := moduleOf hB
  haveI : Module.Finite (ZMod p) (Additive B) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod p) (Additive B) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive B)
    rw [Nat.card_zmod] at h
    have : Nat.card (Additive B) = Nat.card B := Nat.card_congr Additive.toMul
    rw [this, hn] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  have e : {D : Subgroup B // D.index = p} ≃ {H : Submodule (ZMod p) (Additive B) // IsCoatom H} :=
    Equiv.subtypeEquiv (subgroupEquiv hB).toEquiv (fun D => by
      rw [coatom_iff_index]
      rfl)
  rw [Nat.card_congr e, hyperplane_count, hrank, Nat.card_zmod]

end Abstract

theorem subgroupOf_map_subtype_eq {G : Type} [Group G] (A : Subgroup G) (E : Subgroup A) :
    (E.map A.subtype).subgroupOf A = E :=
  Subgroup.comap_map_eq_self_of_injective A.subtype_injective E

@[expose] def hyperplanesEquiv {G : Type} [Group G] (p : ℕ) (A : Subgroup G) :
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p A ≃ {E : Subgroup A // E.index = p} where
  toFun D := ⟨D.1.subgroupOf A, D.2.2⟩
  invFun E := ⟨E.1.map A.subtype, by
    refine ⟨Subgroup.map_subtype_le _, ?_⟩
    show ((E.1.map A.subtype).subgroupOf A).index = p
    rw [subgroupOf_map_subtype_eq]
    exact E.2⟩
  left_inv D := Subtype.ext (Subgroup.map_subgroupOf_eq_of_le D.2.1)
  right_inv E := Subtype.ext (subgroupOf_map_subtype_eq A E.1)

end ElementaryAbelianHyperplaneCounts

end CoprimeActions

namespace CoprimeActions.ElementaryAbelianHyperplaneCounts

open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations

theorem card_hyperplanes {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    [Finite A] (hA : CFSG.Open.IsElemAbelian p A) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card A = p ^ n) :
    Nat.card (hyperplanes p A) = ∑ i ∈ Finset.range n, p ^ i := by
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := fun a b => hA.1.is_comm.comm a b }
  rw [Nat.card_congr (hyperplanesEquiv p A)]
  exact natCard_hyperplanes_abstract (B := A) (fun x => Subtype.ext (hA.2 x x.2)) hcard

end CoprimeActions.ElementaryAbelianHyperplaneCounts

end CFSG.LinearAlgebra

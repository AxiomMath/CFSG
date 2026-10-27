module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.GH74.GLS.C3.Layer2

open Subgroup CFSG CFSG.ABGLocalTools

section Embedding

open Equiv Equiv.Perm DihedralGroup

private def altFactsD8Fun7 : DihedralGroup 4 → Perm (Fin 7)
  | .r i => (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) ^ i.val
  | .sr i => (swap 0 2 * swap 4 5) * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) ^ i.val

private theorem altFactsD8Fun7_mul :
    ∀ a b : DihedralGroup 4, altFactsD8Fun7 (a * b) = altFactsD8Fun7 a * altFactsD8Fun7 b := by
  decide

private theorem altFactsD8Fun7_injective :
    ∀ a b : DihedralGroup 4, altFactsD8Fun7 a = altFactsD8Fun7 b → a = b := by
  decide

private theorem altFactsD8Fun7_even :
    ∀ a : DihedralGroup 4, altFactsD8Fun7 a ∈ alternatingGroup (Fin 7) := by
  intro a
  rw [Equiv.Perm.mem_alternatingGroup]
  revert a
  decide

private def altFactsD8Hom7 : DihedralGroup 4 →* alternatingGroup (Fin 7) :=
  (MonoidHom.mk' altFactsD8Fun7 altFactsD8Fun7_mul).codRestrict _ altFactsD8Fun7_even

private theorem altFactsD8Hom7_injective : Function.Injective altFactsD8Hom7 := fun a b h =>
  altFactsD8Fun7_injective a b (congrArg Subtype.val h)

private def altFactsD8Fun6 : DihedralGroup 4 → Perm (Fin 6)
  | .r i => (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) ^ i.val
  | .sr i => (swap 0 2 * swap 4 5) * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) ^ i.val

private theorem altFactsD8Fun6_mul :
    ∀ a b : DihedralGroup 4, altFactsD8Fun6 (a * b) = altFactsD8Fun6 a * altFactsD8Fun6 b := by
  decide

private theorem altFactsD8Fun6_injective :
    ∀ a b : DihedralGroup 4, altFactsD8Fun6 a = altFactsD8Fun6 b → a = b := by
  decide

private theorem altFactsD8Fun6_even :
    ∀ a : DihedralGroup 4, altFactsD8Fun6 a ∈ alternatingGroup (Fin 6) := by
  intro a
  rw [Equiv.Perm.mem_alternatingGroup]
  revert a
  decide

private def altFactsD8Hom6 : DihedralGroup 4 →* alternatingGroup (Fin 6) :=
  (MonoidHom.mk' altFactsD8Fun6 altFactsD8Fun6_mul).codRestrict _ altFactsD8Fun6_even

private theorem altFactsD8Hom6_injective : Function.Injective altFactsD8Hom6 := fun a b h =>
  altFactsD8Fun6_injective a b (congrArg Subtype.val h)

private theorem altFacts_exists_d8Hom (n : ℕ) (hn : n = 6 ∨ n = 7) :
    ∃ f : DihedralGroup 4 →* alternatingGroup (Fin n), Function.Injective f := by
  rcases hn with rfl | rfl
  · exact ⟨altFactsD8Hom6, altFactsD8Hom6_injective⟩
  · exact ⟨altFactsD8Hom7, altFactsD8Hom7_injective⟩

private theorem altFacts_card_factorization (n : ℕ) (hn : n = 6 ∨ n = 7) :
    (Nat.card (alternatingGroup (Fin n))).factorization 2 = 3 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  rcases hn with rfl | rfl <;>
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide +kernel

end Embedding

section Dihedral

open DihedralGroup

private theorem altFacts_d4_r2_central : ∀ x : DihedralGroup 4, r 2 * x = x * r 2 := by decide

private theorem altFacts_d4_central_eq :
    ∀ w : DihedralGroup 4, (∀ p, w * p = p * w) → w = 1 ∨ w = r 2 := by decide

private theorem altFacts_d4_noncomm : (sr 0 : DihedralGroup 4) * r 1 ≠ r 1 * sr 0 := by decide

private theorem altFacts_d4_r2_ne_one : (r 2 : DihedralGroup 4) ≠ 1 := by decide

private def altFactsKleinV : Subgroup (DihedralGroup 4) where
  carrier := {x | x = 1 ∨ x = r 2 ∨ x = sr 0 ∨ x = sr 2}
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide

private theorem altFactsKleinV_card : Nat.card altFactsKleinV = 4 := by
  classical
  have h : ∀ x : DihedralGroup 4,
      x ∈ altFactsKleinV ↔ x ∈ ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4)) := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Iff.rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_finsetCard]
  decide

private theorem altFactsKleinV_isElementaryAbelian : IsElementaryAbelian 2 altFactsKleinV := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    apply Subtype.ext
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    obtain ⟨x, hx⟩ := x
    apply Subtype.ext
    rcases hx with rfl | rfl | rfl | rfl <;> decide

private theorem altFacts_props_of_equiv_dihedral {G : Type*} [Group G] {P : Subgroup G}
    (ψ : ↥P ≃* DihedralGroup 4) :
    (∃ z ∈ P, z ≠ 1 ∧ (∀ p ∈ P, z * p = p * z) ∧
        ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z) ∧
      (∃ p ∈ P, orderOf p = 2 ∧ ∃ r ∈ P, p * r ≠ r * p) := by
  constructor
  · refine ⟨(ψ.symm (r 2) : G), (ψ.symm (r 2)).2, ?_, ?_, ?_⟩
    · intro h
      have h1 : ψ.symm (r 2) = 1 := Subtype.ext h
      exact altFacts_d4_r2_ne_one (by simpa using congrArg ψ h1)
    · intro p hp
      have h := congrArg ψ.symm (altFacts_d4_r2_central (ψ ⟨p, hp⟩))
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
      exact congrArg Subtype.val h
    · intro w hw hc
      have hw' : ∀ q : DihedralGroup 4, ψ ⟨w, hw⟩ * q = q * ψ ⟨w, hw⟩ := by
        intro q
        have := hc (ψ.symm q : G) (ψ.symm q).2
        apply ψ.symm.injective
        rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
        exact Subtype.ext this
      rcases altFacts_d4_central_eq _ hw' with h | h
      · left
        have : (⟨w, hw⟩ : P) = 1 := ψ.injective (by simpa using h)
        exact congrArg Subtype.val this
      · right
        have : (⟨w, hw⟩ : P) = ψ.symm (r 2) := ψ.injective (by simpa using h)
        exact congrArg Subtype.val this
  · refine ⟨(ψ.symm (sr 0) : G), (ψ.symm (sr 0)).2, ?_, (ψ.symm (r 1) : G), (ψ.symm (r 1)).2, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_sr 0
    · intro h
      apply altFacts_d4_noncomm
      apply ψ.symm.injective
      rw [map_mul, map_mul]
      exact Subtype.ext h

end Dihedral

private theorem altFacts_sylow_iso_dihedral {K : Type*} [Group K] [Finite K]
    (f : DihedralGroup 4 →* K) (hf : Function.Injective f)
    (hK : (Nat.card K).factorization 2 = 3) (Q : Sylow 2 K) :
    Nonempty (↥(Q : Subgroup K) ≃* DihedralGroup 4) := by
  have hcard : Nat.card f.range = 2 ^ (Nat.card K).factorization 2 := by
    rw [hK, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm, DihedralGroup.nat_card]
    norm_num
  let T : Sylow 2 K := Sylow.ofCard f.range hcard
  have hT : (T : Subgroup K) = f.range := Sylow.coe_ofCard _ _
  exact ⟨(Sylow.equiv Q T).trans
    ((MulEquiv.subgroupCongr hT).trans (MonoidHom.ofInjective hf).symm)⟩

theorem sylow_alt_facts {G : Type*} [Group G] [Finite G] (n : ℕ) (hn : n = 6 ∨ n = 7)
    {K P : Subgroup G} (e : K ≃* alternatingGroup (Fin n)) (hP : IsSylowOf 2 P K) :
    Nat.card P = 8 ∧
      (∃ z ∈ P, z ≠ 1 ∧ (∀ p ∈ P, z * p = p * z) ∧
        ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z) ∧
      (∃ p ∈ P, orderOf p = 2 ∧ ∃ r ∈ P, p * r ≠ r * p) ∧
      (∃ E : Subgroup G, E ≤ P ∧ Nat.card E = 4 ∧ IsElementaryAbelian 2 E) := by
  obtain ⟨f, hf⟩ := altFacts_exists_d8Hom n hn
  have hK : (Nat.card K).factorization 2 = 3 := by
    rw [Nat.card_congr e.toEquiv]
    exact altFacts_card_factorization n hn
  let g : DihedralGroup 4 →* K := e.symm.toMonoidHom.comp f
  have hg : Function.Injective g := e.symm.injective.comp hf
  obtain ⟨Q, hQ⟩ := hP
  obtain ⟨iso⟩ := altFacts_sylow_iso_dihedral g hg hK Q
  let ψ : ↥P ≃* DihedralGroup 4 :=
    (((MulEquiv.subgroupCongr hQ).symm.trans
      (Subgroup.equivMapOfInjective (Q : Subgroup K) K.subtype K.subtype_injective).symm).trans iso)
  obtain ⟨hcentre, hnoncentral⟩ := altFacts_props_of_equiv_dihedral ψ
  refine ⟨?_, hcentre, hnoncentral, ?_⟩
  · rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
  · have : IsElementaryAbelian 2 altFactsKleinV := altFactsKleinV_isElementaryAbelian
    let h : DihedralGroup 4 →* G := P.subtype.comp ψ.symm.toMonoidHom
    have hh : Function.Injective h := fun a b hab => ψ.symm.injective (Subtype.ext hab)
    refine ⟨altFactsKleinV.map h, ?_, ?_, IsElementaryAbelian.map h⟩
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact (ψ.symm y).2
    · rw [Subgroup.card_map_of_injective hh, altFactsKleinV_card]

end CFSG.GH74.GLS.C3.Layer2

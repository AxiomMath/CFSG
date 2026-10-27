module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.ComponentClassification.PresentationLocal

theorem gh23_z3a5_equiv_of_rels {H : Type*} [Group H] [Finite H] (y : ℕ → H) (z : H)
    (h3 : ∀ i, i < 3 → y i ^ 3 = 1)
    (h2 : ∀ i j, i < 3 → j < 3 → i ≠ j → (y i * y j) ^ 2 = 1)
    (hz : z ^ 3 = 1) (hc : ∀ i, i < 3 → z * y i = y i * z)
    (hgen : Subgroup.closure ({z} ∪ {h | ∃ i, i < 3 ∧ y i = h}) = ⊤)
    (hcard : Nat.card H = 180) :
    Nonempty (H ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) := by
  classical
  let x : CarmichaelIndex 5 → H := fun k => y ((k.1 : ℕ) - 2)
  have hx : ∀ i, x i ^ 3 = 1 := by
    intro i
    exact h3 _ (by have := i.2; have := i.1.isLt; omega)
  have hxx : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := by
    intro i j hij
    refine h2 _ _ (by have := i.2; have := i.1.isLt; omega)
      (by have := j.2; have := j.1.isLt; omega) ?_
    intro h
    exact hij (Subtype.ext (Fin.ext (by have := i.2; have := j.2; omega)))
  obtain ⟨φ, hφ⟩ := exists_hom_carmichaelCycle (n := 5) (by norm_num) x hx hxx
  have hrange : φ.range = Subgroup.closure (Set.range x) := by
    rw [MonoidHom.range_eq_map, ← closure_range_carmichaelCycle (n := 5) (by norm_num),
      MonoidHom.map_closure]
    congr 1
    ext w
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨a, ⟨k, rfl⟩, ha⟩
      exact ⟨k, (hφ k).symm.trans ha⟩
    · rintro ⟨k, rfl⟩
      exact ⟨carmichaelCycle k, ⟨k, rfl⟩, hφ k⟩
  have hcl : Subgroup.closure (Set.range x) ≤ Subgroup.centralizer ({z} : Set H) := by
    rw [Subgroup.closure_le]
    rintro w ⟨k, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hc _ (by have := k.2; have := k.1.isLt; omega)).symm
  have hcommφ : ∀ a, Commute z (φ a) := by
    intro a
    have hain : φ a ∈ Subgroup.closure (Set.range x) := by
      rw [← hrange]
      exact ⟨a, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hcl hain)).symm
  let f : Multiplicative (ZMod 3) →* H :=
    { toFun := fun a => z ^ (Multiplicative.toAdd a).val
      map_one' := by simp [toAdd_one, ZMod.val_zero]
      map_mul' := by
        intro a b
        have hmod : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz
        show z ^ (Multiplicative.toAdd (a * b)).val =
          z ^ (Multiplicative.toAdd a).val * z ^ (Multiplicative.toAdd b).val
        rw [← pow_add]
        apply pow_eq_pow_iff_modEq.mpr
        rw [toAdd_mul, ZMod.val_add]
        exact (Nat.mod_modEq _ 3).of_dvd hmod }
  let Ψ : Multiplicative (ZMod 3) × alternatingGroup (Fin 5) →* H :=
    MonoidHom.noncommCoprod f φ (fun m n => (hcommφ n).pow_left (Multiplicative.toAdd m).val)
  have hz_range : z ∈ Ψ.range := by
    refine ⟨(Multiplicative.ofAdd (1 : ZMod 3), 1), ?_⟩
    rw [MonoidHom.noncommCoprod_apply]
    have h1 : (1 : ZMod 3).val = 1 := by
      rw [ZMod.val_one_eq_one_mod]
    simp [f, toAdd_ofAdd, h1]
  have hy_range : ∀ i, i < 3 → y i ∈ Ψ.range := by
    intro i hi
    refine ⟨(Multiplicative.ofAdd (0 : ZMod 3),
      carmichaelCycle ⟨⟨i + 2, by omega⟩, by simp⟩), ?_⟩
    have hx' : x ⟨⟨i + 2, by omega⟩, by simp⟩ = y i := by
      show y ((i + 2) - 2) = y i
      rw [Nat.add_sub_cancel]
    rw [MonoidHom.noncommCoprod_apply, hφ, hx']
    simp [f, toAdd_ofAdd, ZMod.val_zero]
  have hrange_top : Ψ.range = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro g hg
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hg
    rcases hg with rfl | ⟨i, hi, rfl⟩
    · exact hz_range
    · exact hy_range i hi
  have hsurj : Function.Surjective Ψ := (MonoidHom.range_eq_top).mp hrange_top
  have hcardM : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ← Nat.card_eq_fintype_card]
    exact Nat.card_zmod 3
  have hcardDom : Nat.card (Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) = 180 := by
    rw [Nat.card_prod, hcardM, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hle : Nat.card (Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) ≤ Nat.card H :=
    le_of_eq (hcardDom.trans hcard.symm)
  have hbij : Function.Bijective Ψ :=
    hsurj.bijective_of_nat_card_le hle
  exact ⟨(MulEquiv.ofBijective Ψ hbij).symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside

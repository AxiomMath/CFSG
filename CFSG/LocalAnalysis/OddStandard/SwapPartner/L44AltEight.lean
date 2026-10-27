module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm

private def c8 : Perm (Fin 8) := Fin.cycleRange (6 : Fin 8)

private def n8 : Perm (Fin 8) := swap (1 : Fin 8) 6 * swap 2 5 * swap 3 4

private lemma c8_pow_seven : c8 ^ 7 = 1 := by decide

private lemma c8_ne_one : c8 ≠ 1 := by decide

private lemma c8_mem : c8 ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup]
  decide

private lemma n8_sign : Perm.sign n8 = -1 := by decide

private lemma n8_conj_c8 : n8 * c8 * n8⁻¹ = c8⁻¹ := by decide

private lemma c8_order : orderOf c8 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime c8_pow_seven c8_ne_one

private lemma orderOf_eA_symm_c8 {G : Type*} [Group G] {A : Subgroup G}
    (eA : A ≃* alternatingGroup (Fin 8)) :
    orderOf ((eA.symm ⟨c8, c8_mem⟩ : A) : G) = 7 := by
  rw [Subgroup.orderOf_coe]
  rw [← MulEquiv.orderOf_eq eA (eA.symm ⟨c8, c8_mem⟩)]
  rw [MulEquiv.apply_symm_apply, Subgroup.orderOf_mk]
  exact c8_order

theorem exists_mem_orderOf_seven {G : Type*} [Group G] (A : Subgroup G)
    (eA : A ≃* alternatingGroup (Fin 8)) : ∃ y ∈ A, orderOf y = 7 := by
  exact ⟨((eA.symm ⟨c8, c8_mem⟩ : A) : G), (eA.symm ⟨c8, c8_mem⟩).2,
    orderOf_eA_symm_c8 eA⟩

theorem exists_inverting_sevenElement {G : Type*} [Group G] (A : Subgroup G)
    (eA : A ≃* alternatingGroup (Fin 8)) (f : MulAut G) (hf : ∀ a ∈ A, f a ∈ A)
    (hout : ¬ ∃ a ∈ A, ∀ x ∈ A, f x = a * x * a⁻¹) :
    ∃ y ∈ A, orderOf y = 7 ∧ ∃ a ∈ A, a * f y * a⁻¹ = y⁻¹ := by
  haveI : Finite A := Finite.of_equiv (alternatingGroup (Fin 8)) eA.toEquiv.symm
  let φ : A →* G := f.toMonoidHom.comp A.subtype
  let α0 : A →* A := φ.codRestrict A (fun a => hf a a.2)
  have hα0inj : Function.Injective α0 := by
    intro a b hab
    apply Subtype.ext
    exact f.injective (congrArg Subtype.val hab)
  have hα0bij : Function.Bijective α0 := Finite.injective_iff_bijective.mp hα0inj
  let α : MulAut A := MulEquiv.ofBijective α0 hα0bij
  have hαapp : ∀ a : A, ((α a : A) : G) = f (a : G) := by
    intro a
    change ((MulEquiv.ofBijective α0 hα0bij) a : G) = f (a : G)
    rw [MulEquiv.ofBijective_apply]
    rfl
  let β : MulAut (alternatingGroup (Fin 8)) := MulAut.congr eA α
  let ι : Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
        (by norm_num) (by norm_num))
  let π : Perm (Fin 8) := ι.symm β
  have hιβ : ι π = β := ι.apply_symm_apply β
  have hιπ : ι π = MulAut.conjNormal (H := alternatingGroup (Fin 8)) π := rfl
  have hβconj : ∀ x : alternatingGroup (Fin 8),
      β x = MulAut.conjNormal (H := alternatingGroup (Fin 8)) π x := by
    intro x
    rw [← hιπ, hιβ]
  have hinner_of_sign : Perm.sign π = 1 → ∃ a ∈ A, ∀ x ∈ A, f x = a * x * a⁻¹ := by
    intro hπ
    have hπmem : π ∈ alternatingGroup (Fin 8) := by
      rw [Perm.mem_alternatingGroup]; exact hπ
    let a0 : A := eA.symm ⟨π, hπmem⟩
    have ha0 : eA a0 = ⟨π, hπmem⟩ := eA.apply_symm_apply _
    have hαconj : ∀ x : A, α x = a0 * x * a0⁻¹ := by
      intro x
      apply eA.injective
      have h1 : eA (α x) = β (eA x) := by simp [β, MulAut.congr_apply]
      rw [h1, hβconj, map_mul, map_mul, map_inv, ha0]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      simp
    refine ⟨(a0 : G), a0.2, ?_⟩
    intro x hx
    have hx' := hαconj ⟨x, hx⟩
    calc f x = ((α ⟨x, hx⟩ : A) : G) := by rw [hαapp]
      _ = ((a0 * ⟨x, hx⟩ * a0⁻¹ : A) : G) := by rw [hx']
      _ = (a0 : G) * x * (a0 : G)⁻¹ := by simp
  have hπsign : Perm.sign π = -1 := by
    rcases Int.units_eq_one_or (Perm.sign π) with h | h
    · exact absurd h fun h1 => hout (hinner_of_sign h1)
    · exact h
  let nπ : Perm (Fin 8) := n8 * π⁻¹
  have hnπ : nπ ∈ alternatingGroup (Fin 8) := by
    rw [Perm.mem_alternatingGroup]
    change Perm.sign (n8 * π⁻¹) = 1
    rw [map_mul, Perm.sign_inv, n8_sign, hπsign]
    decide
  let y0 : A := eA.symm ⟨c8, c8_mem⟩
  let a1 : A := eA.symm ⟨nπ, hnπ⟩
  have hy0 : eA y0 = ⟨c8, c8_mem⟩ := eA.apply_symm_apply _
  have ha1 : eA a1 = ⟨nπ, hnπ⟩ := eA.apply_symm_apply _
  have hconjA : a1 * α y0 * a1⁻¹ = y0⁻¹ := by
    apply eA.injective
    have h1 : eA (α y0) = β (eA y0) := by simp [β, MulAut.congr_apply]
    rw [map_mul, map_mul, map_inv, map_inv, h1, hβconj, ha1, hy0]
    apply Subtype.ext
    simp only [nπ, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    rw [← n8_conj_c8]
    group
  refine ⟨(y0 : G), y0.2, orderOf_eA_symm_c8 eA, (a1 : G), a1.2, ?_⟩
  calc (a1 : G) * f (y0 : G) * (a1 : G)⁻¹
      = ((a1 * α y0 * a1⁻¹ : A) : G) := by
        rw [show f (y0 : G) = ((α y0 : A) : G) from (hαapp y0).symm]
        simp
    _ = ((y0⁻¹ : A) : G) := by rw [hconjA]
    _ = (y0 : G)⁻¹ := by simp

end CFSG.OddStandard.AltStdSec.SwapPartner

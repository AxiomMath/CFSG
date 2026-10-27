module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartOne.S12.Sec154Fin
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

theorem mulAut_perm_fin_inner_of_ge_five {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6)
    (φ : MulAut (Perm (Fin m))) : ∃ β : Perm (Fin m), ∀ x, φ x = β * x * β⁻¹ := by
  have h5 : 5 ≤ Nat.card (Fin m) := by simpa using hm
  have hAm : (alternatingGroup (Fin m)).map φ.toMonoidHom = alternatingGroup (Fin m) := by
    rw [← alternatingGroup.commutator_perm_eq h5, commutator_def, map_commutator,
      Subgroup.map_top_of_surjective _ φ.surjective]
  let ψ : MulAut (alternatingGroup (Fin m)) :=
    (φ.subgroupMap (alternatingGroup (Fin m))).trans (MulEquiv.subgroupCongr hAm)
  obtain ⟨β, hβ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm hm6).2 ψ
  have hA : ∀ a ∈ alternatingGroup (Fin m), φ a = β * a * β⁻¹ := by
    intro a ha
    have h := congrArg (fun f : MulAut (alternatingGroup (Fin m)) =>
      ((f ⟨a, ha⟩ : alternatingGroup (Fin m)) : Perm (Fin m))) hβ
    simp only [MulAut.conjNormal_apply] at h
    rw [h]
    rfl
  refine ⟨β, fun x => ?_⟩
  set w := (β * x * β⁻¹)⁻¹ * φ x with hw
  have hw1 : w = 1 := by
    refine CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
      (by simp only [Fintype.card_fin]; omega) fun c hc => ?_
    have ha : β⁻¹ * c * β ∈ alternatingGroup (Fin m) := by
      simpa using (alternatingGroup.normal (α := Fin m)).conj_mem _ hc β⁻¹
    have hxa : x * (β⁻¹ * c * β) * x⁻¹ ∈ alternatingGroup (Fin m) :=
      (alternatingGroup.normal (α := Fin m)).conj_mem _ ha x
    have e1 : φ (x * (β⁻¹ * c * β) * x⁻¹) = φ x * c * (φ x)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hA _ ha]
      group
    have e2 := hA _ hxa
    rw [e1] at e2
    have e3 : φ x * c * (φ x)⁻¹ = (β * x * β⁻¹) * c * (β * x * β⁻¹)⁻¹ := by
      rw [e2]
      group
    calc w * c = (β * x * β⁻¹)⁻¹ * (φ x * c * (φ x)⁻¹) * φ x := by rw [hw]; group
      _ = (β * x * β⁻¹)⁻¹ * ((β * x * β⁻¹) * c * (β * x * β⁻¹)⁻¹) * φ x := by rw [e3]
      _ = c * w := by rw [hw]; group
  have : φ x = (β * x * β⁻¹) * w := by rw [hw]; group
  rw [this, hw1, mul_one]

theorem mulAut_perm_fin_inner {m : ℕ} (hm6 : m ≠ 6) (φ : MulAut (Perm (Fin m))) :
    ∃ β : Perm (Fin m), ∀ x, φ x = β * x * β⁻¹ := by
  rcases (by omega : m ≤ 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m) with hm | rfl | rfl | hm
  · refine ⟨1, fun x => ?_⟩
    rw [one_mul, inv_one, mul_one]
    interval_cases m
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
    · have h2 : ∀ y : Perm (Fin 2), y ≠ 1 → y = swap 0 1 := by decide
      by_cases hx : x = 1
      · rw [hx, map_one]
      · have hφx : φ x ≠ 1 := fun h => hx (φ.injective (by rw [h, map_one]))
        rw [h2 _ hφx, h2 _ hx]
  · exact CFSG.Quasithin.SBd.perm_three_aut_inner φ
  · obtain ⟨β, hβ⟩ := CFSG.RankThree.PartOne.Sec154Fin.sym4_conj_surjective φ
    refine ⟨β, fun x => ?_⟩
    rw [← hβ]
    rfl
  · exact mulAut_perm_fin_inner_of_ge_five hm hm6 φ

variable {α : Type*} [Fintype α]

theorem mulAut_perm_inner (h6 : Fintype.card α ≠ 6) (φ : MulAut (Perm α)) :
    ∃ β : Perm α, ∀ x, φ x = β * x * β⁻¹ := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let P : Perm α ≃* Perm (Fin (Fintype.card α)) := e.permCongrHom
  obtain ⟨β', hβ'⟩ := mulAut_perm_fin_inner h6 ((P.symm.trans φ).trans P)
  refine ⟨P.symm β', fun x => ?_⟩
  have h := hβ' (P x)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
  have h' := congrArg P.symm h
  rw [MulEquiv.symm_apply_apply] at h'
  rw [h', map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem exists_conj_of_injective (h6 : Fintype.card α ≠ 6) (θ : Perm α →* Perm α)
    (hθ : Function.Injective θ) : ∃ β : Perm α, ∀ x, θ x = β * x * β⁻¹ := by
  have hbij : Function.Bijective θ := ⟨hθ, Finite.injective_iff_surjective.mp hθ⟩
  obtain ⟨β, hβ⟩ := mulAut_perm_inner h6 (MulEquiv.ofBijective θ hbij)
  exact ⟨β, fun x => hβ x⟩

end CFSG.ComponentClassification.RankTwoAlt

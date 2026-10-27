module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

import CFSG.Permutation.AlternatingAutomorphism.Conjugation
import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent
import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Rank

public section

namespace CFSG.GroupTheory

open Equiv Equiv.Perm

theorem card_le_sixteen_of_sq_eq_one_mulAut_alt8
    (E : Subgroup (MulAut (alternatingGroup (Fin 8)))) (hE : ∀ y ∈ E, y * y = 1) :
    Nat.card E ≤ 16 := by
  classical
  let c : Perm (Fin 8) →* MulAut (alternatingGroup (Fin 8)) := MulAut.conjNormal
  have hinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    refine CFSG.GH74.GLS.IVK.GHInv.eq_one_of_commute_alternating (by simp) ?_
    intro g hg
    have h1 := congrArg (fun f : MulAut (alternatingGroup (Fin 8)) => (f ⟨g, hg⟩ : Perm (Fin 8))) hσ
    simp only [c, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc σ * g = (σ * g * σ⁻¹) * σ := by group
      _ = g * σ := by rw [h1]
  have hsurj : Function.Surjective c := by
    intro f
    obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
      (by omega : 8 = 5 ∨ 7 ≤ 8) f
    refine ⟨σ, MulEquiv.ext fun g => Subtype.ext ?_⟩
    simp only [c, MulAut.conjNormal_apply]
    exact (hσ g).symm
  let E' : Subgroup (Perm (Fin 8)) := E.comap c
  have hE' : ∀ x ∈ E', x ^ 2 = 1 := by
    intro x hx
    have h1 : c x * c x = 1 := hE (c x) hx
    rw [← map_mul] at h1
    rw [pow_two]
    exact hinj (by rw [h1, map_one])
  have hcard := CFSG.OddStandard.AltStdSmall4.card_le_two_pow_half_of_sq_eq_one E' hE'
  have hmap : E'.map c = E := Subgroup.map_comap_eq_self_of_surjective hsurj E
  have h2 : Nat.card ↥(E'.map c) = Nat.card ↥E' := Subgroup.card_map_of_injective hinj
  rw [hmap] at h2
  rw [h2]
  simpa using hcard

theorem card_le_sixteen_mul_card_inf_centralizer_of_mulEquiv_alt8 {K : Type} [Group K]
    [Finite K] (X : Subgroup K) [X.Normal] (e : ↥X ≃* alternatingGroup (Fin 8))
    (A : Subgroup K) (hA : ∀ x ∈ A, x * x = 1) :
    Nat.card ↥A ≤ 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (X : Set K)) := by
  classical
  let φ : K →* MulAut (alternatingGroup (Fin 8)) :=
    ((MulAut.congr e).toMonoidHom).comp (MulAut.conjNormal : K →* MulAut ↥X)
  let ψ : ↥A →* MulAut (alternatingGroup (Fin 8)) := φ.comp A.subtype
  have hrange : Nat.card ↥ψ.range ≤ 16 := by
    refine card_le_sixteen_of_sq_eq_one_mulAut_alt8 ψ.range ?_
    rintro _ ⟨x, rfl⟩
    show ψ x * ψ x = 1
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hA x x.2)
    rw [this, map_one]
  have hker : Nat.card ↥ψ.ker ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (X : Set K)) := by
    let f : ↥ψ.ker → ↥(A ⊓ Subgroup.centralizer (X : Set K)) := fun x =>
      ⟨(x.1 : K), Subgroup.mem_inf.mpr ⟨x.1.2, ?_⟩⟩
    · refine Nat.card_le_card_of_injective f ?_
      intro x y hxy
      have h1 := congrArg (fun t : ↥(A ⊓ Subgroup.centralizer (X : Set K)) => (t : K)) hxy
      exact Subtype.ext (Subtype.ext h1)
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hx : ψ x.1 = 1 := x.2
      have h1 : (MulAut.conjNormal (H := X) (x.1 : K) : MulAut ↥X) = 1 := by
        have : (MulAut.congr e) (MulAut.conjNormal (H := X) (x.1 : K)) = 1 := hx
        exact (MulAut.congr e).injective (by rw [this, map_one])
      have h2 := congrArg (fun f : MulAut ↥X => ((f ⟨c, hc⟩ : ↥X) : K)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      have h3 : (x.1 : K) * c = c * (x.1 : K) := by
        calc (x.1 : K) * c = (x.1 * c * (x.1 : K)⁻¹) * x.1 := by group
          _ = c * x.1 := by rw [h2]
      exact h3.symm
  have hmul : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = Nat.card ↥A := by
    rw [← ψ.ker.card_mul_index, Subgroup.index_ker]
  calc Nat.card ↥A = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := hmul.symm
    _ = Nat.card ↥ψ.range * Nat.card ↥ψ.ker := mul_comm _ _
    _ ≤ 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (X : Set K)) := Nat.mul_le_mul hrange hker

end CFSG.GroupTheory

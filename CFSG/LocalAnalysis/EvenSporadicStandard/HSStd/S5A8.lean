module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv

theorem exists_conj_perm_eight {H : Type*} [Group H] (ψ : Perm (Fin 8) →* H)
    (hψ : Function.Injective ψ) (hN : ((alternatingGroup (Fin 8)).map ψ).Normal) (g : H) :
    ∃ σ : Perm (Fin 8), ∀ n ∈ (alternatingGroup (Fin 8)).map ψ,
      g * n * g⁻¹ = ψ σ * n * (ψ σ)⁻¹ := by
  classical
  set A := alternatingGroup (Fin 8) with hA
  set N : Subgroup H := A.map ψ with hNdef
  have : N.Normal := hN
  let e : A ≃* N := Subgroup.equivMapOfInjective A ψ hψ
  let α : MulAut A := (MulAut.congr e).symm (MulAut.conjNormal (H := N) g)
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
      (by norm_num)).2 α
  refine ⟨σ, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 : (e (α ⟨a, ha⟩) : H) = g * ψ a * g⁻¹ := by
    have : e (α ⟨a, ha⟩) = MulAut.conjNormal (H := N) g (e ⟨a, ha⟩) := by
      simp [α]
    rw [this, MulAut.conjNormal_apply]
    rfl
  have h2 : ((α ⟨a, ha⟩ : A) : Perm (Fin 8)) = σ * a * σ⁻¹ := by
    rw [← hσ]
    exact MulAut.conjNormal_apply σ ⟨a, ha⟩
  have h3 : ((e (α ⟨a, ha⟩) : N) : H) = ψ ((α ⟨a, ha⟩ : A) : Perm (Fin 8)) := rfl
  rw [← h1, h3, h2, map_mul, map_mul, map_inv]

theorem map_commutator_range {G : Type*} [Group G] (ψ : Perm (Fin 8) →* G)
    (hψ : Function.Injective ψ) (T : Subgroup G) (hT : ψ.range = T) :
    (commutator ↥T).map T.subtype = (alternatingGroup (Fin 8)).map ψ := by
  let e : Perm (Fin 8) ≃* ↥T := (MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hT)
  have he : T.subtype.comp e.toMonoidHom = ψ := by
    ext σ
    rfl
  have h1 : (commutator (Perm (Fin 8))).map e.toMonoidHom = commutator ↥T := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← h1, Subgroup.map_map, he, alternatingGroup.commutator_perm_eq (by simp)]

theorem mul_inv_mem_alternatingGroup {σ κ : Perm (Fin 8)} (hσ : σ ∉ alternatingGroup (Fin 8))
    (hκ : κ ∉ alternatingGroup (Fin 8)) : σ * κ⁻¹ ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup] at hσ hκ ⊢
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact absurd h hσ
  rcases Int.units_eq_one_or (Equiv.Perm.sign κ) with h' | h'
  · exact absurd h' hκ
  rw [map_mul, map_inv, h, h']
  decide

end CFSG.EvenSporadicStandard.HSStd

module

public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

theorem exists_label {G : Type} [Group G] {K : Subgroup G} {S : Set G}
    (hinv : ∀ k ∈ K, ∀ c ∈ S, k * c * k⁻¹ ∈ S) (hcard : Nat.card ↥S = 5) :
    ∃ (s : Fin 5 → G) (ρ : ↥K →* Perm (Fin 5)), Function.Injective s ∧ (∀ i, s i ∈ S) ∧
      (∀ x ∈ S, ∃ i, s i = x) ∧
      ∀ (l : ↥K) (i : Fin 5), (l : G) * s i * (l : G)⁻¹ = s (ρ l i) := by
  classical
  haveI : Finite ↥S := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let e : ↥S ≃ Fin 5 := (Finite.equivFin ↥S).trans (finCongr hcard)
  letI : MulAction ↥K ↥S :=
    { smul := fun l c => ⟨(l : G) * c * (l : G)⁻¹, hinv l l.2 c c.2⟩
      one_smul := fun c => Subtype.ext (by
        show ((1 : ↥K) : G) * (c : G) * ((1 : ↥K) : G)⁻¹ = c
        simp)
      mul_smul := fun l l' c => Subtype.ext (by
        show ((l * l' : ↥K) : G) * (c : G) * ((l * l' : ↥K) : G)⁻¹ =
          (l : G) * ((l' : G) * (c : G) * (l' : G)⁻¹) * (l : G)⁻¹
        simp [mul_assoc]) }
  let ρ : ↥K →* Perm (Fin 5) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom ↥K ↥S)
  have hρ : ∀ (l : ↥K) (i : Fin 5), e.symm (ρ l i) = l • e.symm i := fun l i => by
    simp [ρ, Equiv.permCongrHom, Equiv.permCongr_apply]
  refine ⟨fun i => (e.symm i : G), ρ, ?_, fun i => (e.symm i).2,
    fun x hx => ⟨e ⟨x, hx⟩, by simp⟩, fun l i => ?_⟩
  · intro i j h
    exact e.symm.injective (Subtype.ext h)
  · have h := congrArg Subtype.val (hρ l i)
    exact h.symm

end CFSG.EvenSporadicStandard.HNRecog.Section4

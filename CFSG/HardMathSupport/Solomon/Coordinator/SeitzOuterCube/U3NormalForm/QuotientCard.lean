module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF

theorem card_quotient_map_comap {G H : Type*} [Group G] [Group H] (U : Subgroup G)
    (φ : U →* H) (A : Subgroup H) (hsurj : ∀ a ∈ A, ∃ u : U, φ u = a) (S : Subgroup G)
    (hker : ∀ u : U, φ u = 1 ↔ (u : G) ∈ S) :
    Nat.card (((A.comap φ).map U.subtype) ⧸ S.subgroupOf ((A.comap φ).map U.subtype)) =
      Nat.card A := by
  set Ã : Subgroup U := A.comap φ with hÃ
  set P : Subgroup G := Ã.map U.subtype with hP
  let e : Ã ≃* P := Ã.equivMapOfInjective U.subtype U.subtype_injective
  have he : ∀ y : Ã, ((e y : P) : G) = (((y : Ã) : U) : G) := fun y => rfl
  let ψ0 : Ã →* A := (φ.comp Ã.subtype).codRestrict A (fun x => x.2)
  let ψ : P →* A := ψ0.comp e.symm.toMonoidHom
  have hψs : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨u, hu⟩ := hsurj a ha
    have huÃ : u ∈ Ã := by
      show φ u ∈ A
      rw [hu]
      exact ha
    refine ⟨e ⟨u, huÃ⟩, ?_⟩
    apply Subtype.ext
    simp only [ψ, ψ0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      MonoidHom.codRestrict_apply, Subgroup.subtype_apply]
    exact hu
  have hψk : ψ.ker = S.subgroupOf P := by
    ext x
    have hx : (x : G) = (((e.symm x : Ã) : U) : G) := by
      rw [← he, MulEquiv.apply_symm_apply]
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hx, ← hker]
    constructor
    · intro h1
      have := congrArg Subtype.val h1
      exact this
    · intro h1
      apply Subtype.ext
      exact h1
  have hN : (S.subgroupOf P).Normal := by rw [← hψk]; infer_instance
  rw [← hψk]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF

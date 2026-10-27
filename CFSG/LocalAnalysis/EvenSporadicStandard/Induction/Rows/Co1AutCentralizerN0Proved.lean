module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31D
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1ModelNorm

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier
  CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Co1Cent

theorem conj_comm_aux {G : Type*} [Group G] (A P S : G)
    (h : A * (P * S * P⁻¹) = P * S * P⁻¹ * A) : P⁻¹ * A * P * S = S * (P⁻¹ * A * P) := by
  calc P⁻¹ * A * P * S = P⁻¹ * (A * (P * S * P⁻¹)) * P := by group
    _ = P⁻¹ * (P * S * P⁻¹ * A) * P := by rw [h]
    _ = S * (P⁻¹ * A * P) := by group

theorem co1AutCentralizerN0_proved
    (hmult : OddMultTrivial .Co1) : Co1AutCentralizerN0 := by
  intro H _ _ L K u N₀ hcov hQ hcan
  have hL : IsSporadic ↥L .Co1 := hcov.isSporadic_of_mult hmult
  have hZ : center ↥L = ⊥ := hcov.center_eq_bot hmult
  obtain ⟨Ψ, hΨ, hΨA, -, hΨu⟩ := co1_model hL hQ
  obtain ⟨p, hpK, hex⟩ := co1_normal_elts hQ hcan hΨ hΨA hΨu
  have hinn := TwoCo1.HypOne.allInner_of_isSporadic hL
  have hconj_inj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h : a * g * a⁻¹ = b * g * b⁻¹ := by
        have := congrArg (fun f : MulAut ↥L => f g) hab
        simpa [MulAut.conj_apply] using this
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h]
        _ = a⁻¹ * b * g := by group
    rw [hZ] at hmem
    exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 hmem)
  have hconj_surj : Function.Surjective (MulAut.conj : ↥L →* MulAut ↥L) := fun α =>
    (hinn α).imp fun g hg => hg.symm
  let eInn : ↥L ≃* MulAut ↥L := MulEquiv.ofBijective MulAut.conj ⟨hconj_inj, hconj_surj⟩
  let P : GL24 := ιC p
  let Θ : ↥(autCentralizer L N₀) →* GL24 := (MulAut.conj P⁻¹).toMonoidHom.comp
    (Ψ.comp (eInn.symm.toMonoidHom.comp (autCentralizer L N₀).subtype))
  have hΘ : ∀ x, Θ x = P⁻¹ * Ψ (eInn.symm (x : MulAut ↥L)) * P := fun x => rfl
  have hΘinj : Function.Injective Θ :=
    (MulAut.conj P⁻¹).injective.comp (hΨ.comp (eInn.symm.injective.comp
      (autCentralizer L N₀).subtype_injective))
  have hPA : P ∈ GA := (p : GA).2
  have hΘA : ∀ x, Θ x ∈ GA := fun x => by
    rw [hΘ]
    exact GA.mul_mem (GA.mul_mem (GA.inv_mem hPA) (hΨA _)) hPA
  have hΘc : ∀ x, ∀ j < 6, Θ x * ιC (sElt j) = ιC (sElt j) * Θ x := by
    intro x j hj
    obtain ⟨k, hkN, hkc⟩ := hex j hj
    have hg : MulAut.conj (eInn.symm (x : MulAut ↥L)) = (x : MulAut ↥L) :=
      eInn.apply_symm_apply (x : MulAut ↥L)
    have hxk := x.2 k hkN
    rw [← hg] at hxk
    have hcomm : eInn.symm (x : MulAut ↥L) * k = k * eInn.symm (x : MulAut ↥L) := by
      have h1 : eInn.symm (x : MulAut ↥L) * k * (eInn.symm (x : MulAut ↥L))⁻¹ = k := hxk
      calc eInn.symm (x : MulAut ↥L) * k = (eInn.symm (x : MulAut ↥L) * k *
          (eInn.symm (x : MulAut ↥L))⁻¹) * eInn.symm (x : MulAut ↥L) := by group
        _ = k * eInn.symm (x : MulAut ↥L) := by rw [h1]
    have h2 := congrArg Ψ hcomm
    rw [map_mul, map_mul, hkc] at h2
    rw [hΘ]
    exact conj_comm_aux (Ψ (eInn.symm (x : MulAut ↥L))) P (ιC (sElt j)) (by
      simpa [P, map_mul, map_inv] using h2)
  have : Finite ↥(autCentralizer L N₀) := Finite.of_injective Θ hΘinj
  obtain ⟨h1, h2, h3⟩ := cent_structure Θ hΘinj hΘA hΘc
  exact ⟨h1, h2, fun E hE _ => h3 E hE⟩

end CFSG.EvenSporadicStandard.Induction

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem sec63PT_exists_induced_aut {Y P : Type} [Group Y] [Group P] {ρ : Y →* P}
    (hρ : Function.Surjective ρ) {σ : MulAut Y} (hσ : σ * σ = 1)
    (hker : ∀ n ∈ ρ.ker, σ n ∈ ρ.ker) :
    ∃ α : MulAut P, (∀ y, ρ (σ y) = α (ρ y)) ∧ α * α = 1 := by
  have hk : ρ.ker ≤ (ρ.comp σ.toMonoidHom).ker := fun n hn => hker n hn
  let α₀ : P →* P := ρ.liftOfSurjective hρ ⟨ρ.comp σ.toMonoidHom, hk⟩
  have hα₀ : ∀ y, α₀ (ρ y) = ρ (σ y) := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨ρ.comp σ.toMonoidHom, hk⟩ y
  have hα₀₀ : ∀ p, α₀ (α₀ p) = p := by
    intro p
    obtain ⟨y, rfl⟩ := hρ p
    rw [hα₀, hα₀, aut_apply_apply hσ]
  let α : MulAut P :=
    { toFun := α₀
      invFun := α₀
      left_inv := hα₀₀
      right_inv := hα₀₀
      map_mul' := map_mul α₀ }
  refine ⟨α, fun y => (hα₀ y).symm, ?_⟩
  ext p
  exact hα₀₀ p

theorem sec63PT_exists_induced_aut_quotient {A P : Type} [Group A] [Finite A] [Group P]
    (e : A ⧸ oddCore A ≃* P) {σ : MulAut A} (hσ : σ * σ = 1) :
    ∃ α : MulAut P, (∀ a : A, e (QuotientGroup.mk (σ a)) = α (e (QuotientGroup.mk a))) ∧
      α * α = 1 := by
  let ρ : A →* P := e.toMonoidHom.comp (QuotientGroup.mk' (oddCore A))
  have hρsurj : Function.Surjective ρ :=
    e.surjective.comp (QuotientGroup.mk'_surjective (oddCore A))
  have hker_eq : ρ.ker = oddCore A := by
    ext n
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk n) = 1 ↔ n ∈ oddCore A
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hker : ∀ n ∈ ρ.ker, σ n ∈ ρ.ker := by
    intro n hn
    rw [hker_eq] at hn ⊢
    exact map_oddCore_le σ (Subgroup.mem_map_of_mem σ.toMonoidHom hn)
  obtain ⟨α, hα, hα2⟩ := sec63PT_exists_induced_aut hρsurj hσ hker
  exact ⟨α, fun a => hα a, hα2⟩

theorem sec63PT_eq_one_of_induced_eq_one {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (hker : ρ.ker ≤ center A) (hperf : commutator A = ⊤) {σ : MulAut A}
    (h : ∀ a, ρ (σ a) = ρ a) : σ = 1 := by
  have hmem : ∀ a : A, a⁻¹ * σ a ∈ center A := by
    intro a
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, h a, inv_mul_cancel]
  let z : A →* A :=
    { toFun := fun a => a⁻¹ * σ a
      map_one' := by simp
      map_mul' := fun s t => by
        have ht := Subgroup.mem_center_iff.mp (hmem s)
        calc (s * t)⁻¹ * σ (s * t) = t⁻¹ * (s⁻¹ * σ s) * σ t := by
              rw [map_mul]; group
          _ = s⁻¹ * σ s * (t⁻¹ * σ t) := by
              rw [ht t⁻¹]; group }
  have hzc : ∀ s, z s ∈ center A := hmem
  have hcomm : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ ≤ z.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hab := Subgroup.mem_center_iff.mp (hzc a) (z b)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hab.symm
  rw [commutator_def] at hperf
  rw [hperf] at hcomm
  refine MulEquiv.ext fun s => ?_
  have hs : z s = 1 := hcomm (Subgroup.mem_top s)
  change s⁻¹ * σ s = 1 at hs
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp hs).symm

theorem sec63PT_oddCore_le_center {A P : Type} [Group A] [Finite A] [Group P] [Nontrivial P]
    (hq : IsQuasisimple A) (e : A ⧸ oddCore A ≃* P) : oddCore A ≤ center A := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (oddCore_normal (G := A)) with h | h
  · exfalso
    haveI : Subsingleton (A ⧸ oddCore A) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton P := e.toEquiv.symm.subsingleton
    exact absurd (inferInstance : Nontrivial P)
      (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton P))
  · exact h

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

theorem exists_fixed_in_plane (hS : PlaneSys V W) {F : Subgroup X} (hF : ActsElemAb V F)
    (hpl : ∀ f : normalizer (V : Set X), (f : X) ∈ F → planeHom hS f = 1) (i : Fin 4) :
    ∃ e ∈ W i, e ≠ 1 ∧ ∀ f ∈ F, f * e * f⁻¹ = e := by
  classical
  have hsqW : ∀ a ∈ W i, a * a = 1 := fun a ha => hS.sq a (hS.le i ha)
  have hinvol : ∀ f ∈ F, InvolAct (W i) f := by
    intro f hf
    have hfn : f ∈ normalizer (V : Set X) := hF.le_normalizer hf
    refine ⟨fun a ha => ?_, fun a ha => hF.sq f hf a (hS.le i ha)⟩
    have h1 : planeHom hS ⟨f, hfn⟩ i = i := by rw [hpl ⟨f, hfn⟩ hf]; rfl
    exact (mem_plane_conj_iff hS ⟨f, hfn⟩ h1 a).mpr ha
  haveI : Finite (W i) := Nat.finite_of_card_ne_zero (by rw [hS.card i]; norm_num)
  by_cases hex : ∃ f ∈ F, ActsNontriv (W i) f
  · obtain ⟨f₀, hf₀, hn₀⟩ := hex
    have hcard : Nat.card {a : W i // f₀ * (a : X) * f₀⁻¹ = a} = 2 :=
      card_fixed_of_actsNontriv (hS.card i) hsqW (hinvol f₀ hf₀) hn₀
    haveI : Nontrivial {a : W i // f₀ * (a : X) * f₀⁻¹ = a} :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
    obtain ⟨e, he1⟩ := exists_ne (⟨1, by simp⟩ : {a : W i // f₀ * (a : X) * f₀⁻¹ = a})
    have he1' : (e.1 : X) ≠ 1 := fun h => he1 (Subtype.ext (Subtype.ext h))
    have hfix0 : f₀ * (e.1 : X) * f₀⁻¹ = e.1 := e.2
    refine ⟨e.1, e.1.2, he1', fun f hf => ?_⟩
    by_cases hfn : ActsNontriv (W i) f
    · have hcomm : ∀ a ∈ W i, f₀ * f * a * (f₀ * f)⁻¹ = f * f₀ * a * (f * f₀)⁻¹ :=
        fun a ha => hF.comm f₀ hf₀ f hf a (hS.le i ha)
      have hmul := actsNontriv_mul_iff (hS.card i) hsqW (hinvol f₀ hf₀) (hinvol f hf) hcomm
      have hnot : ¬ ActsNontriv (W i) (f₀ * f) := by
        intro h
        exact (hmul.mp h).mp hn₀ hfn
      have h1 := not_actsNontriv_iff.mp hnot e.1 e.1.2
      calc f * (e.1 : X) * f⁻¹ = f₀⁻¹ * (f₀ * f * (e.1 : X) * (f₀ * f)⁻¹) * f₀ := by group
        _ = f₀⁻¹ * (e.1 : X) * f₀ := by rw [h1]
        _ = f₀⁻¹ * (f₀ * (e.1 : X) * f₀⁻¹) * f₀ := by rw [hfix0]
        _ = e.1 := by group
    · exact not_actsNontriv_iff.mp hfn e.1 e.1.2
  · push_neg at hex
    haveI : Nontrivial (W i) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hS.card i]; norm_num)
    obtain ⟨e, he1⟩ := exists_ne (1 : W i)
    refine ⟨e, e.2, fun h => he1 (Subtype.ext h), fun f hf => ?_⟩
    exact not_actsNontriv_iff.mp (hex f hf) e e.2

end CFSG.OddStandard.SmallF3.Omega

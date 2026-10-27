module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Card

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B : Subgroup G} {z : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z)

include H W

theorem ThCyc.exists_mul_of_mem_normalizer {g : G} (hgt : g * t * g⁻¹ = z * t)
    {r : G} (hr : r ∈ normalizer ((W5 A t : Subgroup G) : Set G)) :
    ∃ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ ∃ b ∈ Bp A t, r = n * b := by
  have hrA : ∀ x ∈ A, r * x * r⁻¹ ∈ A := fun x hx => H.W5_normalizer_mem W hgt hr hx
  have hinj : ∀ x ∈ A, ∀ y ∈ A, r * x * r⁻¹ = r * y * r⁻¹ → x = y := fun x _ y _ h => by
    simpa using h
  obtain ⟨n, hnL, hn⟩ := W.surj (fun y => r * y * r⁻¹) hrA
    (fun x _ y _ => by group) hinj
  have hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A := fun x hx => by rw [hn x hx]; exact hrA x hx
  have hnN := H.mem_normalizer_W5_of_L W hnL hnA
  refine ⟨n, hnL, hnA, n⁻¹ * r, ⟨mem_centralizer_iff.2 fun x hx => ?_, ?_⟩, by group⟩
  · have := hn x hx
    calc x * (n⁻¹ * r) = n⁻¹ * (n * x * n⁻¹) * r := by group
      _ = n⁻¹ * (r * x * r⁻¹) * r := by rw [this]
      _ = n⁻¹ * r * x := by group
  · have hN : n⁻¹ * r ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
      (normalizer _).mul_mem ((normalizer _).inv_mem hnN) hr
    exact hN

end

end CFSG.EvenSporadicStandard.ThStd

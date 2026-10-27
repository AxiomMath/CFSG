module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftGroup

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly.LowTwoRank

section Semilinear

variable {K : Type} [Field K] [Finite K] {n : ℕ} {Y : Type} [Group Y] {L : Subgroup Y}

theorem semilinear_conj_mem_liftGroup (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n 2 K →* ↥L) {E : Subgroup Y} {t : Y} (htE : ∀ u ∈ E, t * u * t⁻¹ ∈ E)
    {φ : K ≃+* K} {At : GL (Fin n) K}
    (hAt : At ∈ isoGroup (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK
      le_rfl) n)
    (hreal : ∀ g : StatedSU n 2 K, ∃ g' : StatedSU n 2 K,
      (g' : GL (Fin n) K) = At * glAut φ (g : GL (Fin n) K) * At⁻¹ ∧
        t * (ρ g : Y) * t⁻¹ = (ρ g' : Y))
    {A : GL (Fin n) K} (hA : A ∈ liftGroup hK ρ E) :
    At * glAut φ A * At⁻¹ ∈ liftGroup hK ρ E := by
  set h := CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl with hh
  obtain ⟨hAiso, u, hu, hr⟩ := hA
  refine ⟨mul_mem (mul_mem hAt (glAut_mem_primeFormUnitary h isPrimeFormGram_one φ hAiso))
    (inv_mem hAt), t * u * t⁻¹, htE u hu, fun g => ?_⟩
  let σ := conjSUSemi h φ hAt
  have hσinj : Function.Injective σ := fun g₁ g₂ hg => by
    have h1 := congrArg Subtype.val hg
    simp only [σ, coe_conjSUSemi] at h1
    apply Subtype.ext
    exact (glAut φ).injective (mul_left_cancel (mul_right_cancel h1))
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  obtain ⟨g₁, rfl⟩ := hσsurj g
  obtain ⟨g₂, hg₂, hρ₂⟩ := hr g₁
  obtain ⟨g₃, hg₃, hρ₃⟩ := hreal g₂
  obtain ⟨g₄, hg₄, hρ₄⟩ := hreal g₁
  have hg₄' : g₄ = σ g₁ := Subtype.ext hg₄
  refine ⟨g₃, ?_, ?_⟩
  · rw [hg₃, hg₂]
    simp only [σ, coe_conjSUSemi, map_mul, map_inv]
    group
  · rw [← hg₄']
    calc t * u * t⁻¹ * (ρ g₄ : Y) * (t * u * t⁻¹)⁻¹
        = t * (u * (t⁻¹ * (ρ g₄ : Y) * t) * u⁻¹) * t⁻¹ := by group
      _ = (ρ g₃ : Y) := by
        have h5 : t⁻¹ * (ρ g₄ : Y) * t = (ρ g₁ : Y) := by
          rw [← hρ₄]; group
        rw [h5, hρ₂, hρ₃]

theorem exists_semilinear_conj_mem_liftGroup {n : ℕ} (hn : 4 ≤ n)
    (hK : Nat.card K = (2 ^ 1) ^ 2) (ρ : StatedSU n 2 K →* ↥L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n 2 K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n 2 K)))
    {E : Subgroup Y} {t : Y} (ht : t ∈ Subgroup.normalizer (L : Set Y))
    (htE : t ∈ Subgroup.normalizer (E : Set Y)) :
    ∃ (φ : K ≃+* K) (At : GL (Fin n) K), φ ^ 2 = 1 ∧
      At ∈ isoGroup (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n ∧
      (∀ g : StatedSU n 2 K, ∃ g' : StatedSU n 2 K,
        (g' : GL (Fin n) K) = At * glAut φ (g : GL (Fin n) K) * At⁻¹ ∧
          t * (ρ g : Y) * t⁻¹ = (ρ g' : Y)) ∧
      ∀ A ∈ liftGroup hK ρ E, At * glAut φ A * At⁻¹ ∈ liftGroup hK ρ E := by
  obtain ⟨φ, At, hφ, hiso, -, hreal⟩ := exists_semilinear_conj_of_normalizer hn hK ρ e hρe ht
  exact ⟨φ, At, hφ, (mem_primeFormUnitary_one_iff_isometry _ At).mpr hiso, hreal,
    fun A hA => semilinear_conj_mem_liftGroup hK ρ
      (fun u hu => (Subgroup.mem_normalizer_iff.mp htE u).mp hu)
      ((mem_primeFormUnitary_one_iff_isometry _ At).mpr hiso) hreal hA⟩

end Semilinear

end CFSG.HardMathSupport.Curtis.UnitaryLevi

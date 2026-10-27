module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.ConjSylow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree

variable {S : Type*} [Group S]

theorem real3_of_gen [Finite S] {ι : Type} [Fintype ι] {x y : S} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (f : ι → S) (σx σy : ι → ι) (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ Subgroup.closure ({x, y} : Set S)) (h1 : ∃ i, f i = 1)
    (hσx : ∀ i, f i * x = f (σx i)) (hσy : ∀ i, f i * y = f (σy i)) (n : ℕ)
    (hcard : Fintype.card ι = 3 ^ n) (hS : ¬ 3 ^ (n + 1) ∣ Nat.card S)
    (htt : ∀ i, ∃ t, t * f i * t⁻¹ = (f i)⁻¹) : Real3 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup S := Subgroup.closure ({x, y} : Set S) with hPdef
  have hxi : x⁻¹ = x * x :=
    inv_eq_of_mul_eq_one_right (by calc x * (x * x) = x ^ 3 := (pow_three x).symm
      _ = 1 := hx3)
  have hyi : y⁻¹ = y * y :=
    inv_eq_of_mul_eq_one_right (by calc y * (y * y) = y ^ 3 := (pow_three y).symm
      _ = 1 := hy3)
  have hsurj : ∀ g ∈ P, ∃ i, f i = g := by
    intro g hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact h1
    | mul_right g hg s hs ih =>
      obtain ⟨i, rfl⟩ := ih
      rcases hs with rfl | hs
      · exact ⟨σx i, (hσx i).symm⟩
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact ⟨σy i, (hσy i).symm⟩
    | mul_inv_cancel g hg s hs ih =>
      obtain ⟨i, rfl⟩ := ih
      rcases hs with rfl | hs
      · exact ⟨σx (σx i), by rw [hxi, ← mul_assoc, hσx, hσx]⟩
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact ⟨σy (σy i), by rw [hyi, ← mul_assoc, hσy, hσy]⟩
  have hP : Nat.card P = 3 ^ n := by
    have hbij : Function.Bijective fun i : ι => (⟨f i, hmem i⟩ : P) :=
      ⟨fun i j h => hf (congrArg Subtype.val h), fun g => by
        obtain ⟨i, hi⟩ := hsurj g g.2
        exact ⟨i, Subtype.ext hi⟩⟩
    have : Nat.card P = Nat.card ι := (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    rw [this, Nat.card_eq_fintype_card, hcard]
  intro g hg
  by_cases h1 : g = 1
  · exact ⟨1, by simp [h1]⟩
  · obtain ⟨h, hh⟩ := ThetaSpor.exists_conj_mem_of_orderOf_prime_sylow 3 n P hP hS
      (orderOf_eq_prime hg h1)
    obtain ⟨i, hi⟩ := hsurj _ hh
    obtain ⟨t, ht⟩ := htt i
    refine ⟨h * t * h⁻¹, ?_⟩
    calc h * t * h⁻¹ * g * (h * t * h⁻¹)⁻¹ = h * (t * (h⁻¹ * g * h) * t⁻¹) * h⁻¹ := by group
      _ = g⁻¹ := by rw [← hi, ht, hi]; group

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree

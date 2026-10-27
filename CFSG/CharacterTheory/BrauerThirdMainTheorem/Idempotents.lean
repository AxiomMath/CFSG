module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Characters
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open CFSG
open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem idempotentCoeff_eq_sum {G : Type*} [Group G] [Finite G]
    {characters : Set (G → ℂ)} (hcharacters : characters ⊆ BlocksIrr G) (element : G) :
    BlocksIdempotentCoeff G characters element =
      ∑ character ∈ ((irr_finite G).subset hcharacters).toFinset,
        character 1 / (Nat.card G : ℂ) * character element⁻¹ := by
  classical
  apply finsum_mem_eq_sum_of_subset
  · intro character hcharacter
    simpa only [Finset.mem_coe, Set.Finite.mem_toFinset] using hcharacter.1
  · intro character hcharacter
    simpa only [Finset.mem_coe, Set.Finite.mem_toFinset] using hcharacter

theorem idempotentCoeff_conj {G : Type*} [Group G] [Finite G]
    {characters : Set (G → ℂ)} (hcharacters : characters ⊆ BlocksIrr G)
    (element conjugator : G) :
    BlocksIdempotentCoeff G characters (conjugator * element * conjugator⁻¹) =
      BlocksIdempotentCoeff G characters element := by
  classical
  rw [idempotentCoeff_eq_sum hcharacters, idempotentCoeff_eq_sum hcharacters]
  apply Finset.sum_congr rfl
  intro character hcharacter
  have hcharacterIrr := hcharacters (by simpa only [Set.Finite.mem_toFinset] using hcharacter)
  rw [show (conjugator * element * conjugator⁻¹)⁻¹ =
      conjugator * element⁻¹ * conjugator⁻¹ by group]
  rw [irr_conj hcharacterIrr]

theorem admissible_central {G : Type*} [Group G] [Finite G] (m : Ideal BlocksAlgInt)
    {characters : Set (G → ℂ)} (hcharacters : BlocksAdmissible m G characters) :
    BlocksIsCentralR m (BlocksIdempotentCoeff G characters) := by
  exact ⟨hcharacters.2, idempotentCoeff_conj hcharacters.1⟩

theorem centralChar_idempotentCoeff {G : Type*} [Group G] [Finite G]
    {characters : Set (G → ℂ)} (hcharacters : characters ⊆ BlocksIrr G)
    {character : G → ℂ} (hcharacter : character ∈ BlocksIrr G) :
    BlocksCentralChar character (BlocksIdempotentCoeff G characters) =
      if character ∈ characters then 1 else 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hdegree := irr_degree_ne_zero hcharacter
  let finiteCharacters := ((irr_finite G).subset hcharacters).toFinset
  have hcoeff (element : G) : BlocksIdempotentCoeff G characters element =
      ∑ candidate ∈ finiteCharacters, candidate 1 / (Nat.card G : ℂ) * candidate element⁻¹ :=
    idempotentCoeff_eq_sum hcharacters element
  unfold BlocksCentralChar
  rw [finsum_eq_sum_of_fintype]
  simp_rw [hcoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (candidate : G → ℂ) (hcandidate : candidate ∈ finiteCharacters) :
      (∑ element : G, (candidate 1 / (Nat.card G : ℂ) * candidate element⁻¹) *
        character element) = if candidate = character then character 1 else 0 := by
    have hcandidateIrr := hcharacters
      (by simpa only [finiteCharacters, Set.Finite.mem_toFinset] using hcandidate)
    have horth := irr_orthogonality hcharacter hcandidateIrr
    rw [finsum_eq_sum_of_fintype] at horth
    calc
      (∑ element : G, (candidate 1 / (Nat.card G : ℂ) * candidate element⁻¹) *
        character element) = candidate 1 *
          ((Nat.card G : ℂ)⁻¹ * ∑ element : G, character element * candidate element⁻¹) := by
            simp only [div_eq_mul_inv, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro element _
            ring
      _ = candidate 1 * (if character = candidate then 1 else 0) := by
        by_cases hequal : character = candidate
        · rw [ite_eq_left hequal] at horth ⊢
          exact congrArg (fun value : ℂ => candidate 1 * value) horth
        · rw [ite_eq_right hequal] at horth ⊢
          exact congrArg (fun value : ℂ => candidate 1 * value) horth
      _ = if candidate = character then character 1 else 0 := by
        by_cases hequal : candidate = character
        · subst candidate
          simp
        · simp [hequal, Ne.symm hequal]
  rw [Finset.sum_congr rfl hterm]
  by_cases hmember : character ∈ characters
  · have hfiniteMember : character ∈ finiteCharacters := by
      simpa only [finiteCharacters, Set.Finite.mem_toFinset] using hmember
    simp only [Finset.sum_ite_eq', hfiniteMember, ↓reduceIte, hmember]
    exact div_self hdegree
  · have hfiniteNonmember : character ∉ finiteCharacters := by
      simpa only [finiteCharacters, Set.Finite.mem_toFinset] using hmember
    simp only [Finset.sum_ite_eq', hfiniteNonmember, ↓reduceIte, zero_div, hmember]

end CFSG.BrauerThirdMainTheorem.Helpers

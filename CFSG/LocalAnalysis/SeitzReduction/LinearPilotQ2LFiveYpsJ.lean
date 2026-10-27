module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsRad
import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type*} [Field F]

@[expose] def ypsRadSpace (X : Subgroup (unitriangular 5 F))
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hcent : ∀ g : unitriangular 5 F, (∀ x ∈ X, g * x = x * g) → g ∈ X) :
    Submodule F (Matrix (Fin 5) (Fin 5) F) where
  carrier := {N | ∃ x ∈ X, ypsMat x - 1 = N}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    have hN := (isStrictUpperFive_ypsMat_sub_one x).add (isStrictUpperFive_ypsMat_sub_one y)
    refine ⟨uFiveElt _ hN, hcent _ fun z hz => ypsMat_injective ?_, by
      rw [ypsMat_uFiveElt, add_sub_cancel_left]⟩
    have hxz := congrArg ypsMat (hcomm x hx z hz)
    have hyz := congrArg ypsMat (hcomm y hy z hz)
    rw [ypsMat_mul, ypsMat_mul] at hxz hyz
    rw [ypsMat_mul, ypsMat_mul, ypsMat_uFiveElt]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hxz, hyz]
  zero_mem' := ⟨1, X.one_mem, by rw [ypsMat_one, sub_self]⟩
  smul_mem' := by
    rintro a _ ⟨x, hx, rfl⟩
    have hN := (isStrictUpperFive_ypsMat_sub_one x).smul a
    refine ⟨uFiveElt _ hN, hcent _ fun z hz => ypsMat_injective ?_, by
      rw [ypsMat_uFiveElt, add_sub_cancel_left]⟩
    have hxz := congrArg ypsMat (hcomm x hx z hz)
    rw [ypsMat_mul, ypsMat_mul] at hxz
    rw [ypsMat_mul, ypsMat_mul, ypsMat_uFiveElt]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, one_mul,
      mul_one, hxz]

section Rad

variable {X : Subgroup (unitriangular 5 F)} {hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x}
  {hcent : ∀ g : unitriangular 5 F, (∀ x ∈ X, g * x = x * g) → g ∈ X}

theorem sub_one_mem_ypsRadSpace_iff {x : unitriangular 5 F} :
    ypsMat x - 1 ∈ ypsRadSpace X hcomm hcent ↔ x ∈ X := by
  refine ⟨fun ⟨y, hy, h⟩ => ?_, fun hx => ⟨x, hx, rfl⟩⟩
  rwa [ypsMat_injective (sub_left_injective h)] at hy

theorem brkFive_mem_ypsRadSpace (hnorm : X.Normal) {a b : Fin 5} (hab : a < b)
    {N : Matrix (Fin 5) (Fin 5) F} (hN : N ∈ ypsRadSpace X hcomm hcent) :
    brkFive a b N ∈ ypsRadSpace X hcomm hcent := by
  obtain ⟨x, hx, rfl⟩ := hN
  set g := uFiveRoot a b hab (1 : F)
  have hy : g * x * g⁻¹ ∈ X := hnorm.conj_mem x hx g
  have hE : single a b (1 : F) * ypsMat x * single a b 1 = 0 := by
    rw [single_mul_mul_single, ypsMat_apply_of_lt x hab, mul_zero, zero_mul, single_zero]
  have key : brkFive a b (ypsMat x - 1) = (ypsMat (g * x * g⁻¹) - 1) - (ypsMat x - 1) := by
    rw [ypsMat_mul, ypsMat_mul, uFiveRoot_inv, ypsMat_uFiveRoot, ypsMat_uFiveRoot, ← single_neg]
    rw [show (1 + single a b (1 : F)) * ypsMat x * (1 + -single a b 1) = ypsMat x +
        single a b 1 * ypsMat x - ypsMat x * single a b 1 -
          single a b 1 * ypsMat x * single a b 1 by noncomm_ring, hE]
    unfold brkFive
    noncomm_ring
  rw [key]
  exact Submodule.sub_mem _ ⟨_, hy, rfl⟩ ⟨x, hx, rfl⟩

theorem isUFiveRadicalSpace_ypsRadSpace [CharP F 2] [Finite F] (hF : Nat.card F = 4)
    (hnorm : X.Normal) (hsq : ∀ x ∈ X, x * x = 1) (hcard : Nat.card X = 2 ^ 8) :
    IsUFiveRadicalSpace (ypsRadSpace X hcomm hcent) where
  strictUpper := by
    rintro _ ⟨x, -, rfl⟩
    exact isStrictUpperFive_ypsMat_sub_one x
  comm := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := congrArg ypsMat (hcomm x hx y hy)
    rw [ypsMat_mul, ypsMat_mul] at h
    simp only [sub_mul, mul_sub, one_mul, mul_one, h]
    abel
  sq := by
    rintro _ ⟨x, hx, rfl⟩
    have h := congrArg ypsMat (hsq x hx)
    rw [ypsMat_mul, ypsMat_one] at h
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    rw [show (ypsMat x - 1) * (ypsMat x - 1) = ypsMat x * ypsMat x - ypsMat x - ypsMat x + 1 by
      noncomm_ring, h, show (1 : Matrix (Fin 5) (Fin 5) F) - ypsMat x - ypsMat x + 1 =
        (2 : F) • (1 - ypsMat x) by rw [two_smul]; abel, h2, zero_smul]
  brk01 := fun _ hN => brkFive_mem_ypsRadSpace hnorm (by decide) hN
  brk12 := fun _ hN => brkFive_mem_ypsRadSpace hnorm (by decide) hN
  brk23 := fun _ hN => brkFive_mem_ypsRadSpace hnorm (by decide) hN
  brk34 := fun _ hN => brkFive_mem_ypsRadSpace hnorm (by decide) hN
  cent := by
    intro N hN hNJ
    refine ⟨uFiveElt N hN, hcent _ fun z hz => ypsMat_injective ?_, by
      rw [ypsMat_uFiveElt, add_sub_cancel_left]⟩
    have h := hNJ _ ⟨z, hz, rfl⟩
    rw [ypsMat_mul, ypsMat_mul, ypsMat_uFiveElt]
    rw [mul_sub, sub_mul, mul_one, one_mul, sub_eq_sub_iff_add_eq_add, add_comm] at h
    rw [add_mul, mul_add, one_mul, mul_one, add_left_cancel_iff.1 (h.trans (add_comm _ _)).symm]
  finrank_eq := by
    have hbij : Function.Bijective (fun x : X =>
        (⟨ypsMat (x : unitriangular 5 F) - 1, x, x.2, rfl⟩ : ypsRadSpace X hcomm hcent)) := by
      refine ⟨fun x y h => Subtype.ext (ypsMat_injective (sub_left_injective
        (congrArg Subtype.val h))), ?_⟩
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have h1 := Nat.card_congr (Equiv.ofBijective _ hbij)
    rw [hcard, Module.natCard_eq_pow_finrank (K := F), hF] at h1
    have h2 : 4 ^ Module.finrank F (ypsRadSpace X hcomm hcent) = 4 ^ 4 := by
      rw [← h1]
      norm_num
    exact Nat.pow_right_injective (by norm_num) h2

end Rad

theorem apply34_or_apply01_of_radical [CharP F 2] [Finite F] (hF : Nat.card F = 4)
    {X : Subgroup (unitriangular 5 F)} (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hcent : ∀ g : unitriangular 5 F, (∀ x ∈ X, g * x = x * g) → g ∈ X) (hnorm : X.Normal)
    (hsq : ∀ x ∈ X, x * x = 1) (hcard : Nat.card X = 2 ^ 8) :
    (∀ x ∈ X, ypsMat x 3 4 = 0) ∨ ∀ x ∈ X, ypsMat x 0 1 = 0 := by
  have hJ := isUFiveRadicalSpace_ypsRadSpace (hcomm := hcomm) (hcent := hcent) hF hnorm hsq hcard
  rcases hJ.apply34_or_apply01 with h | h
  · exact Or.inl fun x hx => by simpa using h _ ⟨x, hx, rfl⟩
  · exact Or.inr fun x hx => by simpa using h _ ⟨x, hx, rfl⟩

theorem exists_eq_uFiveTwisted [CharP F 2] [Finite F] (hF : Nat.card F = 4)
    {X : Subgroup (unitriangular 5 F)} (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hcent : ∀ g : unitriangular 5 F, (∀ x ∈ X, g * x = x * g) → g ∈ X) (hnorm : X.Normal)
    (hsq : ∀ x ∈ X, x * x = 1) (hcard : Nat.card X = 2 ^ 8)
    (h34 : ∀ x ∈ X, ypsMat x 3 4 = 0) : ∃ e : F, X = uFiveTwisted e := by
  have hJ := isUFiveRadicalSpace_ypsRadSpace (hcomm := hcomm) (hcent := hcent) hF hnorm hsq hcard
  obtain ⟨e, he⟩ := hJ.exists_eq_twistedSpace (by
    rintro _ ⟨x, hx, rfl⟩
    simpa using h34 x hx)
  refine ⟨e, ?_⟩
  ext x
  rw [← sub_one_mem_ypsRadSpace_iff (hcomm := hcomm) (hcent := hcent), he, mem_uFiveTwistedSpace,
    mem_uFiveTwisted]
  simp [isStrictUpperFive_ypsMat_sub_one x]

end CFSG.SeitzReduction.LinearPilot

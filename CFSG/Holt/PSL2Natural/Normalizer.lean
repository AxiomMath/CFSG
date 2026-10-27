module

public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore

public section

namespace CFSG.Holt

open MulAction CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (even_linear_two_involution_normal_forms)
open CFSG.Open (fusionIsSylowIn)

private theorem card_galoisField_two (n : ℕ) : Nat.card (GaloisField 2 n) = 2 ^ max n 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · open Polynomial in
    have : IsSplittingField (ZMod 2) (GaloisField 2 0) (X ^ 2 ^ 0 - X : (ZMod 2)[X]) :=
      inferInstanceAs (IsSplittingField (ZMod 2) (SplittingField (X ^ 2 ^ 0 - X : (ZMod 2)[X])) _)
    have hadj := Polynomial.IsSplittingField.adjoin_rootSet (GaloisField 2 0)
      (Polynomial.X ^ 2 ^ 0 - Polynomial.X : (ZMod 2)[X])
    have h : (Polynomial.X ^ 2 ^ 0 - Polynomial.X : (ZMod 2)[X]) = 0 := by simp
    rw [h, Polynomial.rootSet_zero, Algebra.adjoin_empty] at hadj
    have hsurj : Function.Surjective (algebraMap (ZMod 2) (GaloisField 2 0)) := fun x =>
      Algebra.mem_bot.mp (hadj ▸ Algebra.mem_top)
    rw [← Nat.card_congr (Equiv.ofBijective _ ⟨(algebraMap (ZMod 2) _).injective, hsurj⟩),
      Nat.card_zmod]
    rfl
  · rw [max_eq_left (Nat.one_le_iff_ne_zero.mpr hn), GaloisField.card 2 n hn]

variable {Δ : Type*} {L : Subgroup (Equiv.Perm Δ)} {n : ℕ}

private theorem IsNaturalPSL2.finite (hL : IsNaturalPSL2 L n) : Finite Δ := by
  obtain ⟨-, ψ, -⟩ := hL
  exact Finite.of_equiv _ ψ

private theorem IsNaturalPSL2.odd_card (hL : IsNaturalPSL2 L n) : Odd (Nat.card Δ) := by
  obtain ⟨-, ψ, -⟩ := hL
  rw [← Nat.card_congr ψ, Projectivization.card_of_finrank_two _ _ (Module.finrank_fin_fun _),
    card_galoisField_two]
  exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one

end CFSG.Holt

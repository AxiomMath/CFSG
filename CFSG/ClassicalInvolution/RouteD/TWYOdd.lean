module

public import CFSG.ClassicalInvolution.RouteD.TWYCount
public import CFSG.ClassicalInvolution.RouteD.TwinYR3Classify
public import CFSG.ClassicalInvolution.RouteD.TWYLayer
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Odd

variable {p f : ℕ} [Fact p.Prime]

theorem card_fund_centralizing_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {nY : ℕ} (hn : 4 ≤ nY)
    {R R' : Subgroup (modelUniv .POmegaOdd nY p f Fact.out).K}
    {x x' a a' : (modelUniv .POmegaOdd nY p f Fact.out).K}
    (hd : TwinDatumOn .POmegaOdd (modelUniv .POmegaOdd nY p f Fact.out) R R' x x')
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd nY p f Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd nY p f Fact.out).K) :
    Nat.card {S : Subgroup (modelUniv .POmegaOdd nY p f Fact.out).K //
        S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd nY p f Fact.out).D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set (modelUniv .POmegaOdd nY p f Fact.out).K)} *
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
    2 * framesOdd (p ^ f) (nY - 3) := by
  have he : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd nY p f := ⟨Fact.out, he, by omega, hp2⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadOdd nY (GaloisField p f)),
      oddDatum nY (GaloisField p f)⟩ → ∀ {R R' : Subgroup M.K} {x x' a a' : M.K},
      TwinDatumOn .POmegaOdd M R R' x x' → a ∈ R → a' ∈ R' →
      a * a * x⁻¹ ∈ Subgroup.center M.K → a' * a' * x'⁻¹ ∈ Subgroup.center M.K →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaOdd M.D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set M.K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesOdd (p ^ f) (nY - 3) := by
    intro M hM
    subst hM
    intro R R' x x' a a' hd ha ha' hsq hsq'
    have c := spinCtx_odd hp2 hq hn hadm
    obtain ⟨X, hX, hdim, hcount, -⟩ := card_fund_centralizing_twin c hd ha ha' hsq hsq'
    have hV : Module.finrank (GaloisField p f) (Fin nY ⊕ Fin nY ⊕ Unit → GaloisField p f) =
        2 * nY + 1 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_unit]
      ring
    have hXdim : Module.finrank (GaloisField p f) X = 2 * ((nY - 3) + 2) + 1 := by omega
    have hodd : Odd (Nat.card (GaloisField p f)) := c.hodd
    have hfr := card_frame_regular_odd hodd (nondegenerate_polarBilin_restrict hX) hXdim
    rw [hcount, hfr, hcard]
  exact key _ rfl hd ha ha' hsq hsq'

end Odd

end CFSG.ClassicalInvolution.RouteD.TWY

module

public import CFSG.ClassicalInvolution.RouteD.TWYCount
public import CFSG.ClassicalInvolution.RouteD.TWYType
public import CFSG.ClassicalInvolution.RouteD.TwinYR3Classify
public import CFSG.ClassicalInvolution.RouteD.TWYLayer
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.GroupTheory.WeirSylow (IsPlusType not_isPlusType_quadMinus isPlusType_quadPlus)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Even

variable {t : StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
  {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)}

theorem card_fund_centralizing_even (c : SpinCtx t Q D) {m : ℕ}
    (hdim : Module.finrank F (ι → F) = 2 * m) {R R' : Subgroup (spinGroup Q)}
    {x x' a a' : spinGroup Q} (hd : TwinDatumOn t ⟨spinGroup Q, D⟩ R R' x x') (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ((IsPlusType Q ↔ IsSquare (-1 : F)) →
      Nat.card {S : Subgroup (spinGroup Q) // S ∈ fundamentalSubgroups t D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set (spinGroup Q))} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) =
      2 * framesPlus (Nat.card F) (m - 3)) ∧
    (¬ (IsPlusType Q ↔ IsSquare (-1 : F)) →
      Nat.card {S : Subgroup (spinGroup Q) // S ∈ fundamentalSubgroups t D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set (spinGroup Q))} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) =
      2 * framesMinus (Nat.card F) (m - 4)) := by
  obtain ⟨X, hX, hXd, hcount, W, hc, horth, hW, hWd, hWt⟩ :=
    card_fund_centralizing_twin c hd ha ha' hsq hsq'
  have hV := c.hV
  have hXd' : Module.finrank F X = 2 * (m - 1) := by omega
  have hnd := nondegenerate_polarBilin_restrict hX
  have htype := isPlusType_iff_of_isCompl hc horth hX hW (a := m - 1) (b := 1) (by omega) le_rfl
    hXd' (by omega)
  have hPX : IsPlusType (Q.restrict X) ↔ (IsPlusType Q ↔ IsSquare (-1 : F)) := by
    have h1 := htype
    have h2 := hWt
    tauto
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rw [hcount, card_frame_regular_plus hnd (j := m - 3) (by omega) (hPX.mpr hs)]
  · rw [hcount, card_frame_regular_minus c.hodd hnd (j := m - 4) (by omega)
      (fun h => hs (hPX.mp h))]

end Even

section Models

variable {p f : ℕ} [Fact p.Prime]

theorem card_fund_centralizing_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {nY : ℕ} (hn : 5 ≤ nY)
    {R R' : Subgroup (modelUniv .POmegaPlus nY p f Fact.out).K}
    {x x' a a' : (modelUniv .POmegaPlus nY p f Fact.out).K}
    (hd : TwinDatumOn .POmegaPlus (modelUniv .POmegaPlus nY p f Fact.out) R R' x x')
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .POmegaPlus nY p f Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .POmegaPlus nY p f Fact.out).K) :
    (IsSquare (-1 : GaloisField p f) →
      Nat.card {S : Subgroup (modelUniv .POmegaPlus nY p f Fact.out).K //
          S ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus nY p f Fact.out).D ∧
            S ≤ Subgroup.centralizer ({a * a'} :
              Set (modelUniv .POmegaPlus nY p f Fact.out).K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesPlus (p ^ f) (nY - 3)) ∧
    (¬ IsSquare (-1 : GaloisField p f) →
      Nat.card {S : Subgroup (modelUniv .POmegaPlus nY p f Fact.out).K //
          S ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus nY p f Fact.out).D ∧
            S ≤ Subgroup.centralizer ({a * a'} :
              Set (modelUniv .POmegaPlus nY p f Fact.out).K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesMinus (p ^ f) (nY - 4)) := by
  have he : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ nY := by omega
  have hadm : StatedLieAdmissible .POmegaPlus nY p f := ⟨Fact.out, he, by omega⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus nY (GaloisField p f)),
      plusDatum nY (GaloisField p f) hn3⟩ → ∀ {R R' : Subgroup M.K} {x x' a a' : M.K},
      TwinDatumOn .POmegaPlus M R R' x x' → a ∈ R → a' ∈ R' →
      a * a * x⁻¹ ∈ Subgroup.center M.K → a' * a' * x'⁻¹ ∈ Subgroup.center M.K →
      ((IsSquare (-1 : GaloisField p f) →
        Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaPlus M.D ∧
            S ≤ Subgroup.centralizer ({a * a'} : Set M.K)} *
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
        2 * framesPlus (p ^ f) (nY - 3)) ∧
      (¬ IsSquare (-1 : GaloisField p f) →
        Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaPlus M.D ∧
            S ≤ Subgroup.centralizer ({a * a'} : Set M.K)} *
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
        2 * framesMinus (p ^ f) (nY - 4))) := by
    intro M hM
    subst hM
    intro R R' x x' a a' hd ha ha' hsq hsq'
    have c := spinCtx_plus hp2 hq hn hn3 hadm
    have hdim : Module.finrank (GaloisField p f) (Fin nY ⊕ Fin nY → GaloisField p f) =
        2 * nY := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    have hmain := card_fund_centralizing_even c hdim hd ha ha' hsq hsq'
    have hP : IsPlusType (quadPlus nY (GaloisField p f)) := isPlusType_quadPlus _ nY
    rw [hcard] at hmain
    exact ⟨fun hs => hmain.1 (iff_of_true hP hs), fun hs => hmain.2 (fun h => hs (h.mp hP))⟩
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) hd ha ha' hsq hsq'

theorem card_fund_centralizing_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {nY : ℕ} (hn : 5 ≤ nY)
    {R R' : Subgroup (modelUniv .POmegaMinus nY p f Fact.out).K}
    {x x' a a' : (modelUniv .POmegaMinus nY p f Fact.out).K}
    (hd : TwinDatumOn .POmegaMinus (modelUniv .POmegaMinus nY p f Fact.out) R R' x x')
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus nY p f Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus nY p f Fact.out).K) :
    (IsSquare (-1 : GaloisField p f) →
      Nat.card {S : Subgroup (modelUniv .POmegaMinus nY p f Fact.out).K //
          S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus nY p f Fact.out).D ∧
            S ≤ Subgroup.centralizer ({a * a'} :
              Set (modelUniv .POmegaMinus nY p f Fact.out).K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesMinus (p ^ f) (nY - 4)) ∧
    (¬ IsSquare (-1 : GaloisField p f) →
      Nat.card {S : Subgroup (modelUniv .POmegaMinus nY p f Fact.out).K //
          S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus nY p f Fact.out).D ∧
            S ≤ Subgroup.centralizer ({a * a'} :
              Set (modelUniv .POmegaMinus nY p f Fact.out).K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesPlus (p ^ f) (nY - 3)) := by
  have he : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus nY p f := ⟨Fact.out, he, by omega⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have c := spinCtx_minus hp2 hq hn hadm
  have hdim : Module.finrank (GaloisField p f)
      (Fin (nY - 1) ⊕ Fin (nY - 1) ⊕ Fin 2 → GaloisField p f) = 2 * nY := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have hmain := card_fund_centralizing_even c hdim hd ha ha' hsq hsq'
  have hP : ¬ IsPlusType (quadMinus nY (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) := not_isPlusType_quadMinus (by omega) (minusCoeffs_irr p f)
  rw [hcard] at hmain
  exact ⟨fun hs => hmain.2 (fun h => hP (h.mpr hs)), fun hs => hmain.1 (iff_of_false hP hs)⟩

theorem card_fund_centralizing_pm {tY : StatedLieTag}
    (htY : tY = .POmegaPlus ∨ tY = .POmegaMinus) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {nY : ℕ}
    (hn : 5 ≤ nY) {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    {x x' a a' : (modelUniv tY nY p f Fact.out).K}
    (hd : TwinDatumOn tY (modelUniv tY nY p f Fact.out) R R' x x') (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K) :
    ((IsSquare (-1 : GaloisField p f) ↔ tY = .POmegaPlus) →
      Nat.card {S : Subgroup (modelUniv tY nY p f Fact.out).K //
          S ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D ∧
            S ≤ Subgroup.centralizer ({a * a'} : Set (modelUniv tY nY p f Fact.out).K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesPlus (p ^ f) (nY - 3)) ∧
    (¬ (IsSquare (-1 : GaloisField p f) ↔ tY = .POmegaPlus) →
      Nat.card {S : Subgroup (modelUniv tY nY p f Fact.out).K //
          S ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D ∧
            S ≤ Subgroup.centralizer ({a * a'} : Set (modelUniv tY nY p f Fact.out).K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesMinus (p ^ f) (nY - 4)) := by
  rcases htY with rfl | rfl
  · have h := card_fund_centralizing_plus hp2 hq hn hd ha ha' hsq hsq'
    exact ⟨fun hs => h.1 (hs.mpr rfl), fun hs => h.2 (fun hS => hs (iff_of_true hS rfl))⟩
  · have h := card_fund_centralizing_minus hp2 hq hn hd ha ha' hsq hsq'
    have hne : (StatedLieTag.POmegaMinus = StatedLieTag.POmegaPlus) = False := by simp
    refine ⟨fun hs => h.2 (fun hS => ?_), fun hs => h.1 ?_⟩
    · have := hs.mp hS
      rw [hne] at this
      exact this
    · by_contra hS
      exact hs (by rw [hne]; exact iff_of_false hS id)

end Models

end CFSG.ClassicalInvolution.RouteD.TWY

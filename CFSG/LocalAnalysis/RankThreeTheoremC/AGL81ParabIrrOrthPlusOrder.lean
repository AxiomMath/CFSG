module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusAut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusLevi
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthPlus

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem sq_mem_orthElementaryGroup [CharP K 2] (hr : 3 ≤ r) {h : GLV r K}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) :
    h ^ 2 ∈ orthElementaryGroup (quadPlus r K) := by
  have hT : ∃ T : Submodule K (Fin r ⊕ Fin r → K),
      Module.finrank K T = 3 ∧ ∀ x ∈ T, quadPlus r K x = 0 :=
    ⟨flag r K 3, finrank_flag_of_le hr, flag_singular 3⟩
  obtain ⟨-, -, -, -, -, hsq, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts
      (nondegenerate_polarBilin_quadPlus r K) hT
  rw [← orthDerived_eq_orthElementary hr]
  exact hsq h hh

theorem pow_card_units_eq_one_of_mem_center {ι : Type} [Fintype ι] [DecidableEq ι] {z : GL ι K}
    (hz : z ∈ Subgroup.center (GL ι K)) : z ^ Nat.card Kˣ = 1 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨a, rfl⟩ := hz
  rw [← map_pow, pow_card_eq_one', map_one]

variable [CharP K 2]

theorem exists_pow_eq_one_of_central_blocks (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) {t m : ℕ} (ht : t = 0 ∨ t ∈ D) (hDt : ∀ d ∈ D, d ≤ t)
    (htm : t + m = r) {h : GLV r K} (hh : h ∈ plusFlagStabO K r D)
    (hb : ∀ (b : ℕ) (hb : b ∈ D),
      plusEBlockHomO (fun d hd => (hD d hd).2) hb ⟨h, hh⟩ ∈
        Subgroup.center (GL (Fin (b - predCut D b)) K))
    (hres : plusResBlockHomO (fun d hd => (hD d hd).2) ht htm ⟨h, hh⟩ ∈
      Subgroup.center (GL (Fin m ⊕ Fin m) K)) :
    ∃ j : ℕ, h ^ (2 * Nat.card Kˣ * 2 ^ j) = 1 := by
  set g : ↥(plusFlagStabO K r D) := ⟨h, hh⟩ with hg
  have hmemO : h ^ (2 * Nat.card Kˣ) ∈ plusFlagStabO K r D := pow_mem hh _
  have hE : h ^ (2 * Nat.card Kˣ) ∈ orthElementaryGroup (quadPlus r K) := by
    rw [pow_mul]
    exact pow_mem (sq_mem_orthElementaryGroup hr (mem_plusFlagStabO.1 hh).1) _
  have hQ : h ^ (2 * Nat.card Kˣ) ∈ plusFlagStab K r D := mem_plusFlagStab_iff.2 ⟨hmemO, hE⟩
  have hgpow : (⟨h ^ (2 * Nat.card Kˣ), hmemO⟩ : ↥(plusFlagStabO K r D)) =
      g ^ (2 * Nat.card Kˣ) := rfl
  have hlev : (⟨h ^ (2 * Nat.card Kˣ), hQ⟩ : ↥(plusFlagStab K r D)) ∈
      leviKer (fun d hd => (hD d hd).2) ht htm := by
    refine mem_leviKer.2 ⟨fun b hb' => ?_, ?_⟩
    · change plusEBlockHomO (fun d hd => (hD d hd).2) hb' ⟨h ^ (2 * Nat.card Kˣ), hmemO⟩ = 1
      rw [hgpow, map_pow, pow_mul', pow_card_units_eq_one_of_mem_center (hb b hb'), one_pow]
    · change plusResBlockHomO (fun d hd => (hD d hd).2) ht htm
        ⟨h ^ (2 * Nat.card Kˣ), hmemO⟩ = 1
      rw [hgpow, map_pow, pow_mul', pow_card_units_eq_one_of_mem_center hres, one_pow]
  obtain ⟨j, hj⟩ := isPGroup_leviKer (K := K) (hD := fun d hd => (hD d hd).2) (ht := ht)
    (htm := htm) (fun d hd => (hD d hd).1) hDt ⟨_, hlev⟩
  refine ⟨j, ?_⟩
  have h1 := congrArg (fun y : ↥(leviKer (K := K) (fun d hd => (hD d hd).2) ht htm) =>
    ((y : ↥(plusFlagStab K r D)) : GLV r K)) hj
  simpa [pow_mul] using h1

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthPlus

module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCover
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma82
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem inputL3T_holds : InputL3T := by
  intro G _ _ K g hq hg3 hT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hgN, hgT⟩ := gl_trivOn_iff.1 hT
  set E : Subgroup G := Subgroup.zpowers g with hE
  have hEp : IsPGroup 3 ↥E := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := hx
    have h3 : (g ^ n) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
    have hd : orderOf (g ^ n) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact ⟨0, Subtype.ext (by simpa using orderOf_eq_one_iff.1 h)⟩
    · exact ⟨1, Subtype.ext (by simpa using h3)⟩
  have hEc : Subgroup.centralizer (E : Set G) = Cs g := by
    refine le_antisymm (Subgroup.centralizer_le (by simp [hE])) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    have hc : g * x = x * g := (Subgroup.mem_centralizer_singleton_iff.1 hx).symm
    exact ((Commute.zpow_left (show Commute g x from hc) n)).eq
  have hgD : g ∈ dQ K := by
    refine mem_dQ.2 ⟨hgN, ?_, fun y hy => ?_⟩
    · exact le_normalizer_glaPPrimeCoreOf_of_le_normalizer (p := 3) (X := K)
        (M := Subgroup.zpowers g) (Subgroup.zpowers_le.2 hgN) (Subgroup.mem_zpowers g)
    · have := (GLAPPrimeCoreOf 3 K).inv_mem (hgT y hy)
      simpa [mul_assoc] using this
  have hED : E ≤ dQ K := Subgroup.zpowers_le.2 hgD
  have hq' : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore 3 ↥K) := hq
  have hQ := isQuasisimple_cover hEp hED hq'
  obtain ⟨J, hJ, hJtop, huniq⟩ := exists_glaPComponent_of_isQuasisimple hQ
  have hcore := glaPPrimeCoreOf_cover hEp hED
  rw [hEc] at hJ hJtop huniq hcore
  have hlayer : CLay K g = J :=
    le_antisymm (sSup_le fun L hL => (huniq L hL).le) (le_sSup hJ)
  rw [hlayer]
  refine ⟨hJ, fun k hk => ?_⟩
  obtain ⟨u, hu, hku⟩ := exists_mul_mem_cover hEp hED hk
  rw [hEc] at hku
  have hCK : K ⊓ Cs g ≤ K := inf_le_left
  have hle : barX 3 (K ⊓ Cs g) (K ⊓ Cs g) ≤ barX 3 (K ⊓ Cs g) J := hJtop ▸ le_top
  obtain ⟨j, hj, hjc⟩ := exists_of_barX_le hle hku hku
  have hw : j⁻¹ * (k * u) ∈ GLAPPrimeCoreOf 3 K := by
    rw [hcore] at hjc
    exact hjc.2
  have : k = j * (j⁻¹ * (k * u)) * u⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hj)
    (Subgroup.mem_sup_right hw)) (Subgroup.inv_mem _ (Subgroup.mem_sup_right hu))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

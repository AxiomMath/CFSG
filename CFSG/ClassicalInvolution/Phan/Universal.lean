module

public import CFSG.ClassicalInvolution.Phan.Parabolic
public import CFSG.ClassicalInvolution.Phan.Residues

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits CFSG.Monster.B.Geometry
  CFSG.Monster.B.Geometry.ChamberSystem

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem phanUniversalAt_of_simplyTwoConnected (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hS : (frameSystem (unitaryInvolution K p f) n).SimplyTwoConnected) :
    PhanUniversalAt K p f n := by
  intro Y _ F
  obtain ⟨ψ, hψ, -⟩ := frames_universal_completion hK
    (frameSystem_connected (isUnitaryInvolution_unitaryInvolution hK) hK (by omega)) hS
    (fun J hJ => F.parabolicHom hK J hJ)
    (fun J J' hJ hJ' hJJ' g hgJ' hgJ => F.parabolicHom_compat hK hJ hJ' hJJ' g hgJ' hgJ)
  exact ⟨ψ, F.comp_blockEmb_of_parabolicHom hK (by omega) ψ hψ⟩

theorem phanUniversal_of_simplyTwoConnected
    (hS : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p],
      Nat.card K = (p ^ f) ^ 2 → 5 ≤ p ^ f → ∀ n : ℕ, 3 ≤ n →
        (frameSystem (unitaryInvolution K p f) n).SimplyTwoConnected) :
    PhanUniversal :=
  fun K _ _ p f _ _ hK hq _ hn =>
    phanUniversalAt_of_simplyTwoConnected hK hq (hS K p f hK hq _ hn)

end CFSG.ClassicalInvolution.Phan

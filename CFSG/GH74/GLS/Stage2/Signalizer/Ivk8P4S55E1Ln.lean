module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1LnAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Tr

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

theorem e1Core_projectiveSL [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r] (hn : 3 ≤ n)
    (hBT : LieType.BorelTits.Holds (projectiveSL n K) r) : E1Core r (projectiveSL n K) := by
  intro b hb1 hbr hHH E hE hinv
  by_contra hne
  obtain ⟨M, S, hM, hS, hR⟩ := e1_engine hBT b hHH hE hinv hne
  have hmem : M ∈ maximalParabolics (projectiveSL n K) r := ⟨hM, _, ⟨S, rfl⟩, hS⟩
  obtain ⟨W, ⟨hW0, hW1⟩, rfl⟩ :=
    ((maximal_parabolics (K := K) (n := n) r (by omega)).1 ▸ hmem :
      M ∈ projStabilizer '' {W : Submodule K (Fin n → K) | ⊥ < W ∧ W < ⊤})
  have hfix : ∀ x ∈ radProj n K W, b x = x :=
    hR _ (isPGroup_radProj (by omega) W) (radProj_le_projStabilizer W)
      (projStabilizer_le_normalizer_radProj W)
  have hpow := pow_eq_one_of_fix_tvec hn (bot_lt_iff_ne_bot.mp hW0)
    (lt_top_iff_ne_top.mp hW1) b fun v φ h hv hφ =>
      hfix _ ⟨_, tvec_mem_radSL hv hφ, rfl⟩
  have h1 : orderOf b ∣ r := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp h1 with h | h
  · exact hb1 (orderOf_eq_one_iff.mp h)
  · exact hbr (h ▸ dvd_refl r)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

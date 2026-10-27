module

public import CFSG.LieType.BorelExponent.Defs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public section

namespace CFSG.LieType.BorelExponent

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem pow_card_sub_one_mem_projUnipotent {r : ℕ} {K : Type} [Field K] [Finite K]
    {b : CFSG.Open.StatedProj (CFSG.Open.StatedSp r K)} (hb : b ∈ projBorel r K) :
    b ^ (Nat.card K - 1) ∈ projUnipotent r K := by
  obtain ⟨g, hg, rfl⟩ := hb
  exact ⟨_, pow_mem_of_ker_eq (diagHom r K) ker_diagHom (fun _ => units_pi_pow_card_sub_one _) hg,
    map_pow _ _ _⟩

theorem borelExponentAt_PSp : BorelExponentAt .PSp := by
  intro X _ _ m f hadm hLie
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hLie (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hm : 1 ≤ m := by
    have h := hadm
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 hm
  refine HasBorelExponent.of_mulEquiv e.symm (hasBorelExponent_of_sylow P ?_)
  intro x hx
  rw [hP, SymplecticHigher.normalizer_projUnipotent 2 hm] at hx
  rw [hP]
  have h := pow_card_sub_one_mem_projUnipotent hx
  rwa [hcard] at h

end CFSG.LieType.BorelExponent

end

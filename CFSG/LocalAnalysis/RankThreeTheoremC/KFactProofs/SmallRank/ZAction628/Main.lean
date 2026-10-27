module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.ExtraspecialR
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.FiveCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.SevenCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.ThreeCase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

theorem kFactZAction628_holds : KFactZAction628 := by
  intro K _ _ p f hp hf hp2 hf2 hfp S X N z hS hX hNX hNn hXN hzp hz1 hzS hSX hSN hR hC hCz hrk3 _
  have h : Setup628 p f S X N z :=
    ⟨hp, hf, hp2, hf2, hfp, hS, hX, hNX, hNn, hXN, hzp, hz1, hzS, hSX, hSN, hR, hC, hCz⟩
  obtain ⟨t, hExt, hzt, hfix⟩ := R_isExt2 h
  obtain ⟨k, hk⟩ := hExt.card_eq
  have hk3 : k ≤ 3 := rank_bound h hrk3 hExt hk
  have hk1 : 1 ≤ k := k_pos h hExt hzt hk
  have hzR : z ∈ normalizer ((RR S z : Subgroup K) : Set K) :=
    normalizer_commutator_ge_left _ _ (mem_zpowers z)
  have hdvd := p_dvd_pow_sub_one hp hp2 hzp hzR hExt hzt hk hfix
  have hstar : ∀ A : Subgroup K, A ≤ RR S z → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z :=
    fun A hAR hAc hzA => z_centralizes_abelian h (hAR.trans (RR_le_S hzS)) hAc hzA
  have h3 : p = 3 → k = 1 := by
    intro hp3
    subst hp3
    have h8 := card_le_eight_of_three hExt hzp hzR hzt hfix hstar
    rw [hk] at h8
    have h8' : 2 ^ (1 + 2 * k) ≤ 2 ^ 3 := by simpa using h8
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h8'
    omega
  have h7 : p = 7 → k = 3 → False := by
    intro hp7 hk3'
    subst hp7
    subst hk3'
    exact seven_false hExt hzp hzR hzt hfix hstar (by simpa using hk)
  rcases p_cases hp hp2 hk1 hk3 hdvd h3 h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Or.inl rfl, fun _ => shape_three hExt (by simpa using hk) hzp hzR hzt hfix,
      fun h5 => absurd h5 (by norm_num)⟩
  · exact ⟨Or.inr rfl, fun h3' => absurd h3' (by norm_num),
      fun _ => shape_five hExt (by simpa using hk) hzp hzR hzt hfix hstar⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

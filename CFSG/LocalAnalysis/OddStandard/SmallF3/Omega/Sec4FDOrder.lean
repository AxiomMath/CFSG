module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4FD_not_dvd_four (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    {w : OGroup Q} (hww : w * w = 1) (hw4 : invDim w = 4) {H : Subgroup (OGroup Q)}
    (hH : H ≤ Subgroup.centralizer ({w} : Set (OGroup Q))) : ¬ 25920 ∣ Nat.card H := by
  intro hdvd
  have hdvdC : 25920 ∣ Nat.card (Subgroup.centralizer ({w} : Set (OGroup Q))) :=
    dvd_trans hdvd (Subgroup.card_dvd_of_le hH)
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) w
  have hU : Module.finrank (ZMod 3) (commSp w) = 4 := by simpa only [invDim] using hw4
  have hW : Module.finrank (ZMod 3) (fixSp w) = 3 := by omega
  have hC := natCard_centralizer_involution hQ hww
  rw [natCard_oGroup_three (nondegenerate_restrict_fixSp hQ hww) hW] at hC
  rcases Int.units_eq_one_or (quadSign (Q.restrict (commSp w))) with hs | hs
  · rw [natCard_oGroup_four_plus (nondegenerate_restrict_commSp hQ hww) hU hs] at hC
    rw [hC] at hdvdC
    exact absurd hdvdC (by norm_num)
  · rw [natCard_oGroup_four_minus (nondegenerate_restrict_commSp hQ hww) hU hs] at hC
    rw [hC] at hdvdC
    exact absurd hdvdC (by norm_num)

theorem sec4FD_types_of_dvd (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    {u : OGroup Q} (huΩ : u ∈ omegaGroup hQ) (huu : u * u = 1) (hu1 : u ≠ 1)
    {H : Subgroup (OGroup Q)} (hH : H ≤ Subgroup.centralizer ({u} : Set (OGroup Q)))
    (hdvd : 25920 ∣ Nat.card H) : invType u = (2, -1) ∨ invType u = (6, -1) := by
  obtain ⟨hev, hsign⟩ := (involution_mem_omegaGroup_iff hQ huu).mp huΩ
  have hle : invDim u ≤ 7 := by rw [← hdim]; exact invDim_le u
  have hne0 : invDim u ≠ 0 := fun h => hu1 ((invDim_eq_zero_iff huu).mp h)
  have hcases : invDim u = 2 ∨ invDim u = 4 ∨ invDim u = 6 := by
    obtain ⟨k, hk⟩ := hev
    have hk1 : 1 ≤ k := by omega
    have hk3 : k ≤ 3 := by omega
    interval_cases k
    · left; omega
    · right; left; omega
    · right; right; omega
  rcases hcases with h2 | h4 | h6
  · left
    simp only [invType]
    apply Prod.ext
    · exact h2
    · rw [hsign, h2]; decide
  · exfalso
    exact sec4FD_not_dvd_four hQ hdim huu h4 hH hdvd
  · right
    simp only [invType]
    apply Prod.ext
    · exact h6
    · rw [hsign, h6]; decide

end CFSG.OddStandard.SmallF3.Omega

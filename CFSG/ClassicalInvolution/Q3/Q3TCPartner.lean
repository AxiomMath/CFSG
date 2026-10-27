module

public import CFSG.ClassicalInvolution.Q3.Q3TCCtx
public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement


namespace TCtx3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem exists_partner (c : TCtx3 tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hne : (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D).Nonempty) :
    ∃ β ∈ Ω, (∃ t : G, IsClassicalMember3 β t) ∧
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) ∧ HasFixedMember Ω K β z := by
  obtain ⟨R₁, hR₁⟩ := hne
  obtain ⟨M, hMz, hMK, hMQ, hMR⟩ := c.exists_member_of_fund hR₁
  obtain ⟨R₂, hR₂, W₂, hW₂⟩ := c.hY.std R₁ hR₁
  obtain ⟨N', hN'z, hN'K, hN'Q, hN'R⟩ := c.exists_member_of_fund hR₂
  obtain ⟨W₂', hW₂'⟩ := c.stdPair_of_fund hMz hN'z hW₂ hMR hN'R
  have hnc : ¬ Commutes M N' := not_commutes_of_linearBlockStandardPair hW₂'
  have hN'M : N' ≠ M := fun e => ne_of_linearBlockStandardPair hW₂' e.symm
  obtain ⟨g, hg⟩ := hsingle M hMz.1
  have hzx : IsClassicalMember3 M (g * z * g⁻¹) := by
    rw [hg]
    exact c.hz.conj g
  have hP1_x : LocalOddCentral Ω {g * z * g⁻¹} :=
    Gaps.localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
  have hO3_x : LocalOddThreeFree3 Ω (g * z * g⁻¹) :=
    localOddThreeFree3_conj c.hΩ.conjInvariant g z c.hO3
  obtain ⟨dx', hQx⟩ := exists_dictT2_of_member3 c.hY hMz.1 hzx
    (ShapeDictT2.conj3 c.hΩ.conjInvariant g c.d)
  let cx : TCtx3 tY nY Ω M (g * z * g⁻¹) :=
    { hΩ := c.hΩ, hex := c.hex, hK := hMz.1, hz := hzx, hP1 := hP1_x, hO3 := hO3_x,
      d := dx', hQ₀ := hQx, hY := c.hY }
  have hKM : Commutes K M := c.commutes_K_of_ne hMz hMK
  have hKx : K ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    mem_centralizingMembers_of_commutes c.hK hzx.mem hKM
  have hKM' : K ≠ M := hMK.symm
  by_cases hKQ : locImg Ω (g * z * g⁻¹) K ≤ dx'.Q₁
  · exfalso
    have hcomm : ∀ N ∈ centralizingMembers Ω {g * z * g⁻¹}, N ≠ K → Commutes K N :=
      fun N hN hNK => cx.commutes_T_of_ne hKx hKQ hN hNK
    have hconj : ∃ g' : G, K = conjSub g' M :=
      ⟨g⁻¹, by rw [hg, ← conjSub_mul, inv_mul_cancel, conjSub_one]⟩
    have heq := centralizingMembers_eq_of_twin3 c.hΩ hzx c.hz hconj hKx hcomm
    have hN'x : N' ∈ centralizingMembers Ω {g * z * g⁻¹} := heq ▸ hN'z
    exact hnc (cx.commutes_K_of_ne hN'x hN'M)
  · obtain ⟨R₀, hR₀, hKR₀⟩ := cx.exists_fund_of_ne hKx hKM' hKQ
    obtain ⟨R', hR', W, hW⟩ := c.hY.std R₀ hR₀
    obtain ⟨β, hβx, hβM, hβQ, hβR⟩ := cx.exists_member_of_fund hR'
    obtain ⟨W', hW'⟩ := cx.stdPair_of_fund hKx hβx hW hKR₀ hβR
    obtain ⟨t, ht⟩ := c.hΩ.classical β hβx.1
    exact ⟨β, hβx.1, ⟨t, ht⟩, ⟨W', hW'⟩, M, hMz.1, hKM, (cx.commutes_K_of_ne hβx hβM).symm,
      fun hall => hnc (hall N' hN'z hN'M)⟩

end TCtx3

end CFSG.ClassicalInvolution.Q3.Q3TC

module

public import CFSG.ClassicalInvolution.Q3.Q3EXGlue
public import CFSG.ClassicalInvolution.Q3.Q3EPCtx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.WeakCT


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem partner_involution_commutes3 (c : ETCtx3 tY nY Ω K z) {β : Subgroup G} {t : G}
    (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) :
    t * z * t⁻¹ = z := by
  obtain ⟨W, hW⟩ := hKβ
  have hzt : z * t = t * z :=
    Gaps.standardPair_involutions_commute two_ne_zero_gf3 hW c.hz.mem htβ.mem
      c.hz.orderOf_eq_two htβ.orderOf_eq_two
  rw [mul_inv_eq_iff_eq_mul]
  exact hzt.symm

theorem not_commutes_twin_of_partner3 (c : ETCtx3 tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model tY nY) Ω z)
    (hT : FundTwinsExist (modelFund 3 1 tY nY)) (hDC : FundHubUnique (modelFund 3 1 tY nY))
    {M M' β : Subgroup G} (hM : M ∈ centralizingMembers Ω {z}) (hMK : M ≠ K)
    (hM' : M' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K} (hR : R ∈ modelFund 3 1 tY nY)
    (hR' : R' ∈ modelFund 3 1 tY nY) (hMR : locImg Ω z M = R.map c.d.ψ)
    (hM'R' : locImg Ω z M' = R'.map c.d.ψ) (htw : IsFundTwin (modelFund 3 1 tY nY) R R')
    (hβ : β ∈ Ω) (hKβne : K ≠ β) (hKβ : ¬ Commutes K β) (hβM : Commutes β M) :
    ¬ Commutes β M' := by
  classical
  intro hβM'
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hM.1
  obtain ⟨cx⟩ := exists_ctx_member3 c hsingle hshape hM.1 hxM
  obtain ⟨hM'x, RK, Rt, hRK, hRt, hKR, hM'R, htwin⟩ :=
    twin_triangle3 c hT hDC hM hMK hM' hR hR' hMR hM'R' htw hxM cx
  have hKM : Commutes K M := c.commutes_K_of_ne hM hMK
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hβMne : β ≠ M := by
    rintro rfl
    exact not_commutes_self3 hxM hβM
  obtain ⟨Rβ, hRβ, hβR⟩ := cx.exists_fund_of_ne hβx hβMne
  have hRβt : Commutes Rβ Rt := (cx.commutes_iff_fund hβx hM'x hRβ hβR hM'R).mp hβM'
  rcases (htwin.2.2 Rβ hRβ).mpr (Or.inr hRβt) with h1 | h1
  · exact hKβne (cx.eq_of_locImg_eq hKx hβx (by rw [hKR, hβR, h1]))
  · exact hKβ ((cx.commutes_iff_fund hβx hKx hRβ hβR hKR).mpr h1).symm

theorem false_of_twin_fixed3 (c : ETCtx3 tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model tY nY) Ω z)
    (hne : (modelFund 3 1 tY nY).Nonempty)
    (hgen : c.d.ψ.range ≤ ⨆ R ∈ modelFund 3 1 tY nY, R.map c.d.ψ)
    (hT : FundTwinsExist (modelFund 3 1 tY nY)) (hDC : FundHubUnique (modelFund 3 1 tY nY))
    (hL : FundTwinFixed (modelFund 3 1 tY nY)) : False := by
  classical
  obtain ⟨ι, -, D, -⟩ := id hshape
  obtain ⟨R₀, hR₀⟩ := hne
  obtain ⟨M, hM, hMK, hMR⟩ := c.exists_member_of_fund hR₀
  obtain ⟨β, hβ, hKβ, hβM⟩ :=
    c.exists_partner_transport hsingle hM.1 hMK (c.commutes_K_of_ne hM hMK)
  obtain ⟨t, ht⟩ := c.hΩ.classical β hβ
  obtain ⟨W, hW⟩ := hKβ
  have htz : t * z * t⁻¹ = z := partner_involution_commutes3 c ht ⟨W, hW⟩
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K :=
    Gaps.conjSub_eq_of_standardPair two_ne_zero_gf3 hW ht.mem ht.orderOf_eq_two
  obtain ⟨R₀', hR₀', htw⟩ := hT R₀ hR₀
  obtain ⟨M', hM', hM'K, hM'R'⟩ := c.exists_member_of_fund hR₀'
  have hσ2 : ∀ y, Gaps.locAut c.hΩ.conjInvariant htz
      (Gaps.locAut c.hΩ.conjInvariant htz y) = y :=
    Gaps.locAut_locAut c.hΩ.conjInvariant htz h2t
  have hσr : ∀ k, Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ k) ∈ c.d.ψ.range :=
    fun k => c.locAut_mem_range htz h2t hKt hgen k
  have hfix : ∀ x ∈ locImg Ω z M, Gaps.locAut c.hΩ.conjInvariant htz x = x :=
    c.fixed_of_commutes htz ht hM hβM
  have hfix' : ∀ r ∈ R₀, Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r := fun r hr =>
    hfix _ (by rw [hMR]; exact ⟨r, hr, rfl⟩)
  have hfixt := hL c.d.ψ c.d.ker_le (Gaps.locAut c.hΩ.conjInvariant htz) hσ2 hσr R₀ hR₀ R₀' hR₀'
    htw hfix'
  have hM't : M' ≤ Subgroup.centralizer ({t} : Set G) := by
    refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 htz hM').mpr fun a ha => ?_
    rw [hM'R'] at ha
    obtain ⟨r, hr, rfl⟩ := ha
    exact hfixt r hr
  have hcomm : Commutes β M' :=
    c.commutes_partner_of_centralizes (Gaps.fundNoncentral 3) hsingle D hβ ht ⟨W, hW⟩ hM' hM't
      (c.commutes_K_of_ne hM' hM'K)
  exact not_commutes_twin_of_partner3 c hsingle hshape hT hDC hM hMK hM' hR₀ hR₀' hMR hM'R' htw
    hβ (ne_of_linearBlockStandardPair hW) (not_commutes_of_linearBlockStandardPair hW) hβM hcomm

end CFSG.ClassicalInvolution.Q3.Q3W.EX

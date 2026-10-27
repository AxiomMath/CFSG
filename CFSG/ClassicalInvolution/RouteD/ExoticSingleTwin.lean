module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternBasic
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyBase
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

section Facts

variable {KY : Type} [Group KY]

@[expose] def IsFundTwin (𝓕 : Set (Subgroup KY)) (R R' : Subgroup KY) : Prop :=
  R ≠ R' ∧ Commutes R R' ∧ ∀ S ∈ 𝓕, (S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R')

@[expose] def IsHub (𝓕 : Set (Subgroup KY)) (R S : Subgroup KY) : Prop :=
  S ≠ R ∧ Commutes S R ∧ ∀ S' ∈ 𝓕, Commutes S' R → S' ≠ S → Commutes S' S

@[expose] def FundTwinsExist (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ R ∈ 𝓕, ∃ R' ∈ 𝓕, IsFundTwin 𝓕 R R'

@[expose] def FundHubUnique (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ R ∈ 𝓕, ∀ S₁ ∈ 𝓕, ∀ S₂ ∈ 𝓕, IsHub 𝓕 R S₁ → IsHub 𝓕 R S₂ → S₁ = S₂

@[expose] def FundTwinFixed (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ {X : Type} [Group X] (ψ : KY →* X), ψ.ker ≤ Subgroup.center KY →
    ∀ σ : X ≃* X, (∀ x, σ (σ x) = x) → (∀ k, σ (ψ k) ∈ ψ.range) →
    ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, IsFundTwin 𝓕 R R' → (∀ r ∈ R, σ (ψ r) = ψ r) →
      ∀ r ∈ R', σ (ψ r) = ψ r

theorem IsFundTwin.isHub {𝓕 : Set (Subgroup KY)} {R R' : Subgroup KY} (h : IsFundTwin 𝓕 R R') :
    IsHub 𝓕 R R' := by
  refine ⟨h.1.symm, h.2.1.symm, fun S' hS' hc _ => ?_⟩
  rcases (h.2.2 S' hS').mp (Or.inr hc) with rfl | hc'
  · exact absurd rfl ‹_›
  · exact hc'

end Facts

abbrev modelFund (p f : ℕ) [Fact p.Prime] (tY : StatedLieTag) (nY : ℕ) :
    Set (Subgroup (modelUniv tY nY p f Fact.out).K) :=
  fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem twin_triangle (c : ETCtx p f tY nY Ω K z)
    (hT : FundTwinsExist (modelFund p f tY nY)) (hDC : FundHubUnique (modelFund p f tY nY))
    {M M' : Subgroup G} (hM : M ∈ centralizingMembers Ω {z}) (hMK : M ≠ K)
    (hM' : M' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K} (hR : R ∈ modelFund p f tY nY)
    (hR' : R' ∈ modelFund p f tY nY) (hMR : locImg Ω z M = R.map c.d.ψ)
    (hM'R' : locImg Ω z M' = R'.map c.d.ψ) (htw : IsFundTwin (modelFund p f tY nY) R R')
    {xM : G} (hxM : IsClassicalMember p f M xM) (cx : ETCtx p f tY nY Ω M xM) :
    M' ∈ centralizingMembers Ω {xM} ∧ ∃ RK Rt : Subgroup (modelUniv tY nY p f Fact.out).K,
      RK ∈ modelFund p f tY nY ∧ Rt ∈ modelFund p f tY nY ∧ locImg Ω xM K = RK.map cx.d.ψ ∧
        locImg Ω xM M' = Rt.map cx.d.ψ ∧ IsFundTwin (modelFund p f tY nY) RK Rt := by
  classical
  have hKM : Commutes K M := c.commutes_K_of_ne hM hMK
  have hKx : K ∈ centralizingMembers Ω {xM} := mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hKM' : K ≠ M := fun h => hMK h.symm
  obtain ⟨RK, hRK, hKR⟩ := cx.exists_fund_of_ne hKx hKM'
  obtain ⟨Rt, hRt, htwin⟩ := hT RK hRK
  obtain ⟨N, hN, hNM, hNR⟩ := cx.exists_member_of_fund hRt
  have hKN : Commutes K N := (cx.commutes_iff_fund hKx hN hRK hKR hNR).mpr htwin.2.1
  have hNz : N ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN.1 c.hz.mem hKN.symm
  have hNK : N ≠ K := by
    intro h
    rw [h] at hNR
    exact htwin.1 (eq_of_map_eq_of_perfect cx.d.ψ cx.d.ker_le (cx.hY.perfR RK hRK)
      (cx.hY.perfR Rt hRt) (hKR.symm.trans hNR))
  obtain ⟨RN, hRN, hNzR⟩ := c.exists_fund_of_ne hNz hNK
  have hhub : IsHub (modelFund p f tY nY) R RN := by
    refine ⟨fun h => hNM (c.eq_of_locImg_eq hNz hM (by rw [hNzR, hMR, h])), ?_, ?_⟩
    · have hMN : Commutes M N := cx.commutes_K_of_ne hN hNM
      exact (c.commutes_iff_fund hNz hM hRN hNzR hMR).mp hMN.symm
    · intro S hS hSR hSne
      obtain ⟨N', hN'z, hN'K, hN'S⟩ := c.exists_member_of_fund hS
      have hN'M : Commutes N' M := (c.commutes_iff_fund hN'z hM hS hN'S hMR).mpr hSR
      have hN'x : N' ∈ centralizingMembers Ω {xM} :=
        mem_centralizingMembers_of_commutes hN'z.1 hxM.mem hN'M
      have hN'ne : N' ≠ M := by
        rintro rfl
        exact not_commutes_self_of_mem c.hΩ hM.1 hN'M
      obtain ⟨RN', hRN', hN'R⟩ := cx.exists_fund_of_ne hN'x hN'ne
      have hKN' : Commutes K N' := c.commutes_K_of_ne hN'z hN'K
      have hRKN' : Commutes RK RN' := (cx.commutes_iff_fund hKx hN'x hRK hKR hN'R).mp hKN'
      rcases (htwin.2.2 RN' hRN').mp (Or.inr hRKN'.symm) with h1 | h1
      · exfalso
        apply hSne
        have hNN' : N' = N := cx.eq_of_locImg_eq hN'x hN (by rw [hN'R, hNR, h1])
        have : S.map c.d.ψ = RN.map c.d.ψ := by rw [← hN'S, ← hNzR, hNN']
        exact eq_of_map_eq_of_perfect c.d.ψ c.d.ker_le (c.hY.perfR S hS) (c.hY.perfR RN hRN)
          this
      · have hN'N : Commutes N' N :=
          (cx.commutes_iff_fund hN'x hN hRN' hN'R hNR).mpr h1
        exact (c.commutes_iff_fund hN'z hNz hS hN'S hNzR).mp hN'N
  have hRNR' : RN = R' := hDC R hR RN hRN R' hR' hhub htw.isHub
  have hNM' : N = M' := c.eq_of_locImg_eq hNz hM' (by rw [hNzR, hM'R', hRNR'])
  subst hNM'
  exact ⟨hN, RK, Rt, hRK, hRt, hKR, hNR, htwin⟩

theorem not_commutes_twin_of_partner (c : ETCtx p f tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 tY nY Ω z)
    (hT : FundTwinsExist (modelFund p f tY nY)) (hDC : FundHubUnique (modelFund p f tY nY))
    {M M' β : Subgroup G} (hM : M ∈ centralizingMembers Ω {z}) (hMK : M ≠ K)
    (hM' : M' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K} (hR : R ∈ modelFund p f tY nY)
    (hR' : R' ∈ modelFund p f tY nY) (hMR : locImg Ω z M = R.map c.d.ψ)
    (hM'R' : locImg Ω z M' = R'.map c.d.ψ) (htw : IsFundTwin (modelFund p f tY nY) R R')
    (hβ : β ∈ Ω) (hKβne : K ≠ β) (hKβ : ¬ Commutes K β) (hβM : Commutes β M) :
    ¬ Commutes β M' := by
  classical
  intro hβM'
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hM.1
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hshape hM.1 hxM
  obtain ⟨hM'x, RK, Rt, hRK, hRt, hKR, hM'R, htwin⟩ :=
    twin_triangle c hT hDC hM hMK hM' hR hR' hMR hM'R' htw hxM cx
  have hKM : Commutes K M := c.commutes_K_of_ne hM hMK
  have hKx : K ∈ centralizingMembers Ω {xM} := mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} := mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hβMne : β ≠ M := by
    rintro rfl
    exact not_commutes_self_of_mem c.hΩ hM.1 hβM
  obtain ⟨Rβ, hRβ, hβR⟩ := cx.exists_fund_of_ne hβx hβMne
  have hRβt : Commutes Rβ Rt := (cx.commutes_iff_fund hβx hM'x hRβ hβR hM'R).mp hβM'
  rcases (htwin.2.2 Rβ hRβ).mpr (Or.inr hRβt) with h1 | h1
  · exact hKβne (cx.eq_of_locImg_eq hKx hβx (by rw [hKR, hβR, h1]))
  · exact hKβ ((cx.commutes_iff_fund hβx hKx hRβ hβR hKR).mpr h1).symm

theorem false_of_twin_fixed (c : ETCtx p f tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 tY nY Ω z)
    (hne : (modelFund p f tY nY).Nonempty)
    (hgen : c.d.ψ.range ≤ ⨆ R ∈ modelFund p f tY nY, R.map c.d.ψ)
    (hT : FundTwinsExist (modelFund p f tY nY)) (hDC : FundHubUnique (modelFund p f tY nY))
    (hL : FundTwinFixed (modelFund p f tY nY)) : False := by
  classical
  have : NeZero f := ⟨c.hf⟩
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField c.hp2 c.hq
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  obtain ⟨R₀, hR₀⟩ := hne
  obtain ⟨M, hM, hMK, hMR⟩ := c.exists_member_of_fund hR₀
  obtain ⟨β, hβ, hKβ, hβM⟩ :=
    c.exists_partner_transport hsingle hM.1 hMK (c.commutes_K_of_ne hM hMK)
  obtain ⟨t, ht⟩ := c.hΩ.classical β hβ
  obtain ⟨W, hW⟩ := hKβ
  have htz : t * z * t⁻¹ = z := partner_involution_commutes c.hp2 c.hz ht ⟨W, hW⟩
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := Gaps.conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  obtain ⟨R₀', hR₀', htw⟩ := hT R₀ hR₀
  obtain ⟨M', hM', hM'K, hM'R'⟩ := c.exists_member_of_fund hR₀'
  have hσ2 : ∀ y, Gaps.locAut c.hΩ.conjInvariant htz (Gaps.locAut c.hΩ.conjInvariant htz y) = y :=
    Gaps.locAut_locAut c.hΩ.conjInvariant htz h2t
  have hσr : ∀ k, Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ k) ∈ c.d.ψ.range :=
    fun k => ETCtx.locAut_mem_range c htz h2t hKt hgen k
  have hMt : M ≤ Subgroup.centralizer ({t} : Set G) := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hβM t ht.mem m hm).symm
  have hfix := (Gaps.locAut_fixed_iff c.hΩ c.hP1 htz hM).mp hMt
  have hfix' : ∀ r ∈ R₀, Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r := fun r hr =>
    hfix _ (by rw [hMR]; exact ⟨r, hr, rfl⟩)
  have hfixt := hL c.d.ψ c.d.ker_le (Gaps.locAut c.hΩ.conjInvariant htz) hσ2 hσr R₀ hR₀ R₀' hR₀'
    htw hfix'
  have hM't : M' ≤ Subgroup.centralizer ({t} : Set G) := by
    refine (Gaps.locAut_fixed_iff c.hΩ c.hP1 htz hM').mpr fun a ha => ?_
    rw [hM'R'] at ha
    obtain ⟨r, hr, rfl⟩ := ha
    exact hfixt r hr
  have hcomm : Commutes β M' :=
    c.commutes_partner_of_centralizes hsingle (Gaps.fundNoncentral p) hS3 hD4 hβ ht ⟨W, hW⟩ hM'
      hM't (c.commutes_K_of_ne hM' hM'K)
  exact not_commutes_twin_of_partner c hsingle hshape hT hDC hM hMK hM' hR₀ hR₀' hMR hM'R' htw hβ
    (ne_of_linearBlockStandardPair hW) (not_commutes_of_linearBlockStandardPair hW) hβM hcomm

end Main

end CFSG.ClassicalInvolution.RouteD.Exotic

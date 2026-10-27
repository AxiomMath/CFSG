module

public import CFSG.ClassicalInvolution.Q3.Q3EXStar
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleGlue

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem exists_inv_of_member3 (c : ETCtx3 tY nY Ω K z) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ modelFund 3 1 tY nY) (hNR : locImg Ω z N = R.map c.d.ψ) {w : G} (hw : w ∈ N)
    (h2 : orderOf w = 2) :
    ∃ r ∈ R, orderOf r = 2 ∧ c.d.ψ r = locElt Ω z w (le_centralizingLayer hN hw) := by
  have hmem := locElt_mem_locImg (le_centralizingLayer hN) hw
  rw [hNR] at hmem
  obtain ⟨r, hr, hrψ⟩ := hmem
  have hord := orderOf_locElt (le_centralizingLayer hN hw) h2
  have hsq : locElt Ω z w (le_centralizingLayer hN hw) *
      locElt Ω z w (le_centralizingLayer hN hw) = 1 := by
    have := pow_orderOf_eq_one (locElt Ω z w (le_centralizingLayer hN hw))
    rwa [hord, pow_two] at this
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [map_one] at hrψ
    rw [← hrψ, orderOf_one] at hord
    omega
  have hrsq : r * r = 1 := by
    have hker : r * r ∈ c.d.ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hrψ]
      exact hsq
    exact c.hY.central R hR (r * r) (R.mul_mem hr hr) (c.d.ker_le hker)
  exact ⟨r, hr, orderOf_eq_prime (by rwa [pow_two]) hr1, hrψ⟩

theorem false_of_central_involution3 (c : ETCtx3 tY nY Ω K z) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) {v : G} (hv : v ∈ L)
    (h2 : orderOf v = 2) (hcen : ∀ y ∈ locLayer Ω z, v * y = y * v) : False := by
  obtain ⟨R, hR, hLR⟩ := c.exists_fund_of_ne hL hLK
  obtain ⟨r, hrR, hr2, hrψ⟩ := exists_inv_of_member3 c hL hR hLR hv h2
  have hψc : ∀ k, c.d.ψ r * c.d.ψ k = c.d.ψ k * c.d.ψ r := by
    intro k
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
      (classicalInvolutionOddCore ↥(locLayer Ω z)) (c.d.ψ k)
    rw [hrψ, ← hy]
    unfold locElt
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcen y.1 y.2)
  set T : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K := ⊤ with hT
  have hperf : ⁅T, T⁆ = T := by
    have := c.hY.perfK.commutator_eq_top
    rwa [commutator_def] at this
  have hcomm : ∀ a ∈ T, a * r = r * a := by
    refine Gaps.commute_of_commutator_central (L := T) hperf (b := r) fun a _ => c.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (hψc a).symm
  have hcenter : r ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K :=
    Subgroup.mem_center_iff.mpr fun a => hcomm a (Subgroup.mem_top a)
  have h1 := c.hY.central R hR r hrR hcenter
  rw [h1, orderOf_one] at hr2
  omega

theorem involution_ne3 (c : ETCtx3 tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model tY nY) Ω z) {N N' : Subgroup G} (hN : N ∈ Ω)
    (hN' : N' ∈ Ω) (hne : N ≠ N') {w w' : G} (hw : IsClassicalMember3 N w)
    (hw' : IsClassicalMember3 N' w') : w ≠ w' := by
  rintro rfl
  obtain ⟨cx⟩ := exists_ctx_member3 c hsingle hshape hN hw
  have hN'w : N' ∈ centralizingMembers Ω {w} := ⟨hN', isSubnormal_le hw'.subnormal⟩
  refine false_of_central_involution3 cx hN'w (fun h => hne h.symm) hw'.mem hw'.orderOf_eq_two ?_
  intro y hy
  have h1 : y ∈ Subgroup.centralizer ({w} : Set G) := centralizingLayer_le_centralizer Ω {w} hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp h1).symm

theorem inv_ne_of_ne3 {J : Subgroup G} {v : G} (d : ETCtx3 tY nY Ω J v)
    (hG1 : ∀ {N N' : Subgroup G}, N ∈ Ω → N' ∈ Ω → N ≠ N' → ∀ {w w' : G},
      IsClassicalMember3 N w → IsClassicalMember3 N' w' → w ≠ w')
    {N N' : Subgroup G} (hN : N ∈ centralizingMembers Ω {v})
    (hN' : N' ∈ centralizingMembers Ω {v}) (hne : N ≠ N') {w w' : G}
    (hw : IsClassicalMember3 N w) (hw' : IsClassicalMember3 N' w')
    {r r' : (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hr : d.d.ψ r = locElt Ω v w (le_centralizingLayer hN hw.mem))
    (hr' : d.d.ψ r' = locElt Ω v w' (le_centralizingLayer hN' hw'.mem)) : r ≠ r' := by
  rintro rfl
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw.orderOf_eq_two, pow_two] at this
  have hww' : w' * w' = 1 := by
    have := pow_orderOf_eq_one w'
    rwa [hw'.orderOf_eq_two, pow_two] at this
  have heq : (⟨w, le_centralizingLayer hN hw.mem⟩ : ↥(locLayer Ω v)) =
      ⟨w', le_centralizingLayer hN' hw'.mem⟩ :=
    eq_of_involutions_of_mk d.hP1 (Subtype.ext hww) (Subtype.ext hww')
      (show locElt Ω v w _ = locElt Ω v w' _ from hr.symm.trans hr')
  exact hG1 hN.1 hN'.1 hne hw hw' (congrArg Subtype.val heq)

theorem eq_of_psi_eq3 (c : ETCtx3 tY nY Ω K z)
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K} (hR : R ∈ modelFund 3 1 tY nY)
    (hR' : R' ∈ modelFund 3 1 tY nY) (h : R.map c.d.ψ = R'.map c.d.ψ) : R = R' :=
  eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.hY.pow3 R hR) (c.hY.pow3 R' hR') h

theorem involution_mul_eq3 {J : Subgroup G} {v : G} (d : ETCtx3 tY nY Ω J v)
    (hTK : TwinInvolutionKernel (modelFund 3 1 tY nY))
    (hG1 : ∀ {N N' : Subgroup G}, N ∈ Ω → N' ∈ Ω → N ≠ N' → ∀ {w w' : G},
      IsClassicalMember3 N w → IsClassicalMember3 N' w' → w ≠ w')
    {N N' L L' : Subgroup G} (hN : N ∈ centralizingMembers Ω {v})
    (hN' : N' ∈ centralizingMembers Ω {v}) (hL : L ∈ centralizingMembers Ω {v})
    (hL' : L' ∈ centralizingMembers Ω {v})
    {R R' S S' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ modelFund 3 1 tY nY) (hR' : R' ∈ modelFund 3 1 tY nY)
    (hS : S ∈ modelFund 3 1 tY nY) (hS' : S' ∈ modelFund 3 1 tY nY)
    (hNR : locImg Ω v N = R.map d.d.ψ) (hN'R : locImg Ω v N' = R'.map d.d.ψ)
    (hLS : locImg Ω v L = S.map d.d.ψ) (hL'S : locImg Ω v L' = S'.map d.d.ψ)
    (htw : IsFundTwin (modelFund 3 1 tY nY) R R') (htw' : IsFundTwin (modelFund 3 1 tY nY) S S')
    {w w' u u' : G} (hw : IsClassicalMember3 N w) (hw' : IsClassicalMember3 N' w')
    (hu : IsClassicalMember3 L u) (hu' : IsClassicalMember3 L' u') : w * w' = u * u' := by
  obtain ⟨ε, hε⟩ := hTK
  have key : ∀ {N N' : Subgroup G} (hN : N ∈ centralizingMembers Ω {v})
      (hN' : N' ∈ centralizingMembers Ω {v})
      {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K} (hR : R ∈ modelFund 3 1 tY nY)
      (hR' : R' ∈ modelFund 3 1 tY nY) (hNR : locImg Ω v N = R.map d.d.ψ)
      (hN'R : locImg Ω v N' = R'.map d.d.ψ) (htw : IsFundTwin (modelFund 3 1 tY nY) R R')
      {w w' : G} (hw : IsClassicalMember3 N w) (hw' : IsClassicalMember3 N' w'),
      w * w' = w' * w ∧ locElt Ω v (w * w') ((locLayer Ω v).mul_mem (le_centralizingLayer hN hw.mem)
        (le_centralizingLayer hN' hw'.mem)) = d.d.ψ ε := by
    intro N N' hN hN' R R' hR hR' hNR hN'R htw w w' hw hw'
    have hNN' : Commutes N N' := (d.commutes_iff_fund hN hN' hR hNR hN'R).mpr htw.2.1
    obtain ⟨r, hrR, hr2, hrψ⟩ := exists_inv_of_member3 d hN hR hNR hw.mem hw.orderOf_eq_two
    obtain ⟨r', hr'R, hr'2, hr'ψ⟩ := exists_inv_of_member3 d hN' hR' hN'R hw'.mem
      hw'.orderOf_eq_two
    refine ⟨hNN' w hw.mem w' hw'.mem, ?_⟩
    rcases hε R hR R' hR' htw r hrR r' hr'R hr2 hr'2 with h | h
    · exfalso
      have hne : N ≠ N' := fun e => htw.1 (eq_of_psi_eq3 d hR hR' (hNR.symm.trans (e ▸ hN'R)))
      exact inv_ne_of_ne3 d hG1 hN hN' hne hw hw' (r := r) (r' := r') hrψ hr'ψ h
    · rw [← locElt_mul (le_centralizingLayer hN hw.mem) (le_centralizingLayer hN' hw'.mem),
        ← hrψ, ← hr'ψ, ← map_mul, h]
  obtain ⟨hc1, k1⟩ := key hN hN' hR hR' hNR hN'R htw hw hw'
  obtain ⟨hc2, k2⟩ := key hL hL' hS hS' hLS hL'S htw' hu hu'
  have hsq_of : ∀ {M : Subgroup G} {x : G}, IsClassicalMember3 M x → x * x = 1 := by
    intro M x hx
    have := pow_orderOf_eq_one x
    rwa [hx.orderOf_eq_two, pow_two] at this
  have hmem1 : w * w' ∈ locLayer Ω v :=
    (locLayer Ω v).mul_mem (le_centralizingLayer hN hw.mem) (le_centralizingLayer hN' hw'.mem)
  have hmem2 : u * u' ∈ locLayer Ω v :=
    (locLayer Ω v).mul_mem (le_centralizingLayer hL hu.mem) (le_centralizingLayer hL' hu'.mem)
  have heq := eq_of_involutions_of_mk d.hP1 (a := ⟨w * w', hmem1⟩) (b := ⟨u * u', hmem2⟩)
    (Subtype.ext (mul_self_of_commute (hsq_of hw) (hsq_of hw') hc1))
    (Subtype.ext (mul_self_of_commute (hsq_of hu) (hsq_of hu') hc2))
    (show locElt Ω v (w * w') hmem1 = locElt Ω v (u * u') hmem2 from k1.trans k2.symm)
  exact congrArg Subtype.val heq

theorem ctx_eq_or_commutes_iff3 (c : ETCtx3 tY nY Ω K z) {N N' : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hN' : N' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K} (hR : R ∈ modelFund 3 1 tY nY)
    (hR' : R' ∈ modelFund 3 1 tY nY) (hNR : locImg Ω z N = R.map c.d.ψ)
    (hN'R' : locImg Ω z N' = R'.map c.d.ψ) :
    (R = R' ∨ Commutes R R') ↔ (N = N' ∨ Commutes N N') := by
  refine or_congr ⟨fun h => ?_, fun h => ?_⟩ (c.commutes_iff_fund hN hN' hR hNR hN'R').symm
  · exact c.eq_of_locImg_eq hN hN' (by rw [hNR, hN'R', h])
  · subst h
    exact eq_of_psi_eq3 c hR hR' (hNR.symm.trans hN'R')

theorem twin_triangle3 (c : ETCtx3 tY nY Ω K z)
    (hT : FundTwinsExist (modelFund 3 1 tY nY)) (hDC : FundHubUnique (modelFund 3 1 tY nY))
    {M M' : Subgroup G} (hM : M ∈ centralizingMembers Ω {z}) (hMK : M ≠ K)
    (hM' : M' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K} (hR : R ∈ modelFund 3 1 tY nY)
    (hR' : R' ∈ modelFund 3 1 tY nY) (hMR : locImg Ω z M = R.map c.d.ψ)
    (hM'R' : locImg Ω z M' = R'.map c.d.ψ) (htw : IsFundTwin (modelFund 3 1 tY nY) R R')
    {xM : G} (hxM : IsClassicalMember3 M xM) (cx : ETCtx3 tY nY Ω M xM) :
    M' ∈ centralizingMembers Ω {xM} ∧ ∃ RK Rt : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K,
      RK ∈ modelFund 3 1 tY nY ∧ Rt ∈ modelFund 3 1 tY nY ∧ locImg Ω xM K = RK.map cx.d.ψ ∧
        locImg Ω xM M' = Rt.map cx.d.ψ ∧ IsFundTwin (modelFund 3 1 tY nY) RK Rt := by
  classical
  have hKM : Commutes K M := c.commutes_K_of_ne hM hMK
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
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
    exact htwin.1 (eq_of_psi_eq3 cx hRK hRt (hKR.symm.trans hNR))
  obtain ⟨RN, hRN, hNzR⟩ := c.exists_fund_of_ne hNz hNK
  have hhub : IsHub (modelFund 3 1 tY nY) R RN := by
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
        exact not_commutes_self3 hxM hN'M
      obtain ⟨RN', hRN', hN'R⟩ := cx.exists_fund_of_ne hN'x hN'ne
      have hKN' : Commutes K N' := c.commutes_K_of_ne hN'z hN'K
      have hRKN' : Commutes RK RN' := (cx.commutes_iff_fund hKx hN'x hRK hKR hN'R).mp hKN'
      rcases (htwin.2.2 RN' hRN').mp (Or.inr hRKN'.symm) with h1 | h1
      · exfalso
        apply hSne
        have hNN' : N' = N := cx.eq_of_locImg_eq hN'x hN (by rw [hN'R, hNR, h1])
        have : S.map c.d.ψ = RN.map c.d.ψ := by rw [← hN'S, ← hNzR, hNN']
        exact eq_of_psi_eq3 c hS hRN this
      · have hN'N : Commutes N' N :=
          (cx.commutes_iff_fund hN'x hN hRN' hN'R hNR).mpr h1
        exact (c.commutes_iff_fund hN'z hNz hS hN'S hNzR).mp hN'N
  have hRNR' : RN = R' := hDC R hR RN hRN R' hR' hhub htw.isHub
  have hNM' : N = M' := c.eq_of_locImg_eq hNz hM' (by rw [hNzR, hM'R', hRNR'])
  subst hNM'
  exact ⟨hN, RK, Rt, hRK, hRt, hKR, hNR, htwin⟩

theorem twin_at_z_of_twin_at_x3 (c : ETCtx3 tY nY Ω K z)
    (hTC : TwinWithinCentralizer (modelFund 3 1 tY nY)) {M : Subgroup G} {xM : G}
    (hM : M ∈ centralizingMembers Ω {z}) (hxM : IsClassicalMember3 M xM)
    (cx : ETCtx3 tY nY Ω M xM) {R₀ : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ modelFund 3 1 tY nY) (hMR : locImg Ω z M = R₀.map c.d.ψ)
    {N N' : Subgroup G} (hN : N ∈ centralizingMembers Ω {xM}) (hNM : N ≠ M)
    (hN' : N' ∈ centralizingMembers Ω {xM}) (hN'M : N' ≠ M)
    {S S' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K} (hS : S ∈ modelFund 3 1 tY nY)
    (hS' : S' ∈ modelFund 3 1 tY nY) (hNS : locImg Ω xM N = S.map cx.d.ψ)
    (hN'S : locImg Ω xM N' = S'.map cx.d.ψ) (htwin : IsFundTwin (modelFund 3 1 tY nY) S S')
    (hNz : N ∈ centralizingMembers Ω {z}) (hN'z : N' ∈ centralizingMembers Ω {z})
    {A B : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hA : A ∈ modelFund 3 1 tY nY) (hB : B ∈ modelFund 3 1 tY nY)
    (hNA : locImg Ω z N = A.map c.d.ψ) (hN'B : locImg Ω z N' = B.map c.d.ψ) :
    IsFundTwin (modelFund 3 1 tY nY) A B := by
  have hNN'ne : N ≠ N' := fun h =>
    htwin.1 (eq_of_psi_eq3 cx hS hS' (hNS.symm.trans (h ▸ hN'S)))
  have hNN' : Commutes N N' := (cx.commutes_iff_fund hN hN' hS hNS hN'S).mpr htwin.2.1
  have hMN : Commutes M N := cx.commutes_K_of_ne hN hNM
  refine hTC R₀ hR₀ A hA B hB
    (fun h => hNN'ne (c.eq_of_locImg_eq hNz hN'z (by rw [hNA, hN'B, h])))
    ((c.commutes_iff_fund hNz hN'z hA hNA hN'B).mp hNN')
    ((c.commutes_iff_fund hNz hM hA hNA hMR).mp hMN.symm)
    ((c.commutes_iff_fund hN'z hM hB hN'B hMR).mp (cx.commutes_K_of_ne hN' hN'M).symm)
    fun T hT' hTR => ?_
  obtain ⟨NT, hNT, hNTK, hNTT⟩ := c.exists_member_of_fund hT'
  have hNTM : Commutes NT M := (c.commutes_iff_fund hNT hM hT' hNTT hMR).mpr hTR
  have hNTx : NT ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hNT.1 hxM.mem hNTM
  have hNTMne : NT ≠ M := by
    rintro rfl
    exact not_commutes_self3 hxM hNTM
  obtain ⟨RT, hRT, hNTR⟩ := cx.exists_fund_of_ne hNTx hNTMne
  rw [ctx_eq_or_commutes_iff3 c hNT hNz hT' hA hNTT hNA,
    ctx_eq_or_commutes_iff3 c hNT hN'z hT' hB hNTT hN'B,
    ← ctx_eq_or_commutes_iff3 cx hNTx hN hRT hS hNTR hNS,
    ← ctx_eq_or_commutes_iff3 cx hNTx hN' hRT hS' hNTR hN'S]
  exact htwin.2.2 RT hRT

theorem false_of_twin_glue3 (c : ETCtx3 tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model tY nY) Ω z)
    (hne : (modelFund 3 1 tY nY).Nonempty) (hT : FundTwinsExist (modelFund 3 1 tY nY))
    (hDC : FundHubUnique (modelFund 3 1 tY nY))
    (hTC : TwinWithinCentralizer (modelFund 3 1 tY nY))
    (hO : FundHasOrthogonal (modelFund 3 1 tY nY))
    (hTK : TwinInvolutionKernel (modelFund 3 1 tY nY)) : False := by
  classical
  have hG1 : ∀ {N N' : Subgroup G}, N ∈ Ω → N' ∈ Ω → N ≠ N' → ∀ {w w' : G},
      IsClassicalMember3 N w → IsClassicalMember3 N' w' → w ≠ w' := by
    intro N N' hN hN' hne w w' hw hw'
    exact involution_ne3 c hsingle hshape hN hN' hne hw hw'
  obtain ⟨R₀, hR₀⟩ := hne
  obtain ⟨M, hM, hMK, hMR⟩ := c.exists_member_of_fund hR₀
  obtain ⟨R₀', hR₀', htw⟩ := hT R₀ hR₀
  obtain ⟨M', hM', hM'K, hM'R'⟩ := c.exists_member_of_fund hR₀'
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hM.1
  obtain ⟨yM, hyM⟩ := c.hΩ.classical M' hM'.1
  obtain ⟨cx⟩ := exists_ctx_member3 c hsingle hshape hM.1 hxM
  obtain ⟨hM'x, RK, Rt, hRK, hRt, hKR, hM'R, htwK⟩ :=
    twin_triangle3 c hT hDC hM hMK hM' hR₀ hR₀' hMR hM'R' htw hxM cx
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem (c.commutes_K_of_ne hM hMK)
  obtain ⟨S, hS, hSne, hSc, hSnt⟩ := hO RK hRK
  obtain ⟨S', hS', htwS⟩ := hT S hS
  have hRKS' : RK = S' ∨ Commutes RK S' := (htwS.2.2 RK hRK).mp (Or.inr hSc.symm)
  have hS'ne : S' ≠ RK := by
    rintro rfl
    exact hSnt htwS.symm
  have hS'c : Commutes S' RK := by
    rcases hRKS' with h | h
    · exact absurd h.symm hS'ne
    · exact h.symm
  obtain ⟨N, hN, hNM, hNS⟩ := cx.exists_member_of_fund hS
  obtain ⟨N', hN', hN'M, hN'S⟩ := cx.exists_member_of_fund hS'
  have hKN : Commutes K N := (cx.commutes_iff_fund hKx hN hRK hKR hNS).mpr hSc.symm
  have hKN' : Commutes K N' := (cx.commutes_iff_fund hKx hN' hRK hKR hN'S).mpr hS'c.symm
  have hNz : N ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN.1 c.hz.mem hKN.symm
  have hN'z : N' ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN'.1 c.hz.mem hKN'.symm
  have hNK : N ≠ K := by
    rintro rfl
    exact hSne (eq_of_psi_eq3 cx hS hRK (hNS.symm.trans hKR))
  have hN'K : N' ≠ K := by
    rintro rfl
    exact hS'ne (eq_of_psi_eq3 cx hS' hRK (hN'S.symm.trans hKR))
  obtain ⟨A, hA, hNA⟩ := c.exists_fund_of_ne hNz hNK
  obtain ⟨B, hB, hN'B⟩ := c.exists_fund_of_ne hN'z hN'K
  have hAB : IsFundTwin (modelFund 3 1 tY nY) A B :=
    twin_at_z_of_twin_at_x3 c hTC hM hxM cx hR₀ hMR hN hNM hN' hN'M hS hS' hNS hN'S htwS hNz
      hN'z hA hB hNA hN'B
  obtain ⟨w, hw⟩ := c.hΩ.classical N hN.1
  obtain ⟨w', hw'⟩ := c.hΩ.classical N' hN'.1
  have e1 : xM * yM = w * w' :=
    involution_mul_eq3 c hTK hG1 hM hM' hNz hN'z hR₀ hR₀' hA hB hMR hM'R' hNA hN'B htw hAB hxM
      hyM hw hw'
  have e2 : z * yM = w * w' :=
    involution_mul_eq3 cx hTK hG1 hKx hM'x hN hN' hRK hRt hS hS' hKR hM'R hNS hN'S htwK htwS
      c.hz hyM hw hw'
  exact hG1 hM.1 c.hK hMK hxM c.hz (mul_right_cancel (e1.trans e2.symm))

theorem clique_prod_eq_one3 {J : Subgroup G} {v : G} (d : ETCtx3 tY nY Ω J v)
    (hCP : FundCliqueProd (modelFund 3 1 tY nY))
    (hG1 : ∀ {N N' : Subgroup G}, N ∈ Ω → N' ∈ Ω → N ≠ N' → ∀ {w w' : G},
      IsClassicalMember3 N w → IsClassicalMember3 N' w' → w ≠ w')
    {N₁ N₂ N₃ N₄ : Subgroup G} (h₁ : N₁ ∈ centralizingMembers Ω {v})
    (h₂ : N₂ ∈ centralizingMembers Ω {v}) (h₃ : N₃ ∈ centralizingMembers Ω {v})
    (h₄ : N₄ ∈ centralizingMembers Ω {v}) (n₁₂ : N₁ ≠ N₂) (n₁₃ : N₁ ≠ N₃) (n₁₄ : N₁ ≠ N₄)
    (n₂₃ : N₂ ≠ N₃) (n₂₄ : N₂ ≠ N₄) (n₃₄ : N₃ ≠ N₄) (c₁₂ : Commutes N₁ N₂)
    (c₁₃ : Commutes N₁ N₃) (c₁₄ : Commutes N₁ N₄) (c₂₃ : Commutes N₂ N₃)
    (c₂₄ : Commutes N₂ N₄) (c₃₄ : Commutes N₃ N₄)
    {R₁ R₂ R₃ R₄ : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR₁ : R₁ ∈ modelFund 3 1 tY nY) (hR₂ : R₂ ∈ modelFund 3 1 tY nY)
    (hR₃ : R₃ ∈ modelFund 3 1 tY nY) (hR₄ : R₄ ∈ modelFund 3 1 tY nY)
    (e₁ : locImg Ω v N₁ = R₁.map d.d.ψ) (e₂ : locImg Ω v N₂ = R₂.map d.d.ψ)
    (e₃ : locImg Ω v N₃ = R₃.map d.d.ψ) (e₄ : locImg Ω v N₄ = R₄.map d.d.ψ)
    {w₁ w₂ w₃ w₄ : G} (hw₁ : IsClassicalMember3 N₁ w₁) (hw₂ : IsClassicalMember3 N₂ w₂)
    (hw₃ : IsClassicalMember3 N₃ w₃) (hw₄ : IsClassicalMember3 N₄ w₄) :
    w₁ * w₂ * w₃ * w₄ = 1 := by
  have neR : ∀ {N N' : Subgroup G} {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K},
      N ∈ centralizingMembers Ω {v} → N' ∈ centralizingMembers Ω {v} →
      locImg Ω v N = R.map d.d.ψ → locImg Ω v N' = R'.map d.d.ψ → N ≠ N' → R ≠ R' := by
    intro N N' R R' hN hN' e e' hne h
    exact hne (d.eq_of_locImg_eq hN hN' (by rw [e, e', h]))
  have comR : ∀ {N N' : Subgroup G} {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K},
      N ∈ centralizingMembers Ω {v} → N' ∈ centralizingMembers Ω {v} →
      R ∈ modelFund 3 1 tY nY → locImg Ω v N = R.map d.d.ψ → locImg Ω v N' = R'.map d.d.ψ →
      Commutes N N' → Commutes R R' := by
    intro N N' R R' hN hN' hR e e' hc
    exact (d.commutes_iff_fund hN hN' hR e e').mp hc
  obtain ⟨r₁, hr₁, hr₁2, hr₁ψ⟩ := exists_inv_of_member3 d h₁ hR₁ e₁ hw₁.mem hw₁.orderOf_eq_two
  obtain ⟨r₂, hr₂, hr₂2, hr₂ψ⟩ := exists_inv_of_member3 d h₂ hR₂ e₂ hw₂.mem hw₂.orderOf_eq_two
  obtain ⟨r₃, hr₃, hr₃2, hr₃ψ⟩ := exists_inv_of_member3 d h₃ hR₃ e₃ hw₃.mem hw₃.orderOf_eq_two
  obtain ⟨r₄, hr₄, hr₄2, hr₄ψ⟩ := exists_inv_of_member3 d h₄ hR₄ e₄ hw₄.mem hw₄.orderOf_eq_two
  have hprod := hCP R₁ hR₁ R₂ hR₂ R₃ hR₃ R₄ hR₄ (neR h₁ h₂ e₁ e₂ n₁₂) (neR h₁ h₃ e₁ e₃ n₁₃)
    (neR h₁ h₄ e₁ e₄ n₁₄) (neR h₂ h₃ e₂ e₃ n₂₃) (neR h₂ h₄ e₂ e₄ n₂₄) (neR h₃ h₄ e₃ e₄ n₃₄)
    (comR h₁ h₂ hR₁ e₁ e₂ c₁₂) (comR h₁ h₃ hR₁ e₁ e₃ c₁₃) (comR h₁ h₄ hR₁ e₁ e₄ c₁₄)
    (comR h₂ h₃ hR₂ e₂ e₃ c₂₃) (comR h₂ h₄ hR₂ e₂ e₄ c₂₄) (comR h₃ h₄ hR₃ e₃ e₄ c₃₄)
    r₁ hr₁ r₂ hr₂ r₃ hr₃ r₄ hr₄ hr₁2 hr₂2 hr₃2 hr₄2
    (inv_ne_of_ne3 d hG1 h₁ h₂ n₁₂ hw₁ hw₂ hr₁ψ hr₂ψ)
    (inv_ne_of_ne3 d hG1 h₁ h₃ n₁₃ hw₁ hw₃ hr₁ψ hr₃ψ)
    (inv_ne_of_ne3 d hG1 h₁ h₄ n₁₄ hw₁ hw₄ hr₁ψ hr₄ψ)
    (inv_ne_of_ne3 d hG1 h₂ h₃ n₂₃ hw₂ hw₃ hr₂ψ hr₃ψ)
    (inv_ne_of_ne3 d hG1 h₂ h₄ n₂₄ hw₂ hw₄ hr₂ψ hr₄ψ)
    (inv_ne_of_ne3 d hG1 h₃ h₄ n₃₄ hw₃ hw₄ hr₃ψ hr₄ψ)
  have hsq_of : ∀ {M : Subgroup G} {x : G}, IsClassicalMember3 M x → x * x = 1 := by
    intro M x hx
    have := pow_orderOf_eq_one x
    rwa [hx.orderOf_eq_two, pow_two] at this
  have m₁ := le_centralizingLayer h₁ hw₁.mem
  have m₂ := le_centralizingLayer h₂ hw₂.mem
  have m₃ := le_centralizingLayer h₃ hw₃.mem
  have m₄ := le_centralizingLayer h₄ hw₄.mem
  have m₁₂ : w₁ * w₂ ∈ locLayer Ω v := (locLayer Ω v).mul_mem m₁ m₂
  have m₁₂₃ : w₁ * w₂ * w₃ ∈ locLayer Ω v := (locLayer Ω v).mul_mem m₁₂ m₃
  have m₁₂₃₄ : w₁ * w₂ * w₃ * w₄ ∈ locLayer Ω v := (locLayer Ω v).mul_mem m₁₂₃ m₄
  have himg : locElt Ω v (w₁ * w₂ * w₃ * w₄) m₁₂₃₄ = 1 := by
    rw [← locElt_mul m₁₂₃ m₄, ← locElt_mul m₁₂ m₃, ← locElt_mul m₁ m₂, ← hr₁ψ, ← hr₂ψ, ← hr₃ψ,
      ← hr₄ψ, ← map_mul, ← map_mul, ← map_mul, hprod, map_one]
  have heq := eq_of_involutions_of_mk d.hP1 (a := ⟨w₁ * w₂ * w₃ * w₄, m₁₂₃₄⟩) (b := 1)
    (Subtype.ext (mul_self_of_commute_four (hsq_of hw₁) (hsq_of hw₂) (hsq_of hw₃) (hsq_of hw₄)
      (c₁₂ w₁ hw₁.mem w₂ hw₂.mem) (c₁₃ w₁ hw₁.mem w₃ hw₃.mem) (c₁₄ w₁ hw₁.mem w₄ hw₄.mem)
      (c₂₃ w₂ hw₂.mem w₃ hw₃.mem) (c₂₄ w₂ hw₂.mem w₄ hw₄.mem) (c₃₄ w₃ hw₃.mem w₄ hw₄.mem)))
    (mul_one 1) (by simpa [locElt] using himg)
  exact congrArg Subtype.val heq

theorem false_of_clique_glue3 (c : ETCtx3 tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model tY nY) Ω z)
    (hne : (modelFund 3 1 tY nY).Nonempty) (hCl : FundHasClique (modelFund 3 1 tY nY))
    (hCP : FundCliqueProd (modelFund 3 1 tY nY)) : False := by
  classical
  have hG1 : ∀ {N N' : Subgroup G}, N ∈ Ω → N' ∈ Ω → N ≠ N' → ∀ {w w' : G},
      IsClassicalMember3 N w → IsClassicalMember3 N' w' → w ≠ w' := by
    intro N N' hN hN' hne w w' hw hw'
    exact involution_ne3 c hsingle hshape hN hN' hne hw hw'
  obtain ⟨R₀, hR₀⟩ := hne
  obtain ⟨M, hM, hMK, hMR⟩ := c.exists_member_of_fund hR₀
  obtain ⟨R₂, hR₂, R₃, hR₃, R₄, hR₄, n02, n03, n04, n23, n24, n34, k02, k03, k04, k23, k24,
    k34⟩ := hCl R₀ hR₀
  obtain ⟨M₂, hM₂, hM₂K, hM₂R⟩ := c.exists_member_of_fund hR₂
  obtain ⟨M₃, hM₃, hM₃K, hM₃R⟩ := c.exists_member_of_fund hR₃
  obtain ⟨M₄, hM₄, hM₄K, hM₄R⟩ := c.exists_member_of_fund hR₄
  have neM : ∀ {N N' : Subgroup G} {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K},
      locImg Ω z N = R.map c.d.ψ → locImg Ω z N' = R'.map c.d.ψ → R ∈ modelFund 3 1 tY nY →
      R' ∈ modelFund 3 1 tY nY → R ≠ R' → N ≠ N' := by
    intro N N' R R' e e' hR hR' hne h
    exact hne (eq_of_psi_eq3 c hR hR' (e.symm.trans (h ▸ e')))
  have comM : ∀ {N N' : Subgroup G} {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K},
      N ∈ centralizingMembers Ω {z} → N' ∈ centralizingMembers Ω {z} →
      R ∈ modelFund 3 1 tY nY → locImg Ω z N = R.map c.d.ψ → locImg Ω z N' = R'.map c.d.ψ →
      Commutes R R' → Commutes N N' := by
    intro N N' R R' hN hN' hR e e' hc
    exact (c.commutes_iff_fund hN hN' hR e e').mpr hc
  have m02 := neM hMR hM₂R hR₀ hR₂ n02
  have m03 := neM hMR hM₃R hR₀ hR₃ n03
  have m04 := neM hMR hM₄R hR₀ hR₄ n04
  have m23 := neM hM₂R hM₃R hR₂ hR₃ n23
  have m24 := neM hM₂R hM₄R hR₂ hR₄ n24
  have m34 := neM hM₃R hM₄R hR₃ hR₄ n34
  have q02 := comM hM hM₂ hR₀ hMR hM₂R k02
  have q03 := comM hM hM₃ hR₀ hMR hM₃R k03
  have q04 := comM hM hM₄ hR₀ hMR hM₄R k04
  have q23 := comM hM₂ hM₃ hR₂ hM₂R hM₃R k23
  have q24 := comM hM₂ hM₄ hR₂ hM₂R hM₄R k24
  have q34 := comM hM₃ hM₄ hR₃ hM₃R hM₄R k34
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hM.1
  obtain ⟨x₂, hx₂⟩ := c.hΩ.classical M₂ hM₂.1
  obtain ⟨x₃, hx₃⟩ := c.hΩ.classical M₃ hM₃.1
  obtain ⟨x₄, hx₄⟩ := c.hΩ.classical M₄ hM₄.1
  have e1 : xM * x₂ * x₃ * x₄ = 1 :=
    clique_prod_eq_one3 c hCP hG1 hM hM₂ hM₃ hM₄ m02 m03 m04 m23 m24 m34 q02 q03 q04 q23 q24 q34
      hR₀ hR₂ hR₃ hR₄ hMR hM₂R hM₃R hM₄R hxM hx₂ hx₃ hx₄
  obtain ⟨cx⟩ := exists_ctx_member3 c hsingle hshape hM.1 hxM
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem (c.commutes_K_of_ne hM hMK)
  have hKM' : K ≠ M := fun h => hMK h.symm
  have inx : ∀ {N : Subgroup G}, N ∈ centralizingMembers Ω {z} → N ≠ K → Commutes N M →
      N ∈ centralizingMembers Ω {xM} := fun hN _ hc =>
    mem_centralizingMembers_of_commutes hN.1 hxM.mem hc
  have hM₂x := inx hM₂ hM₂K q02.symm
  have hM₃x := inx hM₃ hM₃K q03.symm
  have hM₄x := inx hM₄ hM₄K q04.symm
  have ne2 : M₂ ≠ M := fun h => m02 h.symm
  have ne3 : M₃ ≠ M := fun h => m03 h.symm
  have ne4 : M₄ ≠ M := fun h => m04 h.symm
  obtain ⟨RK, hRK, hKR⟩ := cx.exists_fund_of_ne hKx hKM'
  obtain ⟨B₂, hB₂, hM₂B⟩ := cx.exists_fund_of_ne hM₂x ne2
  obtain ⟨B₃, hB₃, hM₃B⟩ := cx.exists_fund_of_ne hM₃x ne3
  obtain ⟨B₄, hB₄, hM₄B⟩ := cx.exists_fund_of_ne hM₄x ne4
  have e2 : z * x₂ * x₃ * x₄ = 1 :=
    clique_prod_eq_one3 cx hCP hG1 hKx hM₂x hM₃x hM₄x (fun h => hM₂K h.symm)
      (fun h => hM₃K h.symm) (fun h => hM₄K h.symm) m23 m24 m34 (c.commutes_K_of_ne hM₂ hM₂K)
      (c.commutes_K_of_ne hM₃ hM₃K) (c.commutes_K_of_ne hM₄ hM₄K) q23 q24 q34 hRK hB₂ hB₃ hB₄
      hKR hM₂B hM₃B hM₄B c.hz hx₂ hx₃ hx₄
  have e3 : xM * x₂ * x₃ * x₄ = z * x₂ * x₃ * x₄ := e1.trans e2.symm
  exact hG1 hM.1 c.hK hMK hxM c.hz
    (mul_right_cancel (mul_right_cancel (mul_right_cancel e3)))

end CFSG.ClassicalInvolution.Q3.Q3W.EX

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic


theorem shapePiece3_of_glueFacts (h3 : OddThreeFreeInput) {tY : StatedLieTag} {nY : ℕ}
    (hY : YData3 tY nY) (hF : GlueFactsOn (modelFund 3 1 tY nY)) :
    ShapePiece3 1 (CompData.model tY nY) := by
  intro G _ _ _ hnab K z hR hshape
  exfalso
  have hΩ := hR.inClass
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictT hY.sc hΩ hK hR.cls hshape
  let c : ETCtx3 tY nY (conjClass3 K) K z :=
    { hΩ := hΩ, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1, hO3 := h3 G K z hR, d := d,
      hY := hY }
  exact EX.false_of_twin_glue3 c (fun L hL => single_class3 K L hL) hshape hF.nonempty hF.twins
    hF.hub hF.twinWithin hF.orth hF.kernel

theorem shapePiece3_of_cliqueFacts (h3 : OddThreeFreeInput) {tY : StatedLieTag} {nY : ℕ}
    (hY : YData3 tY nY) (hF : CliqueFactsOn (modelFund 3 1 tY nY)) :
    ShapePiece3 1 (CompData.model tY nY) := by
  intro G _ _ _ hnab K z hR hshape
  exfalso
  have hΩ := hR.inClass
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictT hY.sc hΩ hK hR.cls hshape
  let c : ETCtx3 tY nY (conjClass3 K) K z :=
    { hΩ := hΩ, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1, hO3 := h3 G K z hR, d := d,
      hY := hY }
  exact EX.false_of_clique_glue3 c (fun L hL => single_class3 K L hL) hshape hF.nonempty hF.clique
    hF.prod

end CFSG.ClassicalInvolution.Q3.Q3W

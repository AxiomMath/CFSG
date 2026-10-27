module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)
open scoped MatrixGroups commutatorElement


section Gen

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {a : ℕ}

theorem eq_top_of_outerGen_le3 (S : D4Ctx3 G K z a) {N M : Subgroup G}
    (hN : N ∈ conjClass3 K) (hM : M ∈ outerSet (conjClass3 K) N) {H : Subgroup G}
    (hNH : outerGen (conjClass3 K) N ≤ H) (hMH : outerGen (conjClass3 K) M ≤ H) : H = ⊤ := by
  set Ω := conjClass3 K with hΩdef
  let 𝔖 : Set (Subgroup G) := {J | J ∈ Ω ∧ outerGen Ω J ≤ H ∧
    ∃ E ∈ outerSet Ω J, outerGen Ω E ≤ H}
  have hsub : 𝔖 ⊆ Ω := fun J hJ => hJ.1
  have hne : 𝔖.Nonempty := ⟨N, hN, hNH, M, hM, hMH⟩
  have hcl : ∀ J ∈ 𝔖, ∀ L ∈ Ω, L ≠ J → Commutes J L → L ∈ 𝔖 := by
    rintro J ⟨hJ, hJH, E, hE, hEH⟩ L hL - hc
    by_cases htw : cnbhd Ω L = cnbhd Ω J
    · refine ⟨hL, ?_, E, ?_, hEH⟩
      · rw [outerGen_eq_of_cnbhd_eq htw]
        exact hJH
      · rw [outerSet_eq_of_cnbhd_eq htw]
        exact hE
    · have hLout : L ∈ outerSet Ω J := ⟨⟨hL, Or.inr hc.symm⟩, htw⟩
      obtain ⟨y, hy, hyE⟩ := exists_conj_of_shape3 S hJ hE hLout
      have hyH : y ∈ H := hJH hy
      refine ⟨hL, ?_, J, mem_outerSet_symm hJ hLout, hJH⟩
      rw [← hyE, outerGen_conj S.setup.inClass.conjInvariant]
      have := conjSub_mono (n := y) hEH
      rwa [conjSub_eq_self_of_mem hyH] at this
  have hall : Ω ⊆ 𝔖 := subset_of_adj_closed ((CoreAssembly.deltaConnected_iff K).mp S.setup.conn)
    hsub hne hcl
  rw [eq_top_iff, ← S.setup.inClass.generated]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨-, -, E, hE, hEH⟩ := hall hL
  exact (le_outerGen (mem_outerSet_symm hL hE)).trans hEH


section Lift

variable {Ω : Set (Subgroup G)} {ι : Type}

theorem ker_k3_of_powCop3 {c : CompData} (hpc : PowCop3 c) {X : Type} [Group X] (φ : c.G →* X)
    (hker : φ.ker ≤ Subgroup.center c.G) : ∀ x ∈ φ.ker, x ^ 3 = 1 → x = 1 := by
  intro x hx h3
  by_contra hne
  have hord : orderOf x = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3)).resolve_left
      fun h => hne (orderOf_eq_one_iff.mp h)
  exact hpc.cop x (hker hx) (by rw [hord])

theorem gen3_of_kind {c : CompData} (hk : c = CompData.model .POmegaPlus 4) :
    ∀ R ∈ c.fund, ModelFacts.Gen3 R :=
  transport_plus_four (fun _ _ S => ∀ R ∈ S, ModelFacts.Gen3 R) D4Facts3.of_gf3.central.gen hk

theorem mul_self_of_isClassicalMember3 {L : Subgroup G} {z₀ : G} (h : IsClassicalMember3 L z₀) :
    z₀ * z₀ = 1 := by
  have h3 : z₀ ^ 2 = 1 := by
    rw [← h.orderOf_eq_two]
    exact pow_orderOf_eq_one _
  simpa [pow_two] using h3

theorem exists_central_preimage3 {w : G} {D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)}
    {i : ι} (hgen : ∀ R ∈ (D.kind i).fund, ModelFacts.Gen3 R)
    (hk3 : ∀ x ∈ (D.hom i).ker, x ^ 3 = 1 → x = 1) {T : Subgroup G} {R : Subgroup (D.kind i).G}
    (hR : Corr3 Ω w D i T R) {a : G} (ha : IsClassicalMember3 T a) (haY : a ∈ locLayer Ω w) :
    ∃ c ∈ R, (∀ r ∈ R, c * r = r * c) ∧ D.hom i c = locMk Ω w ⟨a, haY⟩ ∧ c ≠ 1 := by
  have hmem : locMk Ω w ⟨a, haY⟩ ∈ locImg Ω w T :=
    ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha.mem, rfl⟩
  rw [hR.2.2] at hmem
  obtain ⟨c, hcR, hc⟩ := hmem
  have hcent : ∀ r ∈ R, r * c = c * r :=
    ModelFacts.commute_of_map_commute_of_gen3 (D.hom i) (D.ker_le_center i) hk3
      (hgen R hR.2.1) (b := c) (by
        intro r hr
        have hx : D.hom i r ∈ locImg Ω w T := hR.2.2 ▸ ⟨r, hr, rfl⟩
        obtain ⟨t, ht, hrt⟩ := hx
        rw [hc, ← hrt]
        show locMk Ω w t * locMk Ω w ⟨a, haY⟩ = locMk Ω w ⟨a, haY⟩ * locMk Ω w t
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (isSubnormal_le ha.subnormal (Subgroup.mem_subgroupOf.mp ht)))
  refine ⟨c, hcR, fun r hr => (hcent r hr).symm, hc, ?_⟩
  rintro rfl
  exact locMk_ne_one_of_involution3 ha haY (by rw [← hc, map_one])

theorem commutes_elem_of_commutes_locImg3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) {e : G} (heY : e ∈ locLayer Ω x)
    (h : ∀ a ∈ locImg Ω x L, a * locMk Ω x ⟨e, heY⟩ = locMk Ω x ⟨e, heY⟩ * a) :
    ∀ y ∈ L, y * e = e * y := by
  obtain ⟨z₀, hz⟩ := hΩ.classical L hL.1
  have hLY := le_centralizingLayer hL
  obtain ⟨e'⟩ := hz.nonempty_equiv_sl2 (hex L hL.1)
  obtain ⟨e₁⟩ : Nonempty (↥(L.subgroupOf (locLayer Ω x)) ≃* SL(2, ZMod 3)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hLY).trans e'⟩
  intro y hy
  have hyY : y ∈ locLayer Ω x := hLY hy
  have := commutes_of_commutes_oddQuotient3 hP1 hO3 (K := L.subgroupOf (locLayer Ω x))
    (fun u hu => congrArg Subtype.val (pow_twelve_of_equiv_sl2Three e₁ ⟨u, hu⟩))
    (y := ⟨e, heY⟩) (fun u hu => by
      rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥(locLayer Ω x))]
      change QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))
        ⁅(u : ↥(locLayer Ω x)), (⟨e, heY⟩ : ↥(locLayer Ω x))⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact h _ ⟨u, hu, rfl⟩) (x := ⟨y, hyY⟩) (Subgroup.mem_subgroupOf.mpr hy)
  have h2 := commutatorElement_eq_one_iff_mul_comm.mp this
  exact congrArg Subtype.val h2

theorem mul_commutes_of_mem_comp3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {w : G}
    (hP1 : LocalOddCentral Ω {w}) (hO3 : LocalOddThreeFree3 Ω w)
    (D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)) {i₁ : ι}
    (hk : D.kind i₁ = CompData.model .POmegaPlus 4) {T T' L : Subgroup G}
    (hT : T ∈ compMembers3 Ω w D i₁) (hT' : T' ∈ compMembers3 Ω w D i₁) (hc : Commutes T T')
    (hL : L ∈ compMembers3 Ω w D i₁) {a b : G} (ha : IsClassicalMember3 T a)
    (hb : IsClassicalMember3 T' b) : ∀ y ∈ L, a * b * y = y * (a * b) := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hpc := powCop3_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm
    (by decide) (by decide)
  have hgen := gen3_of_kind hk
  have hk3 := ker_k3_of_powCop3 hpc (D.hom i₁) (D.ker_le_center i₁)
  obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hT
  obtain ⟨R', hR'⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hT'
  have haY : a ∈ locLayer Ω w := le_centralizingLayer hT.1 ha.mem
  have hbY : b ∈ locLayer Ω w := le_centralizingLayer hT'.1 hb.mem
  obtain ⟨c, hcR, hcz, hca, hc1⟩ := exists_central_preimage3 hgen hk3 hR ha haY
  obtain ⟨c', hcR', hcz', hcb, hc1'⟩ := exists_central_preimage3 hgen hk3 hR' hb hbY
  have hRR' : Commutes R R' := (corr_commutes3 hΩ hex hP1 hO3 hpc hR hR').mp hc
  have hcen : c * c' ∈ Subgroup.center (D.kind i₁).G :=
    fund_pair_mul_central_of_kind hk hR.2.1 hR'.2.1 hRR' hcR hcR' hcz hcz' hc1 hc1'
  have habY : a * b ∈ locLayer Ω w := (locLayer Ω w).mul_mem haY hbY
  have himg : locMk Ω w ⟨a * b, habY⟩ = D.hom i₁ (c * c') := by
    rw [map_mul, hca, hcb]
    exact map_mul (locMk Ω w) ⟨a, haY⟩ ⟨b, hbY⟩
  intro y hy
  have := commutes_elem_of_commutes_locImg3 hΩ hex hP1 hO3 hL.1 habY (by
    intro x hx
    obtain ⟨k, hk'⟩ := hL.2 hx
    rw [himg, ← hk', ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen k]) y hy
  exact this.symm

end Lift

theorem isClassicalMember_of_twin3 [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : D4Ctx3 G K z a) {N T : Subgroup G} (hN : N ∈ conjClass3 K) (hT : T ∈ conjClass3 K)
    (htw : cnbhd (conjClass3 K) T = cnbhd (conjClass3 K) N) {w : G}
    (hw : IsClassicalMember3 N w) : IsClassicalMember3 T w := by
  set Ω := conjClass3 K with hΩdef
  have hΩ : InClass3 Ω := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  by_cases hTN : T = N
  · rw [hTN]
    exact hw
  obtain ⟨w', hw'⟩ := hΩ.classical T hT
  have hcTN : Commutes T N := by
    have : T ∈ cnbhd Ω N := htw ▸ self_mem_cnbhd hT
    exact this.2.resolve_left hTN
  obtain ⟨M, hM⟩ := outerSet_nonempty_of_shape3 S hN
  have hMΩ : M ∈ Ω := hM.1.1
  have hNM : N ∈ outerSet Ω M := mem_outerSet_symm hN hM
  have hTM : T ∈ outerSet Ω M := by
    have hMT : M ∈ cnbhd Ω T := htw ▸ hM.1
    exact ⟨mem_cnbhd_symm hT hMT, fun e => hM.2 (e.symm.trans htw)⟩
  obtain ⟨wM, hwM, hP1M, hO3M, ι, hι, D, i₁, -, hk, hrest⟩ := exists_D4At3 S hMΩ
  have hout := outerSet_eq_compMembers3 hΩ hex hwM hMΩ hP1M hO3M (single_class_of_mem3 hMΩ) D hk
    hrest
  have hcM : ∀ L ∈ outerSet Ω M, ∀ y ∈ L, w * w' * y = y * (w * w') := by
    intro L hL
    exact mul_commutes_of_mem_comp3 hΩ hex hP1M hO3M D hk (hout ▸ hNM) (hout ▸ hTM) hcTN.symm
      (hout ▸ hL) hw hw'
  have hcN : ∀ L ∈ outerSet Ω N, ∀ y ∈ L, w * w' * y = y * (w * w') := by
    intro L hL y hy
    have hLN : Commutes L N := hL.1.2.resolve_left fun e => hL.2 (e ▸ rfl)
    have hLT : Commutes L T := by
      have : L ∈ cnbhd Ω T := htw ▸ hL.1
      exact this.2.resolve_left fun e => hL.2 (e ▸ htw)
    have h1 : y * w = w * y := hLN y hy w hw.mem
    have h2 : y * w' = w' * y := hLT y hy w' hw'.mem
    calc w * w' * y = w * (w' * y) := by group
      _ = w * (y * w') := by rw [h2]
      _ = (w * y) * w' := by group
      _ = (y * w) * w' := by rw [h1]
      _ = y * (w * w') := by group
  have hle : ∀ N' : Subgroup G, (∀ L ∈ outerSet Ω N', ∀ y ∈ L, w * w' * y = y * (w * w')) →
      outerGen Ω N' ≤ Subgroup.centralizer ({w * w'} : Set G) := fun N' h =>
    iSup₂_le fun L hL y hy => Subgroup.mem_centralizer_singleton_iff.mpr (h L hL y hy).symm
  have htop := eq_top_of_outerGen_le3 S hN hM (hle N hcN) (hle M hcM)
  have hcentral : w * w' ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({w * w'} : Set G) := by
      rw [htop]
      trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rw [center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hcentral
  have hsq : w * w = 1 := mul_self_of_isClassicalMember3 hw
  have : w' = w := mul_left_cancel (hcentral.trans hsq.symm)
  rw [← this]
  exact hw'

end Gen

end CFSG.ClassicalInvolution.Q3.Q3W.EX

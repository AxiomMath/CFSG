module

public import CFSG.ClassicalInvolution.Q3.Q3E6TWeak
public import CFSG.ClassicalInvolution.Q3.Q3TWRowB

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Exceptional CFSG.LieType.CurtisTits
  CFSG.Blueprint.Chevalley CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TW
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

set_option linter.unusedSectionVars false

variable {G : Type} [Group G]


theorem exists_psi_of_chainTE6_3 (hC : TD4Collapse) {U : Fin 4 → Subgroup G}
    (hU : IsTE6Chain 3 1 le_rfl U) :
    ∃ Ψ : twistedE6Group 3 1 →* G, Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ i, U i ∧
      ∀ i : Fin 4, (nodeTE6 3 1 i).map Ψ = U i := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, -, -, -, hblk⟩ := weakCT3_twistedE6 hC
    (U := fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_self U)
    (fun i j hij x hx y hy => Subtype.ext (hU.comm i j hij x.1 hx y.1 hy))
    (by
      obtain ⟨W, hW⟩ := hU.pair01
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup' hW).trans (sup_le (hUle 0) (hUle 1))) hW⟩)
    (by
      obtain ⟨W, hW⟩ := hU.pair23
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup' hW).trans (sup_le (hUle 2) (hUle 3))) hW⟩)
    (by
      obtain ⟨W, hW, hWle⟩ := hU.pair12
      exact ⟨W.subgroupOf Gs, TwistedB2Model.StandardPair.subgroupOf
        (hWle.trans (sup_le (sup_le (hUle 1) (hUle 2)) (hUle 3))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, ?_⟩
  · intro x hx
    have : Ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro i
    calc (nodeTE6 3 1 i).map (Gs.subtype.comp Ψ')
        = ((nodeTE6 3 1 i).map Ψ').map Gs.subtype := (Subgroup.map_map _ _ _).symm
      _ = ((U i).subgroupOf Gs).map Gs.subtype := congrArg (Subgroup.map Gs.subtype) (hblk i)
      _ = U i := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle i)]

section Recognition

variable [Finite G] [IsSimpleGroup G]

theorem routeD3_twistedE6_of_chain (hnab : ∃ x y : G, x * y ≠ y * x) (hC : TD4Collapse)
    {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K z) {U : Fin 4 → Subgroup G}
    (hU : IsTE6Chain 3 1 le_rfl U) (hU0 : U 0 ∈ Ω)
    (hcover : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K →
      ∃ h ∈ U 1 ⊔ U 2 ⊔ U 3, L = conjSub h (U 1)) :
    CFSG.Blueprint.OddLieType G := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : StatedLieAdmissible .twistedE6 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  obtain ⟨Ψ, hker, hrange, hnode⟩ := exists_psi_of_chainTE6_3 hC hU
  have hscT : FundamentalSingleClass .twistedE6 (twistedE6Datum 3 1) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .twistedE6 0 3 1 Nat.prime_three
      trivial hadm (by decide) (by decide)
  have hΩψ : ∀ R ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum 3 1), R.map Ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT _ (nodeTE6_mem_fund (p := 3) (f := 1) (i := 0) (by decide)) R hR
    rw [hg, ← conjSub_map, hnode 0]
    exact hΩ.conjInvariant _ _ hU0
  set N₀ : Subgroup G := (rankOneHiTE6 (frobQ 3 1)).map Ψ with hN₀
  have hN₀Ω : N₀ ∈ Ω := hΩψ _ (rankOneHiTE6_mem_fund _)
  obtain ⟨g₀, hg₀⟩ := hsingle N₀ hN₀Ω
  have hxN : g₀ * z * g₀⁻¹ ∈ N₀ := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  set x : G := g₀ * z * g₀⁻¹ with hx
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hN₀x : N₀ ∈ centralizingMembers Ω {x} := by
    rw [hx, centralizingMembers_conj hΩ.conjInvariant g₀ z]
    exact ⟨K, hKz, hg₀.symm⟩
  have hcommU : ∀ j : Fin 4, j.val ≠ 0 → Commutes N₀ (U j) := by
    intro j hj
    have := commutes_map Ψ (commutes_rankOneHiTE6_node (p := 3) (f := 1) hj)
    rwa [hnode j] at this
  have hcommY : Commutes N₀ (U 1 ⊔ U 2 ⊔ U 3) :=
    (commutes_sup_of_both_TE6 (commutes_sup_of_both_TE6 (hcommU 1 (by decide)).symm
      (hcommU 2 (by decide)).symm) (hcommU 3 (by decide)).symm).symm
  have hLcomm : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K → Commutes N₀ L := by
    intro L hL hLK
    obtain ⟨h, hh, rfl⟩ := hcover L hL hLK
    intro n hn l hl
    obtain ⟨u, hu, rfl⟩ := hl
    have hnh : Commute n h := (hcommY n hn h hh : n * h = h * n)
    have hnu : Commute n u := (hcommU 1 (by decide) n hn u hu : n * u = u * n)
    exact ((hnh.mul_right hnu).mul_right hnh.inv_right).eq
  set 𝓡 : Set (Subgroup G) := centralizingMembers Ω {z} \ {K} with h𝓡
  have h𝓡sub : 𝓡 ⊆ centralizingMembers Ω {x} := by
    rintro L ⟨hL, hLK⟩
    exact mem_centralizingMembers_of_commutes hL.1 hxN (hLcomm L hL hLK).symm
  have hN₀R : N₀ ∉ 𝓡 := by
    rintro ⟨hL, hLK⟩
    obtain ⟨zN, hzN⟩ := hΩ.classical N₀ hN₀Ω
    exact not_commutes_self3 hzN (hLcomm N₀ hL hLK)
  have hcard : (centralizingMembers Ω {x}).ncard ≤ 1 + 𝓡.ncard := by
    rw [hx, ncard_centralizingMembers_conj hΩ.conjInvariant]
    have : 𝓡.ncard + 1 = (centralizingMembers Ω {z}).ncard :=
      Set.ncard_sdiff_singleton_add_one hKz (Set.toFinite (centralizingMembers Ω {z}))
    omega
  have hEq : centralizingMembers Ω {x} = insert N₀ 𝓡 :=
    centralizingMembers_eq_insert hN₀x h𝓡sub hN₀R hcard
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum 3 1),
    L = R.map Ψ} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩψ R hR
  have hne : 𝔖.Nonempty := ⟨N₀, _, rankOneHiTE6_mem_fund _, rfl⟩
  have hY : U 1 ⊔ U 2 ⊔ U 3 = (nodeTE6 3 1 1 ⊔ nodeTE6 3 1 2 ⊔ nodeTE6 3 1 3).map Ψ := by
    rw [Subgroup.map_sup, Subgroup.map_sup, hnode 1, hnode 2, hnode 3]
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro N ⟨R, hR, rfl⟩ L hL hLN hcomm
    obtain ⟨h, hh⟩ := hscT _ (rankOneHiTE6_mem_fund (frobQ 3 1)) R hR
    have hNeq : R.map Ψ = conjSub (Ψ h) N₀ := by
      rw [hh, hN₀, conjSub_map]
    set L' := conjSub (Ψ h)⁻¹ L with hL'
    have hL'Ω : L' ∈ Ω := hΩ.conjInvariant _ L hL
    have hLL' : L = conjSub (Ψ h) L' := (conjSub_conjSub_inv _ L).symm
    have hL'N : L' ≠ N₀ := fun e => hLN (by rw [hNeq, hLL', e])
    have hcomm' : Commutes N₀ L' := by
      rw [hNeq, hLL'] at hcomm
      exact (commutes_conjSub_iff _).mp hcomm
    have hL'x : L' ∈ centralizingMembers Ω {x} :=
      mem_centralizingMembers_of_commutes hL'Ω hxN hcomm'.symm
    rw [hEq] at hL'x
    rcases hL'x with h1 | h1
    · exact absurd h1 hL'N
    · obtain ⟨y, hy, hL'y⟩ := hcover L' h1.1 h1.2
      rw [hY] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      refine ⟨conjSub h (conjSub y' (nodeTE6 3 1 1)),
        conjSub_mem_fundamentalSubgroups (conjSub_mem_fundamentalSubgroups
          (nodeTE6_mem_fund (p := 3) (f := 1) (i := 1) (by decide)) y') h, ?_⟩
      rw [hLL', hL'y, ← conjSub_map, ← conjSub_map, hnode 1]
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hsub hne hcl
  have hsurj : Function.Surjective Ψ := by
    refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
    calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
      _ ≤ Ψ.range := iSup₂_le fun L hL => by
        obtain ⟨R, -, rfl⟩ := hΩsub hL
        exact Subgroup.map_le_range Ψ R
  have hmodel : CFSG.Blueprint.LieModel
      (twistedE6Group 3 1 ⧸ Subgroup.center (twistedE6Group 3 1)) .twistedE6 0 3 1 :=
    (curtisTitsConclusion_twistedE6.{0} 3 1 hadm).1.2.2
  exact oddLieType_of_model3 hnab hadm (lieModel_of_surjective_simple3 hnab Ψ hsurj hker hmodel)

end Recognition

end CFSG.ClassicalInvolution.Q3.Q3E6T

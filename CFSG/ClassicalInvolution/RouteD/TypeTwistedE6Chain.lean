module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6Model
public import CFSG.ClassicalInvolution.RouteD.LocalTwin
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.CurtisTits CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

structure IsTE6Chain (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) {G : Type} [Group G]
    (U : Fin 4 → Subgroup G) : Prop where
  comm : ∀ i j : Fin 4, i.val + 1 < j.val → Commutes (U i) (U j)
  pair01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (U 0) (U 1)
  pair23 : ∃ W, LinearBlockStandardPair (GaloisField p (2 * f)) W (U 2) (U 3)
  pair12 : ∃ W, UnitaryB2BlockStandardPair (frobQ p f) (frobQ_frobQ p f hf) W (U 1) (U 2) ∧
    W ≤ U 1 ⊔ U 2 ⊔ U 3

theorem exists_psi_of_chainTE6 (hadm : StatedLieAdmissible .twistedE6 0 p f) (hq : 4 ≤ p ^ f)
    {U : Fin 4 → Subgroup G} (hU : IsTE6Chain p f hadm.2.1 U) :
    ∃ Ψ : twistedE6Group p f →* G, Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ i, U i ∧
      ∀ i : Fin 4, (nodeTE6 p f i).map Ψ = U i := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  have hf : 1 ≤ f := hadm.2.1
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  obtain ⟨Ψ', hsurj, hker, -, -, -, hblk⟩ := CFSG.ClassicalInvolution.WeakCT.weakCT_twistedE6 hadm
    hF (by rw [hF]; exact hq) (U := fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_self U)
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
    calc (nodeTE6 p f i).map (Gs.subtype.comp Ψ')
        = ((nodeTE6 p f i).map Ψ').map Gs.subtype := (Subgroup.map_map _ _ _).symm
      _ = ((U i).subgroupOf Gs).map Gs.subtype := congrArg (Subgroup.map Gs.subtype) (hblk i)
      _ = U i := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle i)]

section Recognition

variable [Finite G]

theorem routeD_twistedE6_of_chain (hadm : StatedLieAdmissible .twistedE6 0 p f) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) {U : Fin 4 → Subgroup G}
    (hU : IsTE6Chain p f hadm.2.1 U) (hU0 : U 0 ∈ Ω)
    (hcover : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K →
      ∃ h ∈ U 1 ⊔ U 2 ⊔ U 3, L = conjSub h (U 1)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 := by
  classical
  obtain ⟨Ψ, hker, hrange, hnode⟩ := exists_psi_of_chainTE6 hadm (by omega) hU
  have hscT : FundamentalSingleClass .twistedE6 (twistedE6Datum p f) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .twistedE6 0 p f Fact.out trivial
      hadm (by decide) (by decide)
  have hΩψ : ∀ R ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f), R.map Ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT _ (nodeTE6_mem_fund (p := p) (f := f) (i := 0) (by decide)) R hR
    rw [hg, ← conjSub_map, hnode 0]
    exact hΩ.conjInvariant _ _ hU0
  set N₀ : Subgroup G := (rankOneHiTE6 (frobQ p f)).map Ψ with hN₀
  have hN₀Ω : N₀ ∈ Ω := hΩψ _ (rankOneHiTE6_mem_fund _)
  obtain ⟨g₀, hg₀⟩ := hsingle N₀ hN₀Ω
  have hxN : g₀ * z * g₀⁻¹ ∈ N₀ := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  set x : G := g₀ * z * g₀⁻¹ with hx
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hN₀x : N₀ ∈ centralizingMembers Ω {x} := by
    rw [hx, centralizingMembers_conj hΩ.conjInvariant g₀ z]
    exact ⟨K, hKz, hg₀.symm⟩
  have hcommU : ∀ j : Fin 4, j.val ≠ 0 → Commutes N₀ (U j) := by
    intro j hj
    have := commutes_map Ψ (commutes_rankOneHiTE6_node (p := p) (f := f) hj)
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
    exact not_commutes_self_of_mem hΩ hN₀Ω (hLcomm N₀ hL hLK)
  have hcard : (centralizingMembers Ω {x}).ncard ≤ 1 + 𝓡.ncard := by
    rw [hx, ncard_centralizingMembers_conj hΩ.conjInvariant]
    have : 𝓡.ncard + 1 = (centralizingMembers Ω {z}).ncard :=
      Set.ncard_sdiff_singleton_add_one hKz (Set.toFinite (centralizingMembers Ω {z}))
    omega
  have hEq : centralizingMembers Ω {x} = insert N₀ 𝓡 :=
    centralizingMembers_eq_insert hN₀x h𝓡sub hN₀R hcard
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f),
    L = R.map Ψ} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩψ R hR
  have hne : 𝔖.Nonempty := ⟨N₀, _, rankOneHiTE6_mem_fund _, rfl⟩
  have hY : U 1 ⊔ U 2 ⊔ U 3 = (nodeTE6 p f 1 ⊔ nodeTE6 p f 2 ⊔ nodeTE6 p f 3).map Ψ := by
    rw [Subgroup.map_sup, Subgroup.map_sup, hnode 1, hnode 2, hnode 3]
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro N ⟨R, hR, rfl⟩ L hL hLN hcomm
    obtain ⟨h, hh⟩ := hscT _ (rankOneHiTE6_mem_fund (frobQ p f)) R hR
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
      refine ⟨conjSub h (conjSub y' (nodeTE6 p f 1)),
        conjSub_mem_fundamentalSubgroups (conjSub_mem_fundamentalSubgroups
          (nodeTE6_mem_fund (p := p) (f := f) (i := 1) (by decide)) y') h, ?_⟩
      rw [hLL', hL'y, ← conjSub_map, ← conjSub_map, hnode 1]
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hsub hne hcl
  refine exists_lieSystemData_of_fundamental (t := .twistedE6) (n := 0) trivial hadm Ψ ?_ hker
    ⟨_, rankOneHiTE6_mem_fund (frobQ p f)⟩ (fun L => ⟨fun hL => hΩsub hL, fun hL => hsub hL⟩)
  refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
  calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
    _ ≤ Ψ.range := iSup₂_le fun L hL => by
      obtain ⟨R, -, rfl⟩ := hΩsub hL
      exact Subgroup.map_le_range Ψ R

end Recognition

end CFSG.ClassicalInvolution.RouteD

module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDModel
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDWeak
public import CFSG.ClassicalInvolution.RouteD.LocalTwin
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (linearBlockStandardPair_subgroupOf
  linearBlockStandardPair_le_sup iSup_subgroupOf_eq_top)
open scoped MatrixGroups

section TwistedPair

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {X : Type} [Group X]

@[expose] def SpinMinus6Generated : Prop :=
  haveI := fact_shortField hirr
  (spinMinusModel hirr).lb.range ⊔ (spinMinusModel hirr).sb.range = ⊤

theorem twistedB2BlockPair_le_sup (hg : SpinMinus6Generated hirr) {W U V : Subgroup X}
    (h : TwistedB2BlockPair hirr W U V) : W ≤ U ⊔ V := by
  have := fact_shortField hirr
  obtain ⟨θ, hrange, -, -, hU, hV⟩ := h
  rw [← hrange, MonoidHom.range_eq_map, ← (show (spinMinusModel hirr).lb.range ⊔
    (spinMinusModel hirr).sb.range = ⊤ from hg), Subgroup.map_sup, hU, hV]

theorem twistedB2BlockPair_subgroupOf {W U V J : Subgroup X} (hW : W ≤ J)
    (h : TwistedB2BlockPair hirr W U V) :
    TwistedB2BlockPair hirr (W.subgroupOf J) (U.subgroupOf J) (V.subgroupOf J) := by
  have := fact_shortField hirr
  obtain ⟨θ, hrange, hker, hinjL, hU, hV⟩ := h
  have hJ : ∀ g, θ g ∈ J := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  have himg : ∀ (S : Subgroup _) (Y : Subgroup X), S.map θ = Y →
      S.map (θ.codRestrict J hJ) = Y.subgroupOf J := by
    intro S Y hSY
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hSY ▸ ⟨g, hg, rfl⟩)
    · intro hx
      obtain ⟨g, hg, hgx⟩ := (hSY ▸ Subgroup.mem_subgroupOf.mp hx : (x : X) ∈ S.map θ)
      exact ⟨g, hg, Subtype.ext hgx⟩
  refine ⟨θ.codRestrict J hJ, ?_, ?_, ?_, himg _ _ hU, himg _ _ hV⟩
  · rw [← hrange]
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.codRestrict_apply, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, h⟩
      exact ⟨a, Subtype.ext h⟩
  · intro x hx
    apply hker
    simpa [MonoidHom.mem_ker, Subtype.ext_iff] using hx
  · intro x y hxy
    apply hinjL
    have := congrArg Subtype.val hxy
    simpa using this

end TwistedPair

section Chain

variable {p f : ℕ} {G : Type} [Group G]

theorem weakCT_spinMinus_subgroup {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p f)
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F)
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hg6 : SpinMinus6Generated hirr)
    (U : Fin (n - 1) → Subgroup G)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hpair : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (htw : ∀ i j : Fin (n - 1), i.val + 3 = n → j.val + 2 = n →
      ∃ W, TwistedB2BlockPair hirr W (U i) (U j)) :
    ∃ Ψ : spinGroup (quadMinus n F b c) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (CurtisTits.rankOne (minusDatum n hirr).rootGroup k).map Ψ = U k := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, -, -, -, hblk⟩ :=
    CFSG.ClassicalInvolution.WeakCT.weakCT_spinMinus_of_pair hadm hp2 hF hq hirr (X := ↥Gs)
    (fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_eq_top U)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun i j hij hj => by
      obtain ⟨W, hW⟩ := hpair i j hij hj
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
    (fun i j hi hj => by
      obtain ⟨W, hW⟩ := htw i j hi hj
      exact ⟨W.subgroupOf Gs, twistedB2BlockPair_subgroupOf hirr
        ((twistedB2BlockPair_le_sup hirr hg6 hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, ?_⟩
  · intro x hx
    have : Ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro k
    rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]

end Chain

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem routeD_typeTwistedD_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 6 ≤ n) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaMinus (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin (n - 1) → Subgroup G)
    (hU0 : U (twIdx0 (by omega : 3 ≤ n)) ∈ Ω)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hpair : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (htw : ∀ i j : Fin (n - 1), i.val + 3 = n → j.val + 2 = n →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaMinus ∧ D.rank i = n := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .POmegaMinus n p f := ⟨Fact.out, by omega, by show 4 ≤ n; omega⟩
  have hadmY : StatedLieAdmissible .POmegaMinus (n - 2) p f :=
    ⟨Fact.out, by omega, by show 4 ≤ n - 2; omega⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hF]; omega
  set F := GaloisField p f with hFdef
  obtain ⟨Ψ, hker, hrange, hblk⟩ := weakCT_spinMinus_subgroup hadm hp2 hF h4
    (minusCoeffs_irr p f) hg6 U hcomm hpair htw
  let U' : Fin (n - 2 - 1) → Subgroup G := fun k => U ⟨k.val + 2, by omega⟩
  have hcomm' : ∀ i j : Fin (n - 2 - 1), i.val + 1 < j.val → ∀ u ∈ U' i, ∀ v ∈ U' j,
      u * v = v * u := fun i j hij u hu v hv => hcomm _ _ (by simp only; omega) u hu v hv
  have hpair' : ∀ i j : Fin (n - 2 - 1), i.val + 1 = j.val → j.val + 2 < n - 2 →
      ∃ W, LinearBlockStandardPair F W (U' i) (U' j) := fun i j hij hj =>
    hpair _ _ (by simp only; omega) (by simp only; omega)
  have htw' : ∀ i j : Fin (n - 2 - 1), i.val + 3 = n - 2 → j.val + 2 = n - 2 →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (U' i) (U' j) := fun i j hi hj =>
    htw _ _ (by simp only; omega) (by simp only; omega)
  obtain ⟨ψD, hkerD, hrangeD, hblkD⟩ := weakCT_spinMinus_subgroup hadmY hp2 hF h4
    (minusCoeffs_irr p f) hg6 U' hcomm' hpair' htw'
  have hirr := minusCoeffs_irr p f
  set 𝔖 : Set (Subgroup G) :=
    {L | ∃ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), L = R.map Ψ} with h𝔖
  have hsingleN : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr),
      ∀ R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), ∃ g, R' = conjSub g R :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus n p f Fact.out trivial
      hadm (by decide) (by decide)
  have hsingleY : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum (n - 2) hirr),
      ∀ R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum (n - 2) hirr), ∃ g, R' = conjSub g R :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus (n - 2) p f Fact.out
      trivial hadmY (by decide) (by decide)
  have hk0 : (twIdx0 hn3).val + 1 < n - 1 := by simp only [twIdx0]; omega
  have hr0 :
      (CurtisTits.rankOne (minusDatum n hirr).rootGroup (twIdx0 hn3)).map Ψ = U (twIdx0 hn3) :=
    hblk _
  have hr0mem := rankOne_mem_fund_minus hirr hk0
  have hΩ𝔖 : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    obtain ⟨g, hg⟩ := hsingleN _ hr0mem R hR
    rw [hg, map_conjSub_eq, hr0]
    exact hΩ.conjInvariant _ _ hU0
  set N₀ : Subgroup G := U (twIdx0 hn3) with hN₀
  have hN₀𝔖 : N₀ ∈ 𝔖 := ⟨_, hr0mem, hr0.symm⟩
  set T : Subgroup G := (rankOneHiMinus hirr hn3).map Ψ with hT
  have hT𝔖 : T ∈ 𝔖 := ⟨_, rankOneHiMinus_mem_fund hirr hn3, rfl⟩
  have hTU : ∀ j : Fin (n - 1), 2 ≤ j.val → Commutes T (U j) := by
    intro j hj
    rw [← hblk j]
    exact commutes_map_hom Ψ (commutes_rankOneHiMinus hirr hn3 hj)
  have hTN : Commutes T N₀ := by
    rw [← hr0]
    exact commutes_map_hom Ψ (commutes_hiMinus_twin hirr hn3)
  have hN₀U : ∀ j : Fin (n - 1), 2 ≤ j.val → Commutes N₀ (U j) := fun j hj x hx y hy =>
    hcomm (twIdx0 hn3) j (by simp only [twIdx0]; omega) x hx y hy
  have hDT : Commutes ψD.range T := by
    rw [hrangeD]
    exact commutes_iSup_of_forall fun k => (hTU ⟨k.val + 2, by omega⟩ (by simp only; omega)).symm
  have hDN : Commutes ψD.range N₀ := by
    rw [hrangeD]
    exact commutes_iSup_of_forall fun k =>
      (hN₀U ⟨k.val + 2, by omega⟩ (by simp only; omega)).symm
  have hDrange : ψD.range ≤ Ψ.range := by
    rw [hrangeD, hrange]
    exact iSup_le fun k => le_iSup U _
  have hfinY : Finite (spinGroup (quadMinus (n - 2) F (minusCoeffs p f).1 (minusCoeffs p f).2)) :=
    finite_spinGroup_quadMinus _ _ _
  set Y : Set (Subgroup (spinGroup (quadMinus (n - 2) F (minusCoeffs p f).1
      (minusCoeffs p f).2))) := fundamentalSubgroups .POmegaMinus (minusDatum (n - 2) hirr)
    with hY
  set 𝓡 : Set (Subgroup G) := insert T ((fun R => R.map ψD) '' Y) with h𝓡
  have hr0Y := rankOne_mem_fund_minus hirr (n := n - 2) (k := (⟨0, by omega⟩ : Fin (n - 2 - 1)))
    (by simp only; omega)
  have hk2 : (⟨2, by omega⟩ : Fin (n - 1)).val + 1 < n - 1 := by simp only; omega
  have hψDr0 : (CurtisTits.rankOne (minusDatum (n - 2) hirr).rootGroup
      (⟨0, by omega⟩ : Fin (n - 2 - 1))).map ψD = U ⟨2, by omega⟩ := hblkD _
  have hr2 : (CurtisTits.rankOne (minusDatum n hirr).rootGroup (⟨2, by omega⟩ : Fin (n - 1))).map
      Ψ = U ⟨2, by omega⟩ := hblk _
  have hψD𝔖 : ∀ R ∈ Y, R.map ψD ∈ 𝔖 := by
    intro R hR
    obtain ⟨g, hg⟩ := hsingleY _ hr0Y R hR
    obtain ⟨h, hh⟩ : ψD g ∈ Ψ.range := hDrange ⟨g, rfl⟩
    refine ⟨conjSub h (CurtisTits.rankOne (minusDatum n hirr).rootGroup
      (⟨2, by omega⟩ : Fin (n - 1))), conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fund_minus hirr hk2) h, ?_⟩
    rw [hg, map_conjSub_eq, hψDr0, map_conjSub_eq, hr2, hh]
  have h𝓡𝔖 : 𝓡 ⊆ 𝔖 := by
    rintro _ (rfl | ⟨R, hR, rfl⟩)
    · exact hT𝔖
    · exact hψD𝔖 R hR
  have hcommR : ∀ R ∈ 𝓡, Commutes R N₀ := by
    rintro _ (rfl | ⟨R, hR, rfl⟩)
    · exact hTN
    · exact fun x hx y hy => hDN x (Subgroup.map_le_range ψD R hx) y hy
  have hTnot : T ∉ (fun R => R.map ψD) '' Y := by
    rintro ⟨R', hR', hRT⟩
    have hTle : T ≤ ψD.range := hRT ▸ Subgroup.map_le_range ψD R'
    exact not_commutes_self_of_mem hΩ (hΩ𝔖 hT𝔖) fun x hx y hy => hDT x (hTle hx) y hy
  have hperfY : ∀ R ∈ Y, R ≤ ⁅R, R⁆ := by
    intro R hR
    obtain ⟨g, hg⟩ := hsingleY _ hr0Y R hR
    rw [hg]
    exact conjSub_perfect (rankOne_minusDatum_perfect hirr h4 (by simp only; omega)) g
  have hinj : Set.InjOn (fun R => R.map ψD) Y := fun R hR R' hR' h =>
    eq_of_map_eq_of_perfect_ker_central ψD hkerD (hperfY R hR) (hperfY R' hR') h
  have hcard : (centralizingMembers Ω {z}).ncard ≤ 1 + 𝓡.ncard := by
    have h1 : (locFamily Ω z).ncard ≤ 2 + Y.ncard :=
      hshape.ncard_locFamily_le (by decide) hfinY
    rw [ncard_centralizingMembers_eq hΩ hP1, h𝓡, Set.ncard_insert_of_notMem hTnot (Set.toFinite _),
      hinj.ncard_image]
    omega
  have hH : ∀ N ∈ 𝔖, ∃ g ∈ Ψ.range, N = conjSub g N₀ := by
    rintro _ ⟨R, hR, rfl⟩
    obtain ⟨g, hg⟩ := hsingleN _ hr0mem R hR
    exact ⟨Ψ g, ⟨g, rfl⟩, by rw [hg, map_conjSub_eq, hr0]⟩
  have hinv : ∀ g ∈ Ψ.range, ∀ M ∈ 𝔖, conjSub g M ∈ 𝔖 := by
    rintro _ ⟨h, rfl⟩ _ ⟨R, hR, rfl⟩
    exact ⟨conjSub h R, conjSub_mem_fundamentalSubgroups hR h, by rw [map_conjSub_eq]⟩
  have hcl := adj_closed_of_base_members hΩ hK hsingle hz hΩ𝔖 hN₀𝔖 h𝓡𝔖 hcommR hcard hH hinv
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hΩ𝔖 ⟨N₀, hN₀𝔖⟩ hcl
  have hsurj : Function.Surjective Ψ := by
    refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
    calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
      _ ≤ Ψ.range := iSup₂_le fun L hL => by
        obtain ⟨R, -, rfl⟩ := hΩsub hL
        exact Subgroup.map_le_range Ψ R
  exact exists_lieSystemData_of_fundamental (t := .POmegaMinus) trivial hadm Ψ hsurj hker
    ⟨_, hr0mem⟩ (fun L => ⟨fun hL => hΩsub hL, fun hL => hΩ𝔖 hL⟩)

end Main

end CFSG.ClassicalInvolution.RouteD

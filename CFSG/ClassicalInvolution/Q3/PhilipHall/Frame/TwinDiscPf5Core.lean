module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Quot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescentSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Base

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem eq_of_coreAt_eq (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J L : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hL : L ∈ tqMembers3 Ω c)
    (h : TwinADescent.coreAt c J = TwinADescent.coreAt c L) : J = L := by
  obtain ⟨P, hP, hPc⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hJ.2
  have hPJc : IsSylow2In P (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hP, hPc⟩
  have hPL : P ≤ L := (h ▸ hPJc.1).trans (TwinADescent.coreAt_le_left c L)
  have h8 : 8 ≤ Nat.card P :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ.1 hP)
  exact Sec6Gen.eq_of_le_of_le hΩ hJ.1 hL.1 hP.2.1 (by omega) hP.1 hPL

theorem isUniqueInvolution_coreAt_of_tq (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K : Subgroup G} (hK : K ∈ tqMembers3 Ω c) {z : G} (hz : IsUniqueInvolution K z) :
    IsUniqueInvolution (TwinADescent.coreAt c K) z := by
  obtain ⟨P, hP, hPc⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hK.2
  obtain ⟨z', hz', hzm, -, -⟩ :=
    TwinEdge.Fam.member_data hΩ hK.1 hP hPc
  have hzz : z = z' := hz.eq hz'
  subst hzz
  exact isUniqueInvolution_mono hz (TwinADescent.coreAt_le_left c K) hzm

theorem mem_omegaStarNbr_of_coreFamily (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c)
    (hJ : J ∈ tqMembers3 Ω c)
    (h : TwinADescent.coreAt c J ∈
      omegaStarNbr (TwinADescent.coreFamily Ω c) (TwinADescent.coreAt c K)) :
    J ∈ omegaStarNbr Ω K := by
  obtain ⟨-, hne, U, hU, hUJ, hUN⟩ := h
  have hJK : J ≠ K := fun h' => hne (by rw [h'])
  have hUΩ : U ∈ USet Ω := TwinADescent.mem_USet_of_core hc2 hU
  obtain ⟨R₀, -, J', -, -, hUR₀, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hUΩ
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΩ hUΩ
  have hUJG : U ≤ J := hUJ.trans (TwinADescent.coreAt_le_left c J)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK.1
  have hzA := isUniqueInvolution_coreAt_of_tq hΩ hc2 hK hz
  have hUc : U ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * z * u⁻¹ = z := hzA.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hUN hu))
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]
  have hUN' : U ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK.1 hJ.1 hJK.symm hz hUJG hU2 (by omega) hUc
  exact ⟨hJ.1, hJK, U, hUΩ, hUJG, hUN'⟩

theorem dstarAdj_of_coreFamily (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c) (hJ : J ∈ tqMembers3 Ω c)
    (h : dstarAdj (TwinADescent.coreFamily Ω c) (TwinADescent.coreAt c K)
      (TwinADescent.coreAt c J)) : dstarAdj Ω K J := by
  rcases h.2 with h1 | h1
  · exact ⟨hJ.1, Or.inl (mem_omegaStarNbr_of_coreFamily hΩ hc2 hK hJ h1)⟩
  · exact ⟨hJ.1, Or.inr (mem_omegaStarNbr_of_coreFamily hΩ hc2 hJ hK h1)⟩

end Base

section Sec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem oddCoreOf_le_of_normalizes {Y C : Subgroup G} (hYC : Y ≤ C)
    (hCN : ∀ g ∈ C, conjSub g Y = Y) : oddCoreOf Y ≤ oddCoreOf C := by
  have hPC : oddCoreOf Y ≤ C := (oddCoreOf_le_self Y).trans hYC
  have hinv : ∀ g ∈ C, conjSub g (oddCoreOf Y) = oddCoreOf Y := fun g hg => by
    rw [← AscE184Sect.oddCoreOf_conjSub, hCN g hg]
  have hnorm : ((oddCoreOf Y).subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h1 : (g : G) * x * (g : G)⁻¹ ∈ conjSub (g : G) (oddCoreOf Y) := conj_mem_conjSub hx
    rwa [hinv g g.2] at h1
  have hodd : Odd (Nat.card ↥((oddCoreOf Y).subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv]
    have h1 : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥Y
    have h2 : Nat.card ↥(oddCoreOf Y) = Nat.card (classicalInvolutionOddCore ↥Y) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective).symm.toEquiv
    rw [h2]
    exact h1
  have hle : (oddCoreOf Y).subgroupOf C ≤ classicalInvolutionOddCore ↥C := le_sSup ⟨hnorm, hodd⟩
  intro x hx
  exact ⟨⟨x, hPC hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

variable (Ω c) in
@[expose] def cFam : Set (Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :=
  restrictFamily (TwinADescent.coreFamily Ω c) (Subgroup.centralizer ({c} : Set G))

variable (Ω c) in
@[expose] noncomputable def coreHull : Subgroup ↥(Subgroup.centralizer ({c} : Set G)) :=
  ⨆ L ∈ cFam Ω c, L

variable (Ω c) in
@[expose] def hullFam : Set (Subgroup ↥(coreHull Ω c)) :=
  restrictFamily (cFam Ω c) (coreHull Ω c)

variable (Ω c) in
@[expose] def secFam : Set (Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))) :=
  quotFamily (hullFam Ω c) (classicalInvolutionOddCore ↥(coreHull Ω c))

variable (Ω c) in
@[expose] noncomputable def secImg (J : Subgroup G) :
    Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :=
  (((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
    (coreHull Ω c)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)))

theorem le_coreHull {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) :
    (TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ coreHull Ω c :=
  le_iSup₂_of_le _ ⟨TwinADescent.coreAt c J, TwinADescent.coreAt_mem_coreFamily hJ,
    TwinADescent.coreAt_le_centralizer c J, rfl⟩ le_rfl

theorem subgroupOf_mem_hullFam {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) :
    ((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
      (coreHull Ω c) ∈ hullFam Ω c :=
  ⟨_, ⟨TwinADescent.coreAt c J, TwinADescent.coreAt_mem_coreFamily hJ,
    TwinADescent.coreAt_le_centralizer c J, rfl⟩, le_coreHull hJ, rfl⟩

theorem secImg_mem_secFam {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) :
    secImg Ω c J ∈ secFam Ω c :=
  ⟨_, subgroupOf_mem_hullFam hJ, rfl⟩

theorem exists_of_mem_secFam {M : Subgroup (↥(coreHull Ω c) ⧸
      classicalInvolutionOddCore ↥(coreHull Ω c))} (hM : M ∈ secFam Ω c) :
    ∃ J ∈ tqMembers3 Ω c, M = secImg Ω c J := by
  obtain ⟨_, ⟨_, ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩, -, rfl⟩, rfl⟩ := hM
  exact ⟨J, hJ, rfl⟩

theorem conjSub_coreHull (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) : conjSub g (coreHull Ω c) = coreHull Ω c := by
  have hcl := (TwinADescent.hypOmegaGen_coreFamily hΩ hc2).conjInvariant
  have hle : ∀ g : ↥(Subgroup.centralizer ({c} : Set G)),
      conjSub g (coreHull Ω c) ≤ coreHull Ω c := by
    intro g
    unfold coreHull conjSub
    rw [Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    exact le_iSup₂_of_le (conjSub g L) (hcl g L hL) le_rfl
  refine le_antisymm (hle g) ?_
  have := conjSub_mono (n := g) (hle g⁻¹)
  rwa [conjSub_conjSub_inv] at this

end Sec

section Conn

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem oddCore_coreHull_le (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {n : ↥(coreHull Ω c)} (hn : n ∈ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    (((n : ↥(Subgroup.centralizer ({c} : Set G))) : G)) ∈
      oddCoreOf (Subgroup.centralizer ({c} : Set G)) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set Y : Subgroup G := (coreHull Ω c).map C.subtype with hY
  have hYC : Y ≤ C := fun y ⟨x, _, hx⟩ => hx ▸ x.2
  have hCN : ∀ g ∈ C, conjSub g Y = Y := by
    intro g hg
    have := conjSub_map C.subtype (⟨g, hg⟩ : ↥C) (coreHull Ω c)
    rw [conjSub_coreHull hΩ hc2] at this
    exact this
  have hle := oddCoreOf_le_of_normalizes hYC hCN
  have hOY : ((n : ↥C) : G) ∈ oddCoreOf Y := by
    have h1 : n ∈ classicalInvolutionOddCore ↥(coreHull Ω c) := hn
    have hiso : (classicalInvolutionOddCore ↥(coreHull Ω c)).map
        (Subgroup.equivMapOfInjective (coreHull Ω c) C.subtype C.subtype_injective).toMonoidHom =
        classicalInvolutionOddCore ↥Y :=
      CFSG.ComponentClassification.OddCore.equiv_invariant _
    have h2 : (Subgroup.equivMapOfInjective (coreHull Ω c) C.subtype C.subtype_injective) n ∈
        classicalInvolutionOddCore ↥Y := by
      rw [← hiso]
      exact Subgroup.mem_map_of_mem _ h1
    exact ⟨_, h2, rfl⟩
  exact hle hOY

theorem dstarAdj_of_hullFam (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J J' : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hJ' : J' ∈ tqMembers3 Ω c)
    (h : dstarAdj (hullFam Ω c)
      (((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
        (coreHull Ω c))
      (((TwinADescent.coreAt c J').subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
        (coreHull Ω c))) : dstarAdj Ω J J' := by
  have h1 := dstarAdj_map h
  rw [Subgroup.map_subgroupOf_eq_of_le (le_coreHull hJ),
    Subgroup.map_subgroupOf_eq_of_le (le_coreHull hJ')] at h1
  have h2 := dstarAdj_map h1
  rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J),
    Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J')] at h2
  exact dstarAdj_of_coreFamily hΩ hc2 hJ hJ' h2

theorem exists_conj_omegaStarNbr_gen {H : Type} [Group H] [Finite H] {Λ : Set (Subgroup H)}
    {N : Subgroup H} [N.Normal] (hΛ : HypOmegaGen Λ) (hΛ' : HypOmegaGen (quotFamily Λ N))
    (hN : Odd (Nat.card N)) {K J : Subgroup H} (hK : K ∈ Λ) (hJ : J ∈ Λ)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Λ N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaStarNbr Λ (conjSub n K) := by
  exact E187C.exists_conj_omegaStarNbr_of (fun hJ hUb hUbJ => TwinADescent2.exists_lift_USet_gen hΛ' hN hJ hUb hUbJ)
    (fun hU => Sec6Gen.isPGroup_of_mem_USet hΛ hU) (fun hK hU2 hUN => TwinADescent2.exists_conj_normalizer_gen hΛ hN hK hU2 hUN) hK hJ h

theorem exists_good_lift_gen {H : Type} [Group H] {Λ : Set (Subgroup H)} {N : Subgroup H}
    [N.Normal] (good : Subgroup H → Prop) {K : Subgroup H} (hK : K ∈ Λ) (hgK : good K)
    (hstep : ∀ L ∈ Λ, ∀ L' ∈ Λ, good L →
      dstarAdj (quotFamily Λ N) (L.map (QuotientGroup.mk' N)) (L'.map (QuotientGroup.mk' N)) →
      ∃ L'' ∈ Λ, L''.map (QuotientGroup.mk' N) = L'.map (QuotientGroup.mk' N) ∧ good L'')
    {Mb : Subgroup (H ⧸ N)}
    (hMb : Mb ∈ dstarComp (quotFamily Λ N) (K.map (QuotientGroup.mk' N))) :
    ∃ M ∈ Λ, M.map (QuotientGroup.mk' N) = Mb ∧ good M := by
  induction hMb with
  | refl => exact ⟨K, hK, rfl, hgK⟩
  | tail _ hbc ih =>
    obtain ⟨M, hM, hMb, hgood⟩ := ih
    obtain ⟨L', hL', hL'eq⟩ := hbc.1
    have hL'eq' : L'.map (QuotientGroup.mk' N) = _ := hL'eq
    subst hMb hL'eq'
    obtain ⟨M'', hM'', hM''eq, hgood''⟩ := hstep M hM L' hL' hgood hbc
    exact ⟨M'', hM'', hM''eq, hgood''⟩

end Conn

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_conj_tq_of_connected (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {B : Subgroup G} (hB : B ∈ tqMembers3 Ω c)
    (hconn : ∀ M ∈ secFam Ω c, M ∈ dstarComp (secFam Ω c) (secImg Ω c B)) :
    ∀ M ∈ tqMembers3 Ω c, ∃ n ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)),
      ∃ J' ∈ tqMembers3 Ω c, J' ∈ dstarComp Ω B ∧ M = conjSub n J' := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set X := coreHull Ω c with hX
  set Λ : Set (Subgroup ↥X) := hullFam Ω c with hΛdef
  set N₀ : Subgroup ↥X := classicalInvolutionOddCore ↥X with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ : HypOmegaGen Λ :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) X
  have hΛ' : HypOmegaGen (quotFamily Λ N₀) := TwinEdge.hypOmegaGen_quotFamily_odd hΛ hN₀odd
  have hexΛ : ∀ {L : Subgroup ↥X}, L ∈ Λ → ∃ J ∈ tqMembers3 Ω c,
      L = ((TwinADescent.coreAt c J).subgroupOf C).subgroupOf X := by
    rintro L ⟨_, ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩, -, rfl⟩
    exact ⟨J, hJ, rfl⟩
  let good : Subgroup ↥X → Prop := fun L => ∃ J ∈ tqMembers3 Ω c,
    L = ((TwinADescent.coreAt c J).subgroupOf C).subgroupOf X ∧ J ∈ dstarComp Ω B
  have hstepΛ : ∀ {L L' : Subgroup ↥X}, L' ∈ Λ → good L → dstarAdj Λ L L' → good L' := by
    intro L L' hL' hgood hadj
    obtain ⟨J, hJ, rfl, hJB⟩ := hgood
    obtain ⟨J', hJ', rfl⟩ := hexΛ hL'
    exact ⟨J', hJ', rfl, hJB.tail (dstarAdj_of_hullFam hΩ hc2 hJ hJ' hadj)⟩
  have hBΛ := subgroupOf_mem_hullFam hB
  intro M hM
  have hMΛ := subgroupOf_mem_hullFam hM
  obtain ⟨M', hM', hMeq, hMgood⟩ := exists_good_lift_gen (N := N₀) good hBΛ
    ⟨B, hB, rfl, Relation.ReflTransGen.refl⟩
    (fun L hL L' hL' hgL hadj => by
      obtain ⟨-, hadj | hadj⟩ := hadj
      · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaStarNbr_gen hΛ hΛ' hN₀odd hL hL' hadj
        have h1 := omegaStarNbr_conj hΛ.conjInvariant hn' (n⁻¹ : ↥X)
        rw [conjSub_inv_conjSub] at h1
        have hnn : QuotientGroup.mk' N₀ n⁻¹ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (N₀.inv_mem hn)
        refine ⟨conjSub n⁻¹ L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact hstepΛ (hΛ.conjInvariant _ L' hL') hgL ⟨hΛ.conjInvariant _ L' hL', Or.inl h1⟩
      · obtain ⟨n, hn, hn'⟩ := exists_conj_omegaStarNbr_gen hΛ hΛ' hN₀odd hL' hL hadj
        have hnn : QuotientGroup.mk' N₀ n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
        refine ⟨conjSub n L', hΛ.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact hstepΛ (hΛ.conjInvariant _ L' hL') hgL ⟨hΛ.conjInvariant _ L' hL', Or.inr hn'⟩)
    (hconn _ (map_mem_quotFamily hMΛ))
  obtain ⟨n, hn, hMn⟩ := Q3T6.exists_conj_of_map_eq_gen hΛ hN₀odd hM' hMΛ hMeq
  obtain ⟨J, hJ, rfl, hJB⟩ := hMgood
  have hnC : ((n : ↥C) : G) ∈ C := (n : ↥C).2
  refine ⟨((n : ↥C) : G), oddCore_coreHull_le hΩ hc2 hn, J, hJ, hJB, ?_⟩
  have h3 := conjSub_subgroupOf X n ((TwinADescent.coreAt c J).subgroupOf C)
  rw [h3] at hMn
  have hle2 : conjSub (n : ↥C) ((TwinADescent.coreAt c J).subgroupOf C) ≤ X := by
    have := conjSub_mono (n := (n : ↥C)) (le_coreHull hJ)
    rwa [conjSub_eq_self_of_mem n.2] at this
  have h4 : (TwinADescent.coreAt c M).subgroupOf C =
      conjSub (n : ↥C) ((TwinADescent.coreAt c J).subgroupOf C) := by
    have := congrArg (Subgroup.map X.subtype) hMn
    rwa [Subgroup.map_subgroupOf_eq_of_le (le_coreHull hM),
      Subgroup.map_subgroupOf_eq_of_le hle2] at this
  have h5 : conjSub (n : ↥C) ((TwinADescent.coreAt c J).subgroupOf C) =
      (TwinADescent.coreAt c (conjSub ((n : ↥C) : G) J)).subgroupOf C := by
    rw [conjSub_subgroupOf C (n : ↥C) (TwinADescent.coreAt c J),
      TwinADescent.conjSub_coreAt hnC J]
  have h6 : TwinADescent.coreAt c M = TwinADescent.coreAt c (conjSub ((n : ↥C) : G) J) := by
    have := congrArg (Subgroup.map C.subtype) (h4.trans h5)
    rwa [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c M),
      Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c _)] at this
  exact eq_of_coreAt_eq hΩ hc2 hM (conjSub_mem_tqMembers3 hΩ.conjInvariant hnC hJ) h6

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

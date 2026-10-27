module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinD2Leaves2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem natCard_member_of_oddCent {r : ℕ} (hr : 2 ≤ r) (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) (hO : TightOddCent t)
    {J : Subgroup Y} (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) : Nat.card J = 2 ^ r := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class _ J hJ
  rw [natCard_conjSub]
  have hK2 : IsPGroup 2 (tightCore R) :=
    hd.isPGroup_member hO _ (CoreAssembly.mem_conjClass_self _)
  have hKS : tightCore R = (S : Subgroup R).map R.subtype :=
    hd.sylow_core.eq_of_le hK2 le_rfl hd.sylow_core.1
  obtain ⟨e⟩ := hq
  rw [hKS, Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr e.toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  rw [Nat.add_sub_cancel, pow_add]
  ring

theorem uAt_of_e2At_four_le {r : ℕ} (hr : 4 ≤ r) (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) (hO : TightOddCent t)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hE : TC.E2At (tightCore R) J) : TC.UAt (CoreAssembly.conjClass (tightCore R)) t J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hΩ : HypOmegaGen Ω := hd.hypOmegaGen
  have h2 := hd.isPGroup_member hO
  have hJΩ : J ∈ Ω := hJ.1
  have hJ2 : IsPGroup 2 J := h2 J hJΩ
  obtain ⟨⟨u, hu⟩, -⟩ := hΩ.omega1 J hJΩ
  obtain ⟨-, -, -, -, -, T, hTs, -, hTc, -⟩ := hd.edge_involution hJ hu
  have hJT : J = T := hTs.eq_of_le hJ2 le_rfl hTs.1
  have hJC : J ≤ C := hJT ▸ hTc
  obtain ⟨P, ⟨-, hP2, hPn⟩, huP⟩ := hE t u hd.isUniqueInvolution_core hu
  have hcardJ : Nat.card J = 2 ^ r := natCard_member_of_oddCent (by omega) hd hq hO hJΩ
  have hOC : classicalInvolutionOddCore ↥C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : Y) ∈ oddCoreImg C := ⟨x, hx, rfl⟩
    have hO' : oddCoreImg C = ⊥ := hO
    rw [hO', Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx')
  set J' : Subgroup ↥C := J.subgroupOf C with hJ'def
  set Φ : Set (Subgroup ↥C) := CoreAssembly.conjClass J' with hΦdef
  have hconjC : ∀ x : ↥C, conjSub (x : Y) J ≤ C := fun x => by
    have := conjSub_mono (n := (x : Y)) hJC
    rwa [conjSub_eq_self_of_mem x.2] at this
  set Pset : Set (Subgroup Y) := {L | ∃ x : ↥C, conjSub (x : Y) J = L} with hPset
  have hPΩ : Pset ⊆ Ω := by
    rintro _ ⟨x, rfl⟩
    exact hΩ.conjInvariant _ J hJΩ
  have hrestr : restrictFamily Pset C = Φ := by
    ext L'
    constructor
    · rintro ⟨L, ⟨x, rfl⟩, -, rfl⟩
      exact ⟨x, conjSub_subgroupOf C x J⟩
    · rintro ⟨x, rfl⟩
      exact ⟨conjSub (x : Y) J, ⟨x, rfl⟩, hconjC x, conjSub_subgroupOf C x J⟩
  have hsub : Φ ⊆ restrictFamily Ω C := by
    rw [← hrestr]
    rintro _ ⟨L, hL, hLC, rfl⟩
    exact ⟨L, hPΩ hL, hLC, rfl⟩
  have hΦ : HypOmegaGen Φ :=
    PhilipHall.Frame.hypOmegaGen_sub (PhilipHall.Frame.hypOmegaGen_restrict hΩ C) hsub
      (conjInvariant_conjClass J')
  have hJ'2 : IsPGroup 2 J' := hJ2.comap_subtype
  have h2Φ : ∀ L ∈ Φ, IsPGroup 2 L := by
    rintro _ ⟨x, rfl⟩
    exact isPGroup_conjSub x hJ'2
  have hcardJ' : Nat.card J' = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv
  have h8Φ : ∀ L ∈ Φ, Nat.card L = 2 ^ r := by
    rintro _ ⟨x, rfl⟩
    rw [natCard_conjSub, hcardJ', hcardJ]
  have hAJ' : AEmpty Φ J' := by
    have h := PhilipHall.Frame.aEmpty_restrictFamily hΩ h2 hPΩ hJC (hd.aEmpty J hJΩ)
    rwa [hrestr] at h
  have hAΦ : ∀ L ∈ Φ, AEmpty Φ L :=
    aEmpty_forall_of_transitive (conjInvariant_conjClass J') (fun L hL => hL) hAJ'
  have hu' : IsUniqueInvolution J' ⟨u, hJC hu.mem⟩ := isUniqueInvolution_subgroupOf hu hJC
  have hQn : (P.subgroupOf C).Normal := ⟨fun p hp c => by
    rw [Subgroup.mem_subgroupOf] at hp ⊢
    exact hPn c c.2 p hp⟩
  have hQ2 : IsPGroup 2 (P.subgroupOf C) := hP2.comap_subtype
  have hinO2 : ∀ L ∈ Φ, ∀ w : ↥C, IsUniqueInvolution L w →
      ∃ Q : Subgroup ↥C, Q.Normal ∧ IsPGroup 2 Q ∧ w ∈ Q := by
    rintro _ ⟨x, rfl⟩ w hw
    refine ⟨P.subgroupOf C, hQn, hQ2, ?_⟩
    rw [← (hu'.conj x).eq hw]
    exact hQn.conj_mem _ (Subgroup.mem_subgroupOf.mpr huP) x
  have hle : (⨆ U ∈ USet Φ, U : Subgroup ↥C) ≤ pCore 2 ↥C :=
    iSup_uSet_le_pCore hΦ fun U hU U' hU' =>
      le_normalizer_of_four_le hr hΦ h2Φ h8Φ hAΦ hOC hinO2 hU hU'
  have hJ'Φ : J' ∈ Φ := CoreAssembly.mem_conjClass_self J'
  have hJ'syl : IsSylow2In J' J' := ⟨le_rfl, hJ'2, fun Q hQL _ hLQ => le_antisymm hQL hLQ⟩
  obtain ⟨U', hU'J', hU'c, hU'card⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΦ (TC.mem_RSet_of_isPGroup hJ'Φ hJ'2)).exists_cyclic_index_two
  have hU'Φ : U' ∈ USet Φ := mem_USet_of_natCard hJ'Φ hJ'syl hU'J' hU'c hU'card
  have hU'le : U' ≤ pCore 2 ↥C :=
    (le_iSup₂ (f := fun U (_ : U ∈ USet Φ) => U) U' hU'Φ).trans hle
  have hJsyl : IsSylow2In J J := ⟨le_rfl, hJ2, fun Q hQL _ hLQ => le_antisymm hQL hLQ⟩
  have hUJ : U'.map C.subtype ≤ J := by
    have h1 := Subgroup.map_mono (f := C.subtype) hU'J'
    rwa [Subgroup.map_subgroupOf_eq_of_le hJC] at h1
  have hUc : IsCyclic ↥(U'.map C.subtype) :=
    isCyclic_of_surjective (U'.equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
      (U'.equivMapOfInjective C.subtype C.subtype_injective).surjective
  have hUcard : Nat.card J = 2 * Nat.card ↥(U'.map C.subtype) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, ← hcardJ', hU'card]
  refine ⟨U'.map C.subtype, mem_USet_of_natCard hJΩ hJsyl hUJ hUc hUcard, hUJ,
    (pCore 2 ↥C).map C.subtype, ⟨Subgroup.map_subtype_le _, pCore_isPGroup.map _, ?_⟩,
    Subgroup.map_mono hU'le⟩
  rintro c hc _ ⟨p, hp, rfl⟩
  exact ⟨⟨c, hc⟩ * p * ⟨c, hc⟩⁻¹, (pCore_normal (p := 2) (G := ↥C)).conj_mem p hp ⟨c, hc⟩, rfl⟩

theorem not_thinAt_of_four_le {r : ℕ} (hr : 4 ≤ r) (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) (hO : TightOddCent t)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ¬ TC.ThinAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) J := fun ⟨hE, hnot⟩ =>
  hnot t hd.isUniqueInvolution_core (uAt_of_e2At_four_le hr hd hq hO hJ hE)

theorem clsR_quot {r : ℕ} (hd : TightDatum R S t) (hgen : TightSelfGen R)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    TightClsR r (Y ⧸ classicalInvolutionOddCore Y)
      (R.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
      (TwistQ.sylowMap (classicalInvolutionOddCore Y) S)
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) t) := by
  have hNodd : Odd (Nat.card ↥(classicalInvolutionOddCore Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card Y
  obtain ⟨e⟩ := hq
  refine ⟨⟨(OddQ.sylowEquiv hd hNodd).symm.trans e⟩, ?_,
    CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot⟩
  have hgen' : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hgen
  show (⨆ g : Y ⧸ classicalInvolutionOddCore Y,
      conjSub g (tightCore (R.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))))) = ⊤
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective (classicalInvolutionOddCore Y)), ← hgen', Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [TwistQ.conjSub_map]
  refine le_trans ?_ (le_iSup (fun g : Y ⧸ classicalInvolutionOddCore Y =>
    conjSub g (tightCore (R.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))))
    (QuotientGroup.mk' (classicalInvolutionOddCore Y) g))
  refine conjSub_mono ?_
  unfold tightCore
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxR, hx2⟩, rfl⟩
  refine ⟨⟨x, hxR, rfl⟩, ?_⟩
  rw [← MonoidHom.map_zpowers]
  exact hx2.map _

theorem exists_clsR_subnormalClosure {r : ℕ} (hd : TightDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∃ (ht : t ∈ subnormalClosure (tightCore R))
      (S' : Sylow 2 ↥(R.subgroupOf (subnormalClosure (tightCore R)))),
      TightDatum (R.subgroupOf (subnormalClosure (tightCore R))) S' ⟨t, ht⟩ ∧
      TightSelfGen (R.subgroupOf (subnormalClosure (tightCore R))) ∧
      TightClsR r (↥(subnormalClosure (tightCore R)) ⧸
          classicalInvolutionOddCore ↥(subnormalClosure (tightCore R)))
        ((R.subgroupOf (subnormalClosure (tightCore R))).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(subnormalClosure (tightCore R)))))
        (TwistQ.sylowMap (classicalInvolutionOddCore ↥(subnormalClosure (tightCore R))) S')
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(subnormalClosure (tightCore R)))
          ⟨t, ht⟩) := by
  set H : Subgroup Y := subnormalClosure (tightCore R) with hH
  have hKH : tightCore R ≤ H := le_subnormalClosure _
  have hSH : (S : Subgroup R).map R.subtype ≤ H := hd.sylow_core.1.trans hKH
  obtain ⟨S', hd', ⟨eS⟩⟩ := hd.restrict hSH
  have hgen : TightSelfGen (R.subgroupOf H) := by
    unfold TightSelfGen
    rw [tightCore_subgroupOf hKH]
    exact iSup_conjSub_eq_top_of_subnormalClosure (subnormalClosure_subgroupOf_subnormalClosure _)
  obtain ⟨e⟩ := hq
  exact ⟨hSH hd.mem, S', hd', hgen, clsR_quot hd' hgen ⟨eS.trans e⟩⟩

theorem exists_secDatumR (hd : TightDatum R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) :
    ∃ Sq : Sylow 2 ↥(secR R u), TightDatum (secR R u) Sq
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) ∧
      Nonempty ((Sq : Subgroup ↥(secR R u)) ≃* (S : Subgroup R)) := by
  obtain ⟨-, hu2, hut, -, huK, -⟩ := hd.edge_involution hJ hu
  have hcomm : ∀ r ∈ R, ⁅u, r⁆ ∈ oddCoreImg R := (hd.act_eq_one_iff hut).mp huK
  have huN : u ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hut
  have huC : u ∈ centralizerModOdd ⊤ R :=
    ⟨Subgroup.mem_top u, huN, mem_normalizer_oddCore_of_mem_normalizer huN, hcomm⟩
  obtain ⟨S', hS'⟩ := hd.exists_sylow_le_centralizer
    (Balance.isPGroup_zpowers_of_mul_self_eq_one hu2) (Subgroup.zpowers_le.mpr huC)
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({u} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers u)))
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := (hd.ofSylow S').restrict hS'u
  have hSH : (S₁ : Subgroup ↥(R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))).map
      (R.subgroupOf (Subgroup.centralizer ({u} : Set Y))).subtype ≤ secH R u :=
    hd₁.sylow_core.1.trans (le_subnormalClosure _)
  obtain ⟨S₂, hd₂, ⟨e₂⟩⟩ := hd₁.restrict hSH
  have hNodd := CFSG.ComponentClassification.OddCore.odd_card ↥(secH R u)
  exact ⟨_, OddQ.datum hd₂ hNodd,
    ⟨(OddQ.sylowEquiv hd₂ hNodd).symm.trans (e₂.trans (e₁.trans (Sylow.equiv S' S)))⟩⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4

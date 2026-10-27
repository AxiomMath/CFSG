module

public import CFSG.ClassicalInvolution.Q3.Q3T7K01
public import CFSG.ClassicalInvolution.Q3.Q3T7FUE3
public import CFSG.ClassicalInvolution.Q3.Q3T7FUL

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AEmpty :=
  @CFSG.ClassicalInvolution.Asc77.AEmpty

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G]

theorem HypOmega.toU (h : HypOmega Ω) : CFSG.ClassicalInvolution.T7FU.Asc77.HypOmega (.sl2 3 1) Ω :=
  { h with toGen := h.toGen }
omit [Finite G] in

theorem isClassicalMember_of_twin (hΩ : Q3T7M.HM Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) : Generic.IsClassicalMember M t :=
  CFSG.ClassicalInvolution.T7FU.Asc77.isClassicalMember_of_twin (⟨hΩ, hΩ.toGen⟩) hM hMt

theorem exists_twHom (hΩ : Q3T7M.HM Ω) {M : Subgroup G} {t : G} (hM : M ∈ Ω)
    (hMt : IsUniqueInvolution M t) :
    ∃ ψ : ↥M →* ↥(twImage t M), Function.Surjective ψ ∧
      ψ.ker = classicalInvolutionOddCore ↥M ∧
      ∀ x : ↥M, ((ψ x : ↥(twImage t M)) : TwQ t) =
        twMk t ⟨(x : G), le_TwC_of_isUniqueInvolution hMt x.2⟩ :=
  CFSG.ClassicalInvolution.T7FU.Asc77.exists_twHom (⟨hΩ, hΩ.toGen⟩) hM hMt

theorem nonempty_equiv_sl2_twImage (hΩ : Q3T7M.HM Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) :
    Nonempty (↥(twImage t M) ≃* SL(2, GaloisField 3 1)) := by
  obtain ⟨ψ, hψs, hψker, -⟩ := exists_twHom hΩ hM hMt
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hM
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hψker)).trans e⟩
omit [Finite G] in

theorem isSubnormal_twImage (hΩ : Q3T7M.HM Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) : IsSubnormal (twImage t M) ⊤ :=
  CFSG.ClassicalInvolution.T7FU.Asc77.isSubnormal_twImage (⟨hΩ, hΩ.toGen⟩) hM hMt

theorem mem_oddCore_of_coe_mem_oddCoreOf (hΩ : Q3T7M.HM Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) {x : ↥(TwC t)} (hx : (x : G) ∈ oddCoreOf M) :
    x ∈ classicalInvolutionOddCore ↥(TwC t) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.mem_oddCore_of_coe_mem_oddCoreOf (⟨hΩ, hΩ.toGen⟩) hM hMt hx

theorem commutes_twImage (hΩ : Q3T7M.HM Ω) {M J : Subgroup G} {t : G} (hM : M ∈ Ω)
    (hJ : J ∈ Ω) (hMJ : M ≠ J) (hMt : IsUniqueInvolution M t) (hJt : IsUniqueInvolution J t) :
    Commutes (twImage t M) (twImage t J) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.commutes_twImage (⟨hΩ, hΩ.toGen⟩) hM hJ hMJ hMt hJt
omit [Finite G] in

theorem conjInvariant_twFamily (hΩ : Q3T7M.HM Ω) (t : G) : ConjInvariant (twFamily Ω t) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.conjInvariant_twFamily
    (CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU hΩ) t

theorem HypOmega.of_commuting {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)} (hconj :
    ConjInvariant Λ)
    (hcl : ∀ L ∈ Λ, ∃ z : Y, Generic.IsClassicalMember L z) (hex : ExactMembers Λ)
    (hcomm : ∀ K ∈ Λ, ∀ J ∈ Λ, K ≠ J → Commutes K J) : HypOmega Λ where
  conjInvariant := hconj
  classical := hcl
  exact := hex
  omega4 K hK J hJ hKJ := by
    have hc := hcomm K hK J hJ hKJ
    refine ⟨?_, fun _ => hc⟩
    obtain ⟨z, hz⟩ := hcl K hK
    obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex K hK)
    have h2 : Nat.card (Subgroup.center ↥K) = 2 :=
      natCard_center_of_equiv_sl2 (CFSG.ClassicalInvolution.Uniform.odd_natCard_galoisField_of_pos
        (p := 3) (f := 1) (by norm_num) (by norm_num)) e
    have hle : (K ⊓ J).subgroupOf K ≤ Subgroup.center ↥K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2 x hx.2)
    have hdvd : Nat.card ((K ⊓ J).subgroupOf K) ∣ 2 := h2 ▸ Subgroup.card_dvd_of_le hle
    have hcard : Nat.card ↥(K ⊓ J) = Nat.card ((K ⊓ J).subgroupOf K) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ J ≤ K)).toEquiv).symm
    rw [hcard]
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h <;> rw [h] <;> simp
  omega5 K hK J hJ hKJ _ _ v hvJ _ _ _ :=
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hvJ (hcomm K hK J hJ hKJ).symm)

theorem twFamily_hypOmega (hΩ : Q3T7M.HM Ω) (t : G) :
    HypOmega (twFamily Ω t) := by
  have hodd := CFSG.ClassicalInvolution.Uniform.odd_natCard_galoisField_of_pos (p := 3) (f := 1)
    (by norm_num) (by norm_num)
  have h3 : 3 ≤ Nat.card (GaloisField 3 1) := by
    rw [CFSG.ClassicalInvolution.Uniform.natCard_galoisField_eq (p := 3) (f := 1) (by norm_num)]
    norm_num
  have hexM : ∀ {M : Subgroup G}, M ∈ Ω → IsUniqueInvolution M t →
      classicalInvolutionOddCore ↥(twImage t M) = ⊥ := by
    intro M hM hMt
    obtain ⟨e⟩ := nonempty_equiv_sl2_twImage hΩ hM hMt
    exact normal_odd_of_equiv_sl2 hodd h3 e _ inferInstance
      (CFSG.ComponentClassification.OddCore.odd_card _)
  have hex : ExactMembers (twFamily Ω t) := by
    rintro L ⟨M, hM, hMt, rfl⟩
    exact hexM hM hMt
  refine HypOmega.of_commuting (conjInvariant_twFamily hΩ t) ?_ hex ?_
  · rintro L ⟨M, hM, hMt, rfl⟩
    obtain ⟨e⟩ := nonempty_equiv_sl2_twImage hΩ hM hMt
    refine ⟨twT t, ?_⟩
    exact
      { admissible := ⟨Nat.prime_three, by norm_num, by norm_num⟩
        orderOf_eq_two := orderOf_eq_prime (by rw [pow_two]; exact twT_sq t hMt.sq)
          (twT_ne_one hMt.sq hMt.ne_one)
        mem := ⟨⟨t, t_mem_TwC t⟩, Subgroup.mem_subgroupOf.mpr hMt.mem, rfl⟩
        perfect := fun hns => absurd
          (CFSG.ClassicalInvolution.Uniform.MemberType.isSolvableType_sl2.mpr (by norm_num)) hns
        subnormal := by
          rw [centralizer_twT]
          exact isSubnormal_twImage hΩ hM hMt
        witness := ⟨⟨Nat.prime_three⟩, ⟨((QuotientGroup.quotientMulEquivOfEq (hexM hM hMt)).trans
          QuotientGroup.quotientBot).trans e⟩⟩ }
  · rintro _ ⟨M, hM, hMt, rfl⟩ _ ⟨J, hJ, hJt, rfl⟩ hne
    exact commutes_twImage hΩ hM hJ (fun h => hne (by rw [h])) hMt hJt
end Finite
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

@[expose] def E186QuotOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      ∀ (N : Subgroup G) [N.Normal], Odd (Nat.card N) → N ≤ H → N = ⊥

@[expose] def E186QuotCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      ∀ (N : Subgroup G) [N.Normal], N ≤ Subgroup.center G → IsPGroup 2 N → N ≤ H →
        (∀ J ∈ Ω, J ⊓ N = ⊥) → N = ⊥
end Asc77

end

section

namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {N : Subgroup G} [N.Normal]
variable (p f Ω N) in

structure CentQuot : Prop where
  hyp : Q3T7M.HM Ω
  hyp' : Q3T7M.HM (quotFamily Ω N)
  central : N ≤ Subgroup.center G
  two : IsPGroup 2 ↥N
  meet : ∀ J ∈ Ω, J ⊓ N = ⊥

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AscE186.CentQuot.toU {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]
    (c : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AscE186.CentQuot Ω N) :
    CFSG.ClassicalInvolution.T7FU.Asc77.AscE186.CentQuot (.sl2 3 1) Ω N :=
  { c with hyp := CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU c.hyp, hyp' := CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU c.hyp' }

theorem CentQuot.of_isPGroup (hΩ : Q3T7M.HM Ω)
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) :
    CentQuot Ω N :=
  { hyp := hΩ
    hyp' := Q3T7M.CentQ.quotient_hyp hΩ N hNc (fun K hK => by
      rw [inf_comm, hmeet K hK]
      simp)
    central := hNc
    two := hN2
    meet := hmeet }

namespace CentQuot
open CFSG.ClassicalInvolution.Asc77.AscE186.CentQuot
variable (c : Asc77.AscE186.CentQuot Ω N)
include c
omit [Finite G] in

theorem natCard_map {J : Subgroup G} (hJ : J ∈ Ω) :
    Nat.card ↥(J.map (QuotientGroup.mk' N)) = Nat.card J :=
  (Nat.card_congr (AscQuot.quotRestrictEquiv (c.meet J hJ)).toEquiv).symm

theorem isSylow2In_map {J V : Subgroup G} (hJ : J ∈ Ω) (hV : IsSylow2In V J) :
    IsSylow2In (V.map (QuotientGroup.mk' N)) (J.map (QuotientGroup.mk' N)) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.AscE186.CentQuot.isSylow2In_map c.toU hJ hV
omit [Finite G] in

theorem le_of_map_eq [Finite G] {A B : Subgroup G} (hA : A ∈ Ω) (hB : B ∈ Ω)
    (h : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) : A ≤ B :=
  T7FU.Asc77.AscE186.CentQuot.le_of_map_eq c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hA hB h
omit [Finite G] in

theorem eq_of_map_eq [Finite G] {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N)) : K = J :=
  T7FU.Asc77.AscE186.CentQuot.eq_of_map_eq c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hK hJ h
omit [Finite G] in

theorem map_ne_of_ne [Finite G] {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K) :
    J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
  T7FU.Asc77.AscE186.CentQuot.map_ne_of_ne c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hK hJ hne

theorem mem_normalizer_of_map {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    u ∈ Subgroup.normalizer (K : Set G) :=
  T7FU.Asc77.AscE186.CentQuot.mem_normalizer_of_map c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hK
    hu

theorem exists_lift_RSet {J : Subgroup G} (hJ : J ∈ Ω) {Rb : Subgroup (G ⧸ N)}
    (hRb : Rb ∈ RSet (quotFamily Ω N)) (hRbJ : Rb ≤ J.map (QuotientGroup.mk' N)) :
    ∃ R ∈ RSet Ω, R ≤ J ∧ R.map (QuotientGroup.mk' N) = Rb :=
  T7FU.Asc77.AscE186.CentQuot.exists_lift_RSet c.toU hJ hRb hRbJ

theorem exists_lift_USet {J : Subgroup G} (hJ : J ∈ Ω) {Ub : Subgroup (G ⧸ N)}
    (hUb : Ub ∈ USet (quotFamily Ω N)) (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub :=
  CFSG.ClassicalInvolution.T7FU.Asc77.AscE186.CentQuot.exists_lift_USet c.toU hJ hUb hUbJ

theorem omegaStarNbr_of_map {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    J ∈ omegaStarNbr Ω K :=
  T7FU.Asc77.AscE186.CentQuot.omegaStarNbr_of_map c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hK hJ
    h

theorem omegaNbr_of_map {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    J ∈ omegaNbr Ω K :=
  T7FU.Asc77.AscE186.CentQuot.omegaNbr_of_map c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hK hJ h

theorem omegaNbr_map {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) :=
  T7FU.Asc77.AscE186.CentQuot.omegaNbr_map c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hK hJ

theorem dstarAdj_of_map {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω)
    (h : dstarAdj (quotFamily Ω N) (L.map (QuotientGroup.mk' N))
      (L'.map (QuotientGroup.mk' N))) : dstarAdj Ω L L' :=
  T7FU.Asc77.AscE186.CentQuot.dstarAdj_of_map c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hL hL' h

theorem exists_lift_dstarComp {K : Subgroup G} (hK : K ∈ Ω) {Mb : Subgroup (G ⧸ N)}
    (hMb : Mb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ M ∈ dstarComp Ω K, M.map (QuotientGroup.mk' N) = Mb :=
  T7FU.Asc77.AscE186.CentQuot.exists_lift_dstarComp c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hK
    hMb

theorem aEmpty_quotFamily (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M :=
  T7FU.Asc77.AscE186.CentQuot.aEmpty_quotFamily c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hA
end CentQuot
end Asc77.AscE186

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G]

theorem exists_W_of_hypOmega {Ω : Set (Subgroup G)}
    (hΩ : Q3T7M.HM Ω) (S : Sylow 2 G) :
    ∃ W ∈ WSet Ω, W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W :=
  CFSG.ClassicalInvolution.T7FU.Asc77.exists_W_of_hypOmega (⟨hΩ, hΩ.toGen⟩) S

theorem E186Cent2.quot_odd {Ω : Set (Subgroup G)} (hΩ : Q3T7M.HM Ω) {N : Subgroup G} [N.Normal]
    (hΩ' : Q3T7M.HM (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {K H : Subgroup G} (hK : K ∈ Ω) (h : E186Cent2 Ω K H) :
    E186Cent2 (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N)) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.E186Cent2.quot_odd (⟨hΩ, hΩ.toGen⟩) (⟨hΩ', hΩ'.toGen⟩) hN hK h
variable {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.odd_quot_trans (c : MinCex Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hΩ' : Q3T7M.HM (quotFamily Ω N)) (hN : Odd (Nat.card N)) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.odd_quot_trans c.toU (⟨hΩ', hΩ'.toGen⟩) hN

theorem MinCex.odd_quot_stand (c : MinCex Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hΩ' : Q3T7M.HM (quotFamily Ω N)) (hN : Odd (Nat.card N)) :
    ∃ (Sb : Sylow 2 (G ⧸ N)) (Rb Wb : Subgroup (G ⧸ N)),
      EStand (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) Sb Rb Wb := by
  have hΩ : Q3T7M.HM Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have h3 : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3 (l6_7_proved) G Ω K S R W H c
  have hAΩ : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant h3 c.stand.aEmpty
  set Sb : Sylow 2 (G ⧸ N) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S with hSbdef
  have hSb : (Sb : Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S
  obtain ⟨Wb, hWb, hWbS, hWbn⟩ := exists_W_of_hypOmega hΩ' Sb
  have hRsyl : IsSylow2In R K := hΩ.isSylow2In_of_mem_RSet_of_le hK hRR hRK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'tw
  have hR'syl : IsSylow2In R' K' := hΩ.isSylow2In_of_mem_RSet_of_le hK'Ω hR' hR'K'
  refine ⟨Sb, R.map (QuotientGroup.mk' N), Wb, ?_⟩
  exact
    { hyp := hΩ'
      below := Generic.CITBelowU.mono (natCard_quotient_le N) c.stand.below
      ih := ih8T_mono (natCard_quotient_le N) c.stand.ih
      ob := c.stand.ob
      mem := map_mem_quotFamily hK
      aEmpty := aEmpty_quotFamily hΩ hΩ' hN hAΩ _ (map_mem_quotFamily hK)
      twin := ⟨K'.map (QuotientGroup.mk' N),
        ⟨map_mem_quotFamily hK'Ω, QuotientGroup.mk' N z,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hzK,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K') hzK'⟩,
        map_ne_of_twin hΩ hN hK ⟨hK'Ω, z, hzK, hzK'⟩ hK'ne,
        R'.map (QuotientGroup.mk' N),
        mem_RSet_of_isSylow2In (map_mem_quotFamily hK'Ω) (isSylow2In_map_mk hN hR'syl),
        Subgroup.map_mono hR'K', hSb ▸ Subgroup.map_mono hR'S⟩
      hR := ⟨mem_RSet_of_isSylow2In (map_mem_quotFamily hK) (isSylow2In_map_mk hN hRsyl),
        Subgroup.map_mono hRK, hSb ▸ Subgroup.map_mono hRS⟩
      hW := ⟨hWb, hWbS, hWbn⟩ }
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem twin_conj (hΩ : Q3T7M.HM Ω) {M : Subgroup G} {t δ : G} (hM : M ∈ Ω)
    (hMt : IsUniqueInvolution M t) (hδ : δ * t = t * δ) :
    conjSub δ M ∈ Ω ∧ IsUniqueInvolution (conjSub δ M) t :=
  CFSG.ClassicalInvolution.T7FU.Asc77.twin_conj (CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU hΩ) hM
    hMt hδ
section EndNone
variable [Finite G]

theorem endgame_none (hΩ : HypOmega Ω) {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (m₁ : conjSub d₁ K₁ ≠ K₁) (m₂ : conjSub d₂ K₁ ≠ K₁)
    (m₃ : conjSub (d₁ * d₂) K₁ ≠ K₁) : False :=
  CFSG.ClassicalInvolution.T7FU.Asc77.endgame_none (hΩ := hΩ.toU)
    (hodd := (fun _ hJ => hΩ.toMod.oddGen hJ)) (hbad := hbad) (hK₁ := hK₁) (ht := ht) (g₁ := g₁)
    (g₂ := g₂) (g₃ := g₃) (hc := hc) (m₁ := m₁) (m₂ := m₂) (m₃ := m₃)
end EndNone
section EndOne
variable [Finite G]
omit [Finite G] in

theorem conj_mul_commE (δ y x : G) : y * commE δ x * y⁻¹ = commE δ (y * x) * (commE δ y)⁻¹ := by
  unfold commE
  group

@[expose] def commSub (K : Subgroup G) (δ : G) : Subgroup G :=
  Subgroup.closure (Set.range fun x : ↥K => commE δ (x : G))
omit [Finite G] in

theorem commSub_le (K : Subgroup G) {δ : G} (hδ : conjSub δ K = K) : commSub K δ ≤ K := by
  refine (Subgroup.closure_le K).mpr ?_
  rintro _ ⟨x, rfl⟩
  have h1 : δ * (x : G) * δ⁻¹ ∈ K := by
    have := conj_mem_conjSub (n := δ) x.2
    rwa [hδ] at this
  exact K.mul_mem x.2 (K.inv_mem h1)
omit [Finite G] in

theorem commSub_normal (K : Subgroup G) (δ : G) :
    ∀ y ∈ K, ∀ w ∈ commSub K δ, y * w * y⁻¹ ∈ commSub K δ := by
  intro y hy w hw
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    rw [conj_mul_commE]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨y * x, K.mul_mem hy x.2⟩, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨y, hy⟩, rfl⟩))
  | one => simp
  | mul a b _ _ ha hb =>
    have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem endgame_one (hΩ : HypOmega Ω) {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {δ₀ δ₁ : G}
    (g₀ : GoodInv H t δ₀) (g₁ : GoodInv H t δ₁) (g₂ : GoodInv H t (δ₀ * δ₁))
    (hc : δ₀ * δ₁ = δ₁ * δ₀) (n₀ : conjSub δ₀ K₁ = K₁) (m₁ : conjSub δ₁ K₁ ≠ K₁) : False := by
  exact E187C.endgame_one_of hΩ.toMod.conjInvariant
    (fun hM h => Q3T7M.le_of_sq_mem_of_oddGen (hΩ.toMod.oddGen hM) h)
    (fun hM => hΩ.toMod.exists_orderOf_four_of_mem hM)
    (fun hK hJ hKJ hzK hzJ => hΩ.commutes_of_twin hK hJ hKJ hzK hzJ)
    (fun hK ht hw hwc => by
      rcases (hΩ.center_eq hK ht).2 _ hw hwc with h | h
      · rw [h, one_mul]
      · rw [h]
        exact ht.sq)
    (fun hM E hN => by
      obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hM
      haveI := hN
      rcases Q3T7M.normal_cases3 e E with h | h | ⟨u₀, hu₀E, hu₀4⟩
      · exact Or.inl (by rw [h]; exact bot_le)
      · exact Or.inl h.le
      · exact Or.inr ⟨u₀, hu₀E, hu₀4⟩)
    hbad hK₁ ht g₀ g₁ g₂ hc n₀ m₁

end EndOne
section EndFour
variable [Finite G]

theorem endgame_four_exact (hΩ : HypOmega Ω) {H : Subgroup G}
    {t : G} (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) : False := by
  exact E187C.endgame_four_exact_of
    (fun hK ht hb g₁ g₂ g₃ hc n₁ n₂ => endgame_all hΩ.toMod hK ht hb g₁ g₂ g₃ hc n₁ n₂)
    (fun hK ht g₀ g₁ g₂ hc n₀ m₁ => endgame_one hΩ hbad hK ht g₀ g₁ g₂ hc n₀ m₁)
    (fun hK ht g₁ g₂ g₃ hc m₁ m₂ m₃ => endgame_none hΩ hbad hK ht g₁ g₂ g₃ hc m₁ m₂ m₃) hbad hK₁ ht g₁ g₂ g₃ hc

end EndFour
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

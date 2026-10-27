module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM02
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EK01
public import CFSG.ClassicalInvolution.Q3.Q3T7FUE3
public import CFSG.ClassicalInvolution.Q3.Q3T7FUL

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7E

abbrev _root_.CFSG.ClassicalInvolution.Hat2A7E.Asc77.AEmpty :=
  @CFSG.ClassicalInvolution.Asc77.AEmpty

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G]

theorem HypOmega.toU (h : HypOmega Ω) : CFSG.ClassicalInvolution.T7FU.Asc77.HypOmega .twoA7 Ω :=
  { h with toGen := h.toGen }

theorem exists_twHom (hΩ : HM Ω) {M : Subgroup G} {t : G} (hM : M ∈ Ω)
    (hMt : IsUniqueInvolution M t) :
    ∃ ψ : ↥M →* ↥(twImage t M), Function.Surjective ψ ∧
      ψ.ker = classicalInvolutionOddCore ↥M ∧
      ∀ x : ↥M, ((ψ x : ↥(twImage t M)) : TwQ t) =
        twMk t ⟨(x : G), le_TwC_of_isUniqueInvolution hMt x.2⟩ :=
  CFSG.ClassicalInvolution.T7FU.Asc77.exists_twHom (⟨hΩ, hΩ.toGen⟩) hM hMt

omit [Finite G] in

theorem isSubnormal_twImage (hΩ : HM Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) : IsSubnormal (twImage t M) ⊤ :=
  CFSG.ClassicalInvolution.T7FU.Asc77.isSubnormal_twImage (⟨hΩ, hΩ.toGen⟩) hM hMt

theorem commutes_twImage (hΩ : HM Ω) {M J : Subgroup G} {t : G} (hM : M ∈ Ω)
    (hJ : J ∈ Ω) (hMJ : M ≠ J) (hMt : IsUniqueInvolution M t) (hJt : IsUniqueInvolution J t) :
    Commutes (twImage t M) (twImage t J) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.commutes_twImage (⟨hΩ, hΩ.toGen⟩) hM hJ hMJ hMt hJt

omit [Finite G] in

theorem conjInvariant_twFamily (hΩ : HM Ω) (t : G) : ConjInvariant (twFamily Ω t) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.conjInvariant_twFamily
    (CFSG.ClassicalInvolution.Hat2A7E.HM.toU hΩ) t

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
    have h2 : Nat.card (Subgroup.center ↥K) = 2 := natCard_center_of_exact hz (hex K hK)
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

theorem twFamily_hypOmega (hΩ : HM Ω) (t : G) :
    HypOmega (twFamily Ω t) := by
  have hexM : ∀ {M : Subgroup G}, M ∈ Ω → IsUniqueInvolution M t →
      classicalInvolutionOddCore ↥(twImage t M) = ⊥ := by
    intro M hM hMt
    obtain ⟨ψ, hψs, hψker, -⟩ := exists_twHom hΩ hM hMt
    obtain ⟨z, hz⟩ := hΩ.classical M hM
    let e' : ↥(twImage t M) ≃* ↥M ⧸ classicalInvolutionOddCore ↥M :=
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hψker)
    have hq : CFSG.Open.IsQuasisimple ↥(twImage t M) :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv e' hz.witness.1
    have hZ : Nat.card (Subgroup.center ↥(twImage t M)) = 2 := by
      rw [← hz.natCard_center_eq_two, ← Subgroup.map_center_eq e',
        Subgroup.card_map_of_injective e'.injective]
    exact eq_bot_of_odd_normal hq hZ _ (CFSG.ComponentClassification.OddCore.odd_card _)
  have hex : ExactMembers (twFamily Ω t) := by
    rintro L ⟨M, hM, hMt, rfl⟩
    exact hexM hM hMt
  refine HypOmega.of_commuting (conjInvariant_twFamily hΩ t) ?_ hex ?_
  · rintro L ⟨M, hM, hMt, rfl⟩
    obtain ⟨ψ, hψs, hψker, -⟩ := exists_twHom hΩ hM hMt
    obtain ⟨z, hz⟩ := hΩ.classical M hM
    have : Group.IsPerfect ↥M := hz.perfect Uniform.MemberType.not_isSolvableType_twoA7
    refine ⟨twT t, ?_⟩
    exact
      { admissible := trivial
        orderOf_eq_two := orderOf_eq_prime (by rw [pow_two]; exact twT_sq t hMt.sq)
          (twT_ne_one hMt.sq hMt.ne_one)
        mem := ⟨⟨t, t_mem_TwC t⟩, Subgroup.mem_subgroupOf.mpr hMt.mem, rfl⟩
        perfect := fun _ => Group.IsPerfect.ofSurjective (f := ψ) hψs
        subnormal := by
          rw [centralizer_twT]
          exact isSubnormal_twImage hΩ hM hMt
        witness := Uniform.MemberType.Witness.of_quotientEquiv
          ((((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
            (QuotientGroup.quotientMulEquivOfEq hψker)).symm).trans
            ((QuotientGroup.quotientMulEquivOfEq (hexM hM hMt)).trans
              QuotientGroup.quotientBot).symm) hz.witness }
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
  hyp : HM Ω
  hyp' : HM (quotFamily Ω N)
  central : N ≤ Subgroup.center G
  two : IsPGroup 2 ↥N
  meet : ∀ J ∈ Ω, J ⊓ N = ⊥

theorem _root_.CFSG.ClassicalInvolution.Hat2A7E.Asc77.AscE186.CentQuot.toU {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]
    (c : CFSG.ClassicalInvolution.Hat2A7E.Asc77.AscE186.CentQuot Ω N) :
    CFSG.ClassicalInvolution.T7FU.Asc77.AscE186.CentQuot .twoA7 Ω N :=
  { c with hyp := CFSG.ClassicalInvolution.Hat2A7E.HM.toU c.hyp, hyp' := CFSG.ClassicalInvolution.Hat2A7E.HM.toU c.hyp' }

theorem CentQuot.of_isPGroup (hΩ : HM Ω)
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) :
    CentQuot Ω N :=
  { hyp := hΩ
    hyp' := Hat2A7E.CentQ.quotient_hyp hΩ N hNc (fun K hK => by
      rw [inf_comm, hmeet K hK]
      simp)
    central := hNc
    two := hN2
    meet := hmeet }

namespace CentQuot
open CFSG.ClassicalInvolution.Asc77.AscE186.CentQuot
variable (c : Asc77.AscE186.CentQuot Ω N)
include c

theorem isSylow2In_map {J V : Subgroup G} (hJ : J ∈ Ω) (hV : IsSylow2In V J) :
    IsSylow2In (V.map (QuotientGroup.mk' N)) (J.map (QuotientGroup.mk' N)) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.AscE186.CentQuot.isSylow2In_map c.toU hJ hV

omit [Finite G] in

theorem map_ne_of_ne [Finite G] {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K) :
    J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
  T7FU.Asc77.AscE186.CentQuot.map_ne_of_ne c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hK hJ hne

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
    (hΩ : HM Ω) (S : Sylow 2 G) :
    ∃ W ∈ WSet Ω, W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W :=
  CFSG.ClassicalInvolution.T7FU.Asc77.exists_W_of_hypOmega (⟨hΩ, hΩ.toGen⟩) S

theorem E186Cent2.quot_odd {Ω : Set (Subgroup G)} (hΩ : HM Ω) {N : Subgroup G} [N.Normal]
    (hΩ' : HM (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {K H : Subgroup G} (hK : K ∈ Ω) (h : E186Cent2 Ω K H) :
    E186Cent2 (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N)) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.E186Cent2.quot_odd (⟨hΩ, hΩ.toGen⟩) (⟨hΩ', hΩ'.toGen⟩) hN hK h

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.odd_quot_trans (c : MinCex Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hΩ' : HM (quotFamily Ω N)) (hN : Odd (Nat.card N)) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.odd_quot_trans c.toU (⟨hΩ', hΩ'.toGen⟩) hN

theorem MinCex.odd_quot_stand (c : MinCex Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hΩ' : HM (quotFamily Ω N)) (hN : Odd (Nat.card N)) :
    ∃ (Sb : Sylow 2 (G ⧸ N)) (Rb Wb : Subgroup (G ⧸ N)),
      EStand (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) Sb Rb Wb := by
  have hΩ : HM Ω := c.stand.hyp
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
      below := Hat2A7.CITBelow2A7.mono (natCard_quotient_le N) c.stand.below
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

theorem endgame_one (hΩ : HypOmega Ω) {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {δ₀ δ₁ : G}
    (g₀ : GoodInv H t δ₀) (g₁ : GoodInv H t δ₁) (g₂ : GoodInv H t (δ₀ * δ₁))
    (hc : δ₀ * δ₁ = δ₁ * δ₀) (n₀ : conjSub δ₀ K₁ = K₁) (m₁ : conjSub δ₁ K₁ ≠ K₁) : False := by
  exact E187C.endgame_one_of hΩ.toMod.conjInvariant
    (fun hM h => Hat2A7E.le_of_sq_mem_of_oddGen (hΩ.toMod.oddGen hM) h)
    (fun hM => hΩ.toMod.exists_orderOf_four_of_mem hM)
    (fun hK hJ hKJ hzK hzJ => hΩ.commutes_of_twin hK hJ hKJ hzK hzJ)
    (fun hK ht hw hwc => hΩ.mul_self_eq_one_of_central hK hw hwc)
    (fun hM E hN => by
      have hqs := hΩ.isQuasisimple hM
      rcases normal_eq_top_or_le_center hqs hN with h | h
      · obtain ⟨u, hu, hu4⟩ := hΩ.toMod.exists_orderOf_four_of_mem hM
        exact Or.inr ⟨⟨u, hu⟩, h ▸ Subgroup.mem_top _, by rw [Subgroup.orderOf_mk]; exact hu4⟩
      · exact Or.inl h)
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
end CFSG.ClassicalInvolution.Hat2A7E

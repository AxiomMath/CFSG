module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaTStep1
public import CFSG.GH74.Generic.BProg.B1.Stage3aSD2
public import CFSG.Holt.General.Simple

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.GH74.GLS CFSG.ABGLocalTools

theorem sylow_eq_of_isTwoTerminal {G : Type} [Group G] [Finite G]
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    (hrank : ∀ y : G, orderOf y = 2 → 3 ≤ CFSG.pRank 2 ↥(centralizer ({y} : Set G)))
    {x : G} {K : Subgroup G} (h : IsTwoTerminal x K) {Q R : Subgroup G}
    (hQs : IsSylowOf 2 Q (CxK x K)) (hRs : IsSylowOf 2 R (centralizer (K : Set G)))
    (hQR : Q ≤ R) (hxQ : x ∈ Q) : R = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRC : R ≤ centralizer (K : Set G) := hRs.le
  have hRcs : ∀ r ∈ R, r ∈ centralizerSection K (pPrimeCoreOf 2 K) := fun r hr =>
    CFSG.GH74.Generic.BProg.B1.centralizer_le_centralizerSection K (hRC hr)
  have hRx : R ⊓ centralizer ({x} : Set G) = Q := by
    refine hQs.eq_of_le (le_inf hQR (hQs.le.trans inf_le_left)) (fun g hg => ?_)
      (hRs.isPGroup.to_inf_left)
    exact ⟨hg.2, hRcs g hg.1⟩
  have hxR : x ∈ R := hQR hxQ
  obtain ⟨y, hyR, hy2, hyc⟩ :=
    CFSG.GH74.Generic.BProg.B1.exists_central_involution_of_isPGroup hRs.isPGroup hxR h.1.1
  by_cases hyx : y = x
  · rw [← hRx]
    refine (inf_eq_left.2 fun r hr => ?_).symm
    have := hyc r hr
    rw [hyx] at this
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  · have hyCx : y ∈ centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hyc x hxR)
    have hyQ : y ∈ Q := by rw [← hRx]; exact ⟨hyR, hyCx⟩
    have hyCxK : y ∈ CxK x K := ⟨hyCx, hRcs y hyR⟩
    have hcomp := isCompIn_of_pumpUp_trivial hbal hrank h hyCxK hy2
    have hlt := pumpUpLT_self_of_isCompIn hbal hrank h.1 hyCxK hy2 hcomp
    have hQy := h.2.2 Q hQs y K hlt hyQ (fun q hq => hyc q (hQR hq))
    refine hQy.eq_of_le hQR (fun r hr => ?_) hRs.isPGroup
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (hyc r hr).symm, hRcs r hr⟩

theorem isTerminalPair_of_isTwoTerminal {G : Type} [Group G] [Finite G]
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    (hrank : ∀ y : G, orderOf y = 2 → 3 ≤ CFSG.pRank 2 ↥(centralizer ({y} : Set G)))
    {x : G} {K : Subgroup G} (h : CFSG.GH74.GLS.IsTwoTerminal x K) :
    CFSG.GH74.GLS.IsTerminalPair 2 x K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.IsQuasisimple ↥K := isQuasisimple_of_isILo hbal h.1
  have hx2 : orderOf x = 2 := h.1.1
  have hKle : K ≤ centralizer ({x} : Set G) := (isCompIn_of_isILo hbal h.1).1
  have hCxK : CxK x K ≤ centralizer (K : Set G) :=
    CFSG.GH74.Generic.BProg.CxK_le_centralizer hq
  have h2dvd : 2 ∣ Nat.card ↥K := by
    have hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
    obtain ⟨a, b, hab⟩ := hq.2.2
    have hev : Even (Nat.card (↥K ⧸ Subgroup.center ↥K)) :=
      CFSG.Holt.General.even_card_of_isSimpleGroup ⟨a, b, hab⟩
    exact (even_iff_two_dvd.1 hev).trans (Subgroup.card_quotient_dvd_card _)
  refine ⟨hx2, isCompIn_of_isILo hbal h.1, h2dvd, ?_⟩
  have hxH : x ∈ CxK x K := CFSG.GH74.Generic.BProg.mem_CxK_self hKle
  let X : ↥(CxK x K) := ⟨x, hxH⟩
  have hXord : orderOf X = 2 := by rw [Subgroup.orderOf_mk]; exact hx2
  have hXp : IsPGroup 2 ↥(zpowers X) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hXord]; simp)
  obtain ⟨S, hXS⟩ := hXp.exists_le_sylow
  set Q : Subgroup G := (S : Subgroup ↥(CxK x K)).map (CxK x K).subtype with hQ
  have hQs : IsSylowOf 2 Q (CxK x K) := ⟨S, rfl⟩
  have hxQ : x ∈ Q := ⟨X, hXS (mem_zpowers X), rfl⟩
  set C := centralizer (K : Set G) with hC
  have hQC : Q ≤ C := hQs.le.trans hCxK
  have hQp : IsPGroup 2 ↥Q := hQs.isPGroup
  have hQ' : IsPGroup 2 ↥(Q.subgroupOf C) := hQp.comap_subtype
  obtain ⟨S', hQS'⟩ := hQ'.exists_le_sylow
  set R : Subgroup G := (S' : Subgroup ↥C).map C.subtype with hR
  have hRs : IsSylowOf 2 R C := ⟨S', rfl⟩
  have hQR : Q ≤ R := by
    intro q hq
    exact ⟨⟨q, hQC hq⟩, hQS' (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  have hRQ : R = Q := sylow_eq_of_isTwoTerminal hbal hrank h hQs hRs hQR hxQ
  have hU : CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent K :=
    CFSG.GH74.Generic.BProg.B1.isUniversalComponent_of_sylow hRs fun s hsR hs2 => by
      have hsQ : s ∈ CxK x K := by rw [hRQ] at hsR; exact hQs.le hsR
      exact isCompIn_of_pumpUp_trivial hbal hrank h hsQ hs2
  intro y hy2 hyC
  have h1 : CFSG.Assembly.IsComponentOf K (centralizer ({y} : Set G)) := hU y hyC hy2
  exact ⟨h1.1,
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h1.1).1 h1⟩

end CFSG.OddStandard.SmallF3.HypA2

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Families
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (IsLThreeEps)
open CFSG.LocalAnalysis.RankThreeTheoremC (IsLinThreeCover3)
open TauCeti

@[expose] def T29LThreeEpsCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) (x : X), T29Setup X L x →
    IsLThreeEps (↥L ⧸ center ↥L) → Nat.card (center ↥L) ∣ 3 →
      InducesInnDiagNonInner L x ∧ HasNormalPComplement 3 ↥(centralizer ({x} : Set X)) ∧
        ((∃ y : X, IsPGroup 3 (zpowers y) ∧ InducesNontrivialFieldAut L y) ∨
          9 ≤ Nat.card (CFSG.pCore 3 X))

@[expose] def CentRankAt (d : ValidLieTypeIndex) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → IsSimpleGroup ↥L →
    (∃ a b : ↥L, a * b ≠ b * a) → Nonempty (↥L ≃* (CFSGIndex.lie d).Group) →
      centralizer (L : Set X) = ⊥ → CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 →
        ∀ x : X, orderOf x = 3 → 3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X))

section Index

theorem isLThreeEps_of_isLinThreeCover3 {K : Type} [Group K] {d : ValidLieTypeIndex}
    (hd : IsLinThreeCover3 d) (e : K ≃* (CFSGIndex.lie d).Group) : IsLThreeEps K := by
  obtain ⟨dd, hv⟩ := d
  rcases hd with ⟨q, hq, h3⟩ | ⟨q, hq, h3⟩
  · change dd = .A 2 q at hq
    subst hq
    obtain ⟨-, F, hF, hFin, hcard, ⟨e'⟩⟩ :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    refine Or.inl ⟨F, hF, hFin, ?_, ⟨e'⟩⟩
    have h2 : 2 ≤ q.card := q.isPrimePow_card.two_le
    rw [hcard, ← PrimePower.card_def]
    omega
  · change dd = .twistedA 2 q at hq
    subst hq
    obtain ⟨-, F, hF, hFin, hcard, ⟨e'⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    refine Or.inr ⟨F, hF, hFin, q.p ^ q.exponent, hcard, ?_, ⟨e'⟩⟩
    rw [← PrimePower.card_def]
    omega

end Index

section Setup

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem pRank_component_le (h : T29Setup X L x) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 3 := by
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤
      CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) L.subtype L.subtype_injective ⊤
  have h2 : CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top
  have h3 := h.pRank_top_eq
  omega

@[expose] noncomputable def mulEquivQuotientCenter (hZ : center ↥L = ⊥) :
    ↥L ≃* (↥L ⧸ center ↥L) :=
  (QuotientGroup.quotientBot (G := ↥L)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

theorem false_of_centRankAt (h : T29Setup X L x) (hZ : center ↥L = ⊥)
    {d : ValidLieTypeIndex} (e : (↥L ⧸ center ↥L) ≃* (CFSGIndex.lie d).Group)
    (hd : CentRankAt d) : False := by
  haveI : L.Normal := h.normal
  have hC : centralizer (L : Set X) = ⊥ := h.centralizer_eq_bot hZ
  let f : ↥L ≃* (↥L ⧸ center ↥L) := mulEquivQuotientCenter hZ
  haveI : IsSimpleGroup (↥L ⧸ center ↥L) := h.comp.2.2.2
  haveI : IsSimpleGroup ↥L := f.isSimpleGroup
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := ((CFSG.isComponent_iff_open L).mpr h.comp).1.2.2
    refine ⟨f.symm a, f.symm b, fun hc => hab ?_⟩
    have := congrArg f hc
    simpa using this
  have h3 := hd X L h.normal inferInstance hnab ⟨f.trans e⟩ hC h.pRank_top_eq x h.ord
  rw [h.cent] at h3
  omega

theorem concl_of_lThreeEps (hL3 : T29LThreeEpsCase) (h : T29Setup X L x)
    (hT : IsLThreeEps (↥L ⧸ center ↥L)) (hZ : Nat.card (center ↥L) ∣ 3) : T29Concl X L x :=
  Or.inl ⟨hT, hZ, hL3 X L x h hT hZ⟩

end Setup

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

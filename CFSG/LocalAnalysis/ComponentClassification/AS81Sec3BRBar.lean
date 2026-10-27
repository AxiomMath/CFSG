module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3BR

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint

namespace Sec3

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {x : G}

theorem commutator_map_eq_top {H H' : Type*} [Group H] [Group H'] (f : H →* H')
    {L : Subgroup H} (hL : commutator ↥L = ⊤) : commutator ↥(L.map f) = ⊤ := by
  have hs := f.subgroupMap_surjective L
  have h1 : (commutator ↥L).map (f.subgroupMap L) = commutator ↥(L.map f) := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective _ hs]
  rw [← h1, hL, map_top_of_surjective _ hs]

theorem center_map_le {H : Type*} [Group H] {N : Subgroup H} [N.Normal] {L : Subgroup H}
    (hNL : N ≤ centralizer (L : Set H)) (hL : commutator ↥L = ⊤) :
    Nat.card (center ↥(L.map (QuotientGroup.mk' N))) ∣ Nat.card (center ↥L) := by
  set f := (QuotientGroup.mk' N).subgroupMap L with hf
  have hs : Function.Surjective f := (QuotientGroup.mk' N).subgroupMap_surjective L
  have hker := RankTwoSporadic.ker_quotCenter_map hNL hL
  have hle : center ↥(L.map (QuotientGroup.mk' N)) ≤ (center ↥L).map f := by
    intro c hc
    obtain ⟨a, rfl⟩ := hs c
    refine ⟨a, ?_, rfl⟩
    have h1 : a ∈ ((QuotientGroup.mk' (center ↥(L.map (QuotientGroup.mk' N)))).comp f).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hc
    rw [hf, hker] at h1
    exact h1
  have hge : (center ↥L).map f ≤ center ↥(L.map (QuotientGroup.mk' N)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_center_iff]
    intro b
    obtain ⟨b, rfl⟩ := hs b
    rw [← map_mul, ← map_mul, mem_center_iff.mp ha b]
  rw [le_antisymm hle hge]
  exact card_map_dvd _ _

theorem typeL34_sec3KBar (hS : Sec3Pre G A A₁ R x)
    (hstd : Step31Std) (hBp : commutator ↥(sec3B A₁ x) = ⊤)
    (hBs : NativeSporadic.IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz) :
    TypeL34 (rankTwoQuot ((A₁.subgroupOf (sec3K A₁ R x)).map
      (QuotientGroup.mk' (standardComponentOddCore ↥(sec3K A₁ R x))))) := by
  have hH := rankTwoHyp_sec3K hS hstd hBp hBs
  have hNA := RankTwoSporadic.standardComponentOddCore_le_centralizer hH.standard hH.rank
  let e₁ : ↥(A₁.subgroupOf (sec3K A₁ R x)) ≃* ↥A₁ := subgroupOfEquivOfLe (A₁_le_sec3K hS)
  exact SectionRank.statedClassicalModel_of_mulEquiv
    ((RankTwoSporadic.quotCenterEquivMap hNA hH.standard.1.1).symm.trans
      (RankTwoExceptional.quotCenterCongr e₁)) hS.typeA₁

theorem exists_sec2Setting_sec3K
    (hS : Sec3Pre G A A₁ R x) (hstd : Step31Std) (hII : L34HypII) (h14 : Step14)
    (hL34 : L34General)
    (hBp : commutator ↥(sec3B A₁ x) = ⊤)
    (hBs : NativeSporadic.IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz) :
    ∃ (gb : ↥(sec3K A₁ R x) ⧸ standardComponentOddCore ↥(sec3K A₁ R x))
      (Eb Fb : Subgroup (↥(sec3K A₁ R x) ⧸ standardComponentOddCore ↥(sec3K A₁ R x))),
      Sec2Setting (↥(sec3K A₁ R x) ⧸ standardComponentOddCore ↥(sec3K A₁ R x))
        ((A₁.subgroupOf (sec3K A₁ R x)).map
          (QuotientGroup.mk' (standardComponentOddCore ↥(sec3K A₁ R x))))
        ((R.subgroupOf (sec3K A₁ R x)).map
          (QuotientGroup.mk' (standardComponentOddCore ↥(sec3K A₁ R x)))) gb Eb Fb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := sec3K A₁ R x with hK
  set N := standardComponentOddCore ↥K with hN
  set A' := A₁.subgroupOf K with hA'
  have hH := rankTwoHyp_sec3K hS hstd hBp hBs
  have hodd : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  have hNA := RankTwoSporadic.standardComponentOddCore_le_centralizer hH.standard hH.rank
  have hAp : commutator ↥A' = ⊤ := hH.standard.1.1
  have hHb : RankTwoHypNF (↥K ⧸ N) (A'.map (QuotientGroup.mk' N)) := by
    refine ⟨RankTwoSporadic.standard_map hH.standard hodd hNA, ?_,
      RankTwoSporadic.two_le_pRank_map hodd hNA hAp hH.rank⟩
    intro hn
    apply hH.not_normal
    have h1 : (A' ⊔ N).Normal := by
      have := hn.comap (QuotientGroup.mk' N)
      rwa [comap_map_eq, QuotientGroup.ker_mk'] at this
    rw [← normalizer_eq_top_iff, ← RankTwoSporadic.normalizer_sup_eq hodd hNA hAp]
    exact normalizer_eq_top_iff.mpr h1
  have hT := typeL34_sec3KBar hS hstd hBp hBs
  have hBase : Base (↥K ⧸ N) (A'.map (QuotientGroup.mk' N)) :=
    ⟨hHb, RankTwoSporadic.standardComponentOddCore_quotient_eq_bot,
      hII _ (commutator_map_eq_top _ hAp) hT, Or.inl hT⟩
  have hR : IsSylowOf 2 ((R.subgroupOf K).map (QuotientGroup.mk' N))
      (centralizer ((A'.map (QuotientGroup.mk' N) : Subgroup (↥K ⧸ N)) : Set (↥K ⧸ N))) := by
    rw [RankTwoSporadic.centralizer_map_eq hodd hNA hAp]
    exact AschbacherTheorem3.IsSylowOf.map (isSylowOf_sec3K hS) _
  obtain ⟨gb, Eb, Fb, hFr⟩ := h14 _ _ hBase hT _ hR
  refine ⟨gb, Eb, Fb, hFr, hT, ?_, ?_⟩
  ·
    have h3 : Nat.card (center ↥A') = 3 := by
      rw [← Sec3.card_center_congr (subgroupOfEquivOfLe (A₁_le_sec3K hS)).symm,
        ← card_centerIn, hS.center_A₁, Nat.card_zpowers, hS.order_x]
    have hd := center_map_le hNA hAp
    rw [h3] at hd
    exact Odd.of_dvd_nat (by decide) hd
  ·
    intro G' _ _ A'' _ hH'' hT''
    exact hL34 G' A'' hH'' hT''

end Sec3

end CFSG.ComponentClassification.AS81

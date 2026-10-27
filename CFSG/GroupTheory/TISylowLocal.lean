module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.GroupTheory

open CFSG.CGT.Timmesfeld75
open CFSG.BenderSuzuki

theorem isTI_of_isStronglyEmbeddedOrder_normalizer {G : Type*} [Group G] [Finite G]
    {Q : Sylow 2 G} (h : IsStronglyEmbeddedOrder (Subgroup.normalizer (Q : Set G))) :
    IsTI (Q : Subgroup G) := by
  intro g
  by_cases hg : g ∈ Subgroup.normalizer (Q : Set G)
  · right
    have hconj : conjSubgroup g (Q : Subgroup G) = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    rw [hconj, inf_idem]
  · left
    have hodd : Odd (Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓
        (Subgroup.normalizer (Q : Set G)).map (MulAut.conj g).toMonoidHom)) :=
      h.2.2 g hg
    have hle : (Q : Subgroup G) ⊓ conjSubgroup g (Q : Subgroup G) ≤
        Subgroup.normalizer (Q : Set G) ⊓
          (Subgroup.normalizer (Q : Set G)).map (MulAut.conj g).toMonoidHom :=
      inf_le_inf Subgroup.le_normalizer (Subgroup.map_mono Subgroup.le_normalizer)
    have hdvd : Nat.card ↥((Q : Subgroup G) ⊓ conjSubgroup g (Q : Subgroup G)) ∣
        Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓
          (Subgroup.normalizer (Q : Set G)).map (MulAut.conj g).toMonoidHom) := by
      have h := Subgroup.card_subgroup_dvd_card
        (((Q : Subgroup G) ⊓ conjSubgroup g (Q : Subgroup G)).subgroupOf
          (Subgroup.normalizer (Q : Set G) ⊓
            (Subgroup.normalizer (Q : Set G)).map (MulAut.conj g).toMonoidHom))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
    have hodd' : Odd (Nat.card ↥((Q : Subgroup G) ⊓ conjSubgroup g (Q : Subgroup G))) :=
      Odd.of_dvd_nat hodd hdvd
    rw [Subgroup.eq_bot_iff_card]
    have h2 : IsPGroup 2 ↥((Q : Subgroup G) ⊓ conjSubgroup g (Q : Subgroup G)) :=
      Q.isPGroup'.to_le inf_le_left
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    rw [hn] at hodd'
    have hn0 : n = 0 := by
      by_contra hn0
      exact (Nat.not_even_iff_odd.mpr hodd') (by
        rw [Nat.even_pow]
        exact ⟨even_two, hn0⟩)
    rw [hn0, pow_zero] at hn
    exact hn

theorem inSubgroup_pCore_le_of_isSylow {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {T : Sylow p G} {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) : inSubgroup (pCore p) M ≤ (T : Subgroup G) := by
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p (T : Subgroup G) M := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hTM, T.isPGroup', fun h =>
      T.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hTM))⟩
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hp : pCore p M ≤ (Q : Subgroup M) :=
    (pCore_isPGroup (p := p) (G := M)).le_sylow_of_normal Q
  have hmap : (pCore p M).map M.subtype ≤ (T : Subgroup G) := by
    calc (pCore p M).map M.subtype ≤ (Q : Subgroup M).map M.subtype :=
          Subgroup.map_mono hp
      _ = ((T : Subgroup G).subgroupOf M).map M.subtype := by rw [hQ]
      _ = (T : Subgroup G) ⊓ M := Subgroup.subgroupOf_map_subtype _ M
      _ = (T : Subgroup G) := inf_eq_left.mpr hTM
  simpa [inSubgroup] using hmap

theorem eq_normalizer_of_isTI_sylow {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Sylow 2 G} {M : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) (hTI : IsTI (T : Subgroup G)) :
    M = Subgroup.normalizer (T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR1, hR2, hRM⟩ := hM.1
  have hRleM : R ≤ M := hRM ▸ Subgroup.le_normalizer
  have hRnormal : (R.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRleM).2 (hRM ▸ le_rfl)
  have hRp : R.subgroupOf M ≤ pCore 2 M :=
    le_sSup ⟨hRnormal, hR2.comap_subtype⟩
  have hRin : R ≤ (pCore 2 M).map M.subtype := by
    have h := Subgroup.map_mono (f := M.subtype) hRp
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRleM] at h
  have hRT : R ≤ (T : Subgroup G) := hRin.trans (inSubgroup_pCore_le_of_isSylow hTM)
  have hTne : (T : Subgroup G) ≠ ⊥ := fun hbot =>
    hR1 (le_bot_iff.mp (hRT.trans_eq hbot))
  have hMle : M ≤ Subgroup.normalizer (T : Set G) := by
    intro g hg
    have hgR : conjSubgroup g R = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRM ▸ hg)
    have hRinf : R ≤ (T : Subgroup G) ⊓ conjSubgroup g (T : Subgroup G) := by
      refine le_inf hRT ?_
      calc R = conjSubgroup g R := hgR.symm
        _ ≤ conjSubgroup g (T : Subgroup G) := Subgroup.map_mono hRT
    have hne : (T : Subgroup G) ⊓ conjSubgroup g (T : Subgroup G) ≠ ⊥ := fun hbot =>
      hR1 (le_bot_iff.mp (hRinf.trans_eq hbot))
    rcases hTI g with h | h
    · exact absurd h hne
    · have hle : (T : Subgroup G) ≤ conjSubgroup g (T : Subgroup G) := by
        calc (T : Subgroup G) = (T : Subgroup G) ⊓ conjSubgroup g (T : Subgroup G) := h.symm
          _ ≤ conjSubgroup g (T : Subgroup G) := inf_le_right
      have heq : conjSubgroup g (T : Subgroup G) = T :=
        (Subgroup.eq_of_le_of_card_ge hle (by
          rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g).injective])).symm
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have hNloc : IsPLocal 2 (Subgroup.normalizer (T : Set G)) :=
    ⟨(T : Subgroup G), hTne, T.isPGroup', rfl⟩
  have hNproper : Subgroup.normalizer (T : Set G) ≠ ⊤ := by
    intro htop
    have hTnormal : (T : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    haveI : (T : Subgroup G).Normal := hTnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T : Subgroup G) with hbot | htopT
    · exact hTne hbot
    · have hP : IsPGroup 2 G := by
        have htop2 : IsPGroup 2 (⊤ : Subgroup G) := htopT ▸ T.isPGroup'
        exact htop2.of_equiv Subgroup.topEquiv
      haveI : Group.IsNilpotent G := hP.isNilpotent
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)
  by_contra hne
  exact hM.2 (Subgroup.normalizer (T : Set G)) (lt_of_le_of_ne hMle hne) hNloc

theorem weaklyClosedIn_of_isTI_sylow {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Sylow 2 G} {M V : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) (hTI : IsTI (T : Subgroup G))
    (hV : V ≤ M) (hQ : WeaklyClosedIn V (inSubgroup (pCore 2) M)) :
    WeaklyClosedIn V M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTeq : M = Subgroup.normalizer (T : Set G) :=
    eq_normalizer_of_isTI_sylow hnonab hM hTM hTI
  have hTnormal : (T.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTM).2 (hTeq ▸ le_rfl)
  have hTle : (T : Subgroup G) ≤ (pCore 2 M).map M.subtype := by
    have hT2 : IsPGroup 2 (T.subgroupOf M) := T.isPGroup'.comap_subtype
    have hp : T.subgroupOf M ≤ pCore 2 M := le_sSup ⟨hTnormal, hT2⟩
    have h := Subgroup.map_mono (f := M.subtype) hp
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTM] at h
  have hTO : (T : Subgroup G) = inSubgroup (pCore 2) M :=
    le_antisymm hTle (inSubgroup_pCore_le_of_isSylow hTM)
  have hTwoLe : ∀ U : Subgroup G, U ≤ M → IsPGroup 2 U → U ≤ (T : Subgroup G) := by
    intro U hUM hU2
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup G) M := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      exact ⟨hTM, T.isPGroup', fun h =>
        T.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hTM))⟩
    obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
    have hQnormal : (Q : Subgroup M).Normal := hQ ▸ hTnormal
    have hUsub : IsPGroup 2 (U.subgroupOf M) := hU2.comap_subtype
    obtain ⟨S, hUS⟩ := hUsub.exists_le_sylow
    have hQS : (Q : Subgroup M) ≤ S := IsPGroup.le_sylow_of_normal Q.isPGroup' S
    have hSQ : S = (Q : Subgroup M) := Q.is_maximal' S.isPGroup' hQS
    have h := Subgroup.map_mono (f := M.subtype) (hSQ ▸ hUS)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUM,
      hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTM] at h
  refine ⟨hV, ?_⟩
  intro g hg
  have hV2 : IsPGroup 2 V :=
    (pCore_isPGroup (p := 2) (G := M)).map M.subtype |>.to_le hQ.1
  have hconj2 : IsPGroup 2 (conjSubgroup g V) := hV2.map _
  have hle : conjSubgroup g V ≤ inSubgroup (pCore 2) M := by
    rw [← hTO]
    exact hTwoLe (conjSubgroup g V) hg hconj2
  exact hQ.2 g hle

end CFSG.GroupTheory

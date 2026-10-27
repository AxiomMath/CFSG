module

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.ABGLocalTools Subgroup

section KSecLiftTorus

variable {X : Type} [Group X] [Finite X]

theorem kSecLiftTorus_mem_map_inf_sup {T T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hL : LiftOf T L Ls) {a : X ⧸ gnC T} (ha : a ∈ gnA T T₂ Ls) :
    a ∈ (Subgroup.normalizer (T₂ : Set X) ⊓ (L ⊔ gnC T)).map (toStar T) := by
  obtain ⟨⟨n, hn, rfl⟩, haL⟩ := ha
  refine ⟨n, ⟨hn, ?_⟩, rfl⟩
  have h1 : n ∈ Ls.comap (toStar T) := haL
  rwa [← hL.2, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1

theorem kSecLiftTorus_map_inf_sup_le {T T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hL : LiftOf T L Ls) :
    (Subgroup.normalizer (T₂ : Set X) ⊓ (L ⊔ gnC T)).map (toStar T) ≤ gnA T T₂ Ls := by
  have hmapH : (L ⊔ gnC T).map (toStar T) = L.map (toStar T) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  rintro _ ⟨n, ⟨hn, hnH⟩, rfl⟩
  refine ⟨⟨n, hn, rfl⟩, ?_⟩
  rw [← hL.2, ← hmapH]
  exact ⟨n, hnH, rfl⟩

theorem gnA_frattini_two {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hg : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hL : LiftOf T L Ls) (hLn : L.Normal)
    {a : X ⧸ gnC T} (ha : a ∈ gnA T T₂ Ls) :
    ∃ n ∈ gnA T T₂ Ls,
      n ∈ Subgroup.normalizer ((T ⊓ L).map (toStar T) : Set (X ⧸ gnC T)) ∧
        ∃ b ∈ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T), a = n * b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hLn
  obtain ⟨d, hdD, rfl⟩ := kSecLiftTorus_mem_map_inf_sup hL ha
  have hTN : T ≤ Subgroup.normalizer (T₂ : Set X) := IsGNPair.le_normalizer₂ hg.pair
  set D : Subgroup X := Subgroup.normalizer (T₂ : Set X) ⊓ (L ⊔ gnC T) with hD
  set K : Subgroup X := Subgroup.normalizer (T₂ : Set X) ⊓ L with hK
  have hKD : K ≤ D := inf_le_inf_left _ le_sup_left
  have hUK : T ⊓ L ≤ K := inf_le_inf_right _ hTN
  have hTT : IsSylowOf 2 T ⊤ := isSylowOf_iff.2 ⟨hX.sylow.1, hX.sylow.2.1, hX.sylow.2.2⟩
  have hTL : IsSylowOf 2 (T ⊓ L) L :=
    hTT.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top L).ge
  have hUK' : IsSylowOf 2 (T ⊓ L) K := hTL.of_le hUK inf_le_right
  have hDK : D ≤ Subgroup.normalizer (K : Set X) := by
    refine Subgroup.le_normalizer_iff.2 fun x hx k hk => ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx.1 hk.1) (Subgroup.inv_mem _ hx.1)
    · exact hLn.conj_mem k hk.2 x
  haveI hKn : (K.subgroupOf D).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKD).2 hDK
  have hSylD : IsSylowOf 2 ((T ⊓ L).subgroupOf D) (K.subgroupOf D) := by
    refine (isSylowOf_map_subtype_iff D).1 ?_
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (hUK.trans hKD), inf_eq_left.2 hKD]
  obtain ⟨Q, hQ⟩ := hSylD.exists_sylow_eq_subgroupOf
  have hUKD : (T ⊓ L).subgroupOf D ≤ K.subgroupOf D := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hUK (Subgroup.mem_subgroupOf.1 hx))
  have hfr := Sylow.normalizer_sup_eq_top Q
  rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUKD] at hfr
  have hdmem : (⟨d, hdD⟩ : ↥D) ∈
      Subgroup.normalizer (((T ⊓ L).subgroupOf D : Subgroup ↥D) : Set ↥D) ⊔ K.subgroupOf D := by
    rw [hfr]
    exact Subgroup.mem_top _
  obtain ⟨m, hm, k, hk, hmk⟩ := Subgroup.mem_sup_of_normal_right.1 hdmem
  have hmk' : (m : X) * (k : X) = d := congrArg Subtype.val hmk
  have hmN : (m : X) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup X) : Set X) := by
    have h1 : m ∈ (Subgroup.normalizer ((T ⊓ L : Subgroup X) : Set X)).subgroupOf D := by
      rw [Subgroup.subgroupOf_normalizer_eq (hUK.trans hKD)]
      exact hm
    exact h1
  refine ⟨toStar T m, kSecLiftTorus_map_inf_sup_le hL ⟨(m : X), m.2, rfl⟩, ?_, toStar T k,
    ⟨(k : X), Subgroup.mem_subgroupOf.1 hk, rfl⟩, ?_⟩
  · exact Subgroup.le_normalizer_map (toStar T) ⟨(m : X), hmN, rfl⟩
  · rw [← map_mul, hmk']

end KSecLiftTorus

end CFSG.LocalAnalysis.RankThreeUC.S15

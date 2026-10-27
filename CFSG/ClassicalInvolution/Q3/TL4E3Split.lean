module

public import CFSG.ClassicalInvolution.Q3.TL4E3Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

namespace E3

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_secDatum (hd : TightDatum R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) :
    ∃ Sq : Sylow 2 ↥(secR R u), TightDatum (secR R u) Sq
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) := by
  obtain ⟨-, hu2, hut, -, huK, -⟩ := hd.edge_involution hJ hu
  have hcomm : ∀ r ∈ R, ⁅u, r⁆ ∈ oddCoreImg R := (hd.act_eq_one_iff hut).mp huK
  have huN : u ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hut
  have huC : u ∈ centralizerModOdd ⊤ R :=
    ⟨Subgroup.mem_top u, huN, mem_normalizer_oddCore_of_mem_normalizer huN, hcomm⟩
  obtain ⟨S', hS'⟩ := hd.exists_sylow_le_centralizer
    (Balance.isPGroup_zpowers_of_mul_self_eq_one hu2) (Subgroup.zpowers_le.mpr huC)
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({u} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers u)))
  obtain ⟨S₁, hd₁, -⟩ := (hd.ofSylow S').restrict hS'u
  have hSH : (S₁ : Subgroup ↥(R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))).map
      (R.subgroupOf (Subgroup.centralizer ({u} : Set Y))).subtype ≤ secH R u :=
    hd₁.sylow_core.1.trans (le_subnormalClosure _)
  obtain ⟨S₂, hd₂, -⟩ := hd₁.restrict hSH
  exact ⟨_, OddQ.datum hd₂ (CFSG.ComponentClassification.OddCore.odd_card _)⟩

end E3

section Cit3


theorem tightE3LeafR'_of_parts {r n : ℕ} (hZ2 : TightE3Z2R r n) (hS3 : TightE3S3R r n)
    (hE4 : TightE3E4R r n) : TightE3LeafR' r n := by
  classical
  intro Y _ _ R S t hL hcn hsp hα J hJ u hu htu ht Sb hex
  by_cases hedge : TightEdgeless (secR R u)
  · obtain ⟨Sq, hdq⟩ := E3.exists_secDatum hL.datum hJ.1.2 hu htu ht
    have hP := hdq.partIHypG
    by_cases hsh : ∀ K ∈ CoreAssembly.conjClass (tightCore (secR R u)),
        omegaStarNbr (CoreAssembly.conjClass (tightCore (secR R u))) K = ∅
    · exact hZ2 Y R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge fun W hW =>
        Q3T6.Mu.muIsoZ2_of_shape hP hW ⟨_, CoreAssembly.mem_conjClass_self _⟩ hsh
    · push Not at hsh
      obtain ⟨K, hK, hne⟩ := hsh
      exact hS3 Y R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge fun W hW =>
        Q3T6.Mu.muIsoS3_of_shape hP hW hedge ⟨K, hK, hne⟩
  · exact hE4 Y R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge

theorem tightE3LeafR''_of_parts {r n : ℕ} (hZ2 : TightE3Z2R r n) (hS3 : TightE3S3R r n) :
    TightE3LeafR'' r n := by
  classical
  intro Y _ _ R S t hL hcn hsp hα J hJ u hu htu ht Sb hex
  by_cases hedge : TightEdgeless (secR R u)
  · left
    obtain ⟨Sq, hdq⟩ := E3.exists_secDatum hL.datum hJ.1.2 hu htu ht
    have hP := hdq.partIHypG
    by_cases hsh : ∀ K ∈ CoreAssembly.conjClass (tightCore (secR R u)),
        omegaStarNbr (CoreAssembly.conjClass (tightCore (secR R u))) K = ∅
    · exact hZ2 Y R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge fun W hW =>
        Q3T6.Mu.muIsoZ2_of_shape hP hW ⟨_, CoreAssembly.mem_conjClass_self _⟩ hsh
    · push Not at hsh
      obtain ⟨K, hK, hne⟩ := hsh
      exact hS3 Y R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge fun W hW =>
        Q3T6.Mu.muIsoS3_of_shape hP hW hedge ⟨K, hK, hne⟩
  · rcases hex with h | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact Or.inl h
    · exact absurd h hedge
    · exact absurd h hedge
    · exact Or.inr h

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

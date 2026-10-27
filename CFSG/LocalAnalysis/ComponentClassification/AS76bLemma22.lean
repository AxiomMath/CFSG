module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22Basic

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22

variable {G : Type*} [Group G] [Finite G]

theorem lemma22_core {K R L : Subgroup G} (hKs : Group.IsSolvable ↥K) (hK : TightlyEmbedded K)
    (hR : IsSylowOf 2 R K) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hNL : normalizer (K : Set G) ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R (centralizer (L : Set G))) :
    standardComponentIsStandard L ∨
      ∃ g : G, conj L g ≤ centralizer (L : Set G) ∧
        centralizer (L : Set G) ≤ normalizer (conj L g : Set G) ∧
        IsSylowOf 2 (R ⊓ conj L g) (conj L g) ∧
        fusionStronglyEmbedded ((conj L g ⊓ normalizer (K : Set G)).subgroupOf (conj L g)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer (L : Set G) with hHdef
  have hR1 : R ≠ ⊥ := ne_bot_of_isSylowOf_of_tightlyEmbedded hK hR
  have hNKH : normalizer (K : Set G) ≤ normalizer (H : Set G) :=
    hNL.trans (normalizer_le_normalizer_centralizer L)
  have hH : TightlyEmbedded H := tightlyEmbedded_of_isSylowOf hK hR hRL hR1 hNKH
  have hNH : normalizer (H : Set G) = normalizer (L : Set G) :=
    le_antisymm (normalizer_centralizer_le hK hR hRL hR1 hNL)
      (normalizer_le_normalizer_centralizer L)
  by_cases hstd : ∀ g : G, ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥
  · left
    refine ⟨hL, hH.1, fun g hg => ?_, hNH, hstd⟩
    have hg' : g⁻¹ ∉ normalizer (H : Set G) := fun h => hg (by simpa using inv_mem h)
    simpa [rightConjugate] using hH.2 g⁻¹ hg'
  · right
    push Not at hstd
    obtain ⟨g, hg⟩ := hstd
    set A := conj L g with hAdef
    have hLA : L ≤ centralizer (A : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hg
    have hAH : A ≤ H := le_centralizer_iff.mp hLA
    refine ⟨g, hAH, ?_⟩
    have hHA : H ≤ normalizer (A : Set G) := by
      obtain ⟨T, hT⟩ := exists_isSylowOf 2 L
      have hT1 : T ≠ ⊥ := by
        intro hbot
        have hcard := hT.card_eq
        rw [hbot, Subgroup.card_bot] at hcard
        have h2 : 2 ∣ Nat.card L := even_iff_two_dvd.mp (even_card_of_isQuasisimple hL)
        have hpos : 0 < (Nat.card L).factorization 2 :=
          Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
        exact (Nat.one_lt_pow hpos.ne' (by norm_num)).ne' hcard.symm
      have hCA : centralizer (A : Set G) = conj H g := centralizer_conj L g
      have hCAt : TightlyEmbedded (centralizer (A : Set G)) := by
        rw [hCA]
        exact tightlyEmbedded_conj hH g
      have hTCA : T ≤ centralizer (A : Set G) := hT.le.trans hLA
      have h1 := centralizer_two_subgroup_le _ T hCAt hT.isPGroup hTCA hT1
      have hNCA : normalizer (centralizer (A : Set G) : Set G) = normalizer (A : Set G) := by
        rw [hCA, normalizer_conj, hNH, ← normalizer_conj]
      have hHT : H ≤ centralizer (T : Set G) := centralizer_le hT.le
      exact hHT.trans (h1.trans hNCA.le)
    refine ⟨hHA, ?_⟩
    have hS : IsSylowOf 2 (R ⊓ A) A := hRL.inf_of_le_normalizer hAH hHA
    refine ⟨hS, ?_⟩
    have hAq : CFSG.Open.IsQuasisimple ↥A := isQuasisimple_conj hL g
    have hSK : R ⊓ A ≤ K := inf_le_left.trans hR.le
    have hS1 : R ⊓ A ≠ ⊥ := by
      intro hbot
      apply not_le_centralizer_of_isSylowOf hAq hS
      rw [hbot]
      exact bot_le
    have hAK : ¬ A ≤ normalizer (K : Set G) := by
      intro hAN
      rcases le_or_inf_le_centralizer hAq hAN with hAK | hAK
      · have : Group.IsSolvable ↥A := Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hAK) (Subgroup.inclusion_injective hAK)
        have : Group.IsPerfect ↥A := ⟨hAq.1⟩
        have : Nontrivial ↥A := by
          obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute hAq
          refine ⟨⟨⟨a, ha⟩, 1, fun h => hab ?_⟩⟩
          have : a = 1 := congrArg Subtype.val h
          rw [this, one_mul, mul_one]
        exact Group.IsPerfect.not_isSolvable ↥A inferInstance
      · apply not_le_centralizer_of_isSylowOf hAq hS
        intro x hx
        exact hAK (mem_inf.mpr ⟨(mem_inf.mp hx).2, hR.le (mem_inf.mp hx).1⟩)
    exact fusionStronglyEmbedded_of_tightlyEmbedded hK hS hSK hS1 hAK

end CFSG.ComponentClassification.AS76b

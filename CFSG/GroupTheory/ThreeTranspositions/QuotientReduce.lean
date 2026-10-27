module

public import CFSG.GroupTheory.ThreeTranspositions.QuotientLift
public import CFSG.GroupTheory.ThreeTranspositions.StrongSup
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.GroupTheory.ThreeTranspositions

@[expose] def NoThreeTranspositionClass : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (Y : Subgroup Q) (t : Q),
    CFSG.pPrimeCore 3 Q = ⊥ → ¬ HasE9 Q →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 Y →
    (∃ S : Sylow 2 Q, (S : Subgroup Q) ≤ Y) → t ^ 2 = 1 → t ≠ 1 →
    ∃ a : Q, (t * (a * t * a⁻¹)) ^ 2 ≠ 1 ∧ (t * (a * t * a⁻¹)) ^ 3 ≠ 1

theorem mem_relPPrimeCore_iff {A : Type*} [Group A] [Finite A] (H : Subgroup A) (y : ↥H) :
    (y : A) ∈ CFSG.Open.relPPrimeCore 3 H ↔ y ∈ CFSG.pPrimeCore 3 ↥H := by
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
    Nat.prime_three H]
  constructor
  · rintro ⟨z, hz, hzy⟩
    rwa [← Subtype.ext hzy]
  · intro h
    exact ⟨y, h, rfl⟩

theorem isStronglyPEmbedded_map_quotient_pPrimeCore {A : Type*} [Group A] [Finite A]
    {H H₀ : Subgroup A} (hH₀ : H₀ ≤ H)
    (hY : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 (H₀.subgroupOf H))
    (hne : ¬ H ≤ H₀ ⊔ CFSG.Open.relPPrimeCore 3 H) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3
      ((H₀.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isStronglyPEmbedded_map_mk_of_sup_ne_top Nat.prime_three hY
    (N := CFSG.pPrimeCore 3 ↥H) ?_ ?_
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  · intro htop
    apply hne
    have h := congrArg (Subgroup.map H.subtype) htop
    rw [Subgroup.map_sup,
      ← CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
        Nat.prime_three H, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH₀] at h
    exact h.ge

theorem exists_sylow_two_le_map_quotient {A : Type*} [Group A] [Finite A] {H H₀ : Subgroup A}
    (hS : ∃ S : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ H₀) :
    ∃ S' : Sylow 2 (↥H ⧸ CFSG.pPrimeCore 3 ↥H),
      (S' : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) ≤
        (H₀.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) := by
  obtain ⟨S, hSyl, hSH₀⟩ := hS
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  refine ⟨Q.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective]
  exact Subgroup.map_mono (hQ ▸ Subgroup.comap_mono hSH₀)

theorem sq_or_cube_quotient_pPrimeCore {A : Type*} [Group A] [Finite A] (H : Subgroup A)
    (t' : ↥H)
    (h : ∀ a : ↥H, ((t' : A) * ((a : A) * (t' : A) * (a : A)⁻¹)) ^ 2 ∈
        CFSG.Open.relPPrimeCore 3 H ∨
      ((t' : A) * ((a : A) * (t' : A) * (a : A)⁻¹)) ^ 3 ∈ CFSG.Open.relPPrimeCore 3 H)
    (b : ↥H ⧸ CFSG.pPrimeCore 3 ↥H) :
    (QuotientGroup.mk t' * (b * QuotientGroup.mk t' * b⁻¹)) ^ 2 = 1 ∨
      (QuotientGroup.mk t' * (b * QuotientGroup.mk t' * b⁻¹)) ^ 3 = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
  have hx : (QuotientGroup.mk t' * (QuotientGroup.mk a * QuotientGroup.mk t' *
      (QuotientGroup.mk a)⁻¹) : ↥H ⧸ CFSG.pPrimeCore 3 ↥H) =
      QuotientGroup.mk (t' * (a * t' * a⁻¹)) := rfl
  rw [hx, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    QuotientGroup.eq_one_iff, ← mem_relPPrimeCore_iff, ← mem_relPPrimeCore_iff]
  exact h a

theorem exists_sq_cube_not_mem_relPPrimeCore (hcore : NoThreeTranspositionClass) (A : Type)
    [Group A] [Finite A] (H H₀ : Subgroup A) (t : A) (hH₀ : H₀ ≤ H)
    (hr : CFSG.Open.pRank 3 H ≤ 1)
    (hY : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 (H₀.subgroupOf H))
    (hS : ∃ S : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ H₀)
    (hne : ¬ H ≤ H₀ ⊔ CFSG.Open.relPPrimeCore 3 H) (htH : t ∈ H) (ht2 : t ^ 2 = 1)
    (htK : t ∉ CFSG.Open.relPPrimeCore 3 H) :
    ∃ a ∈ H, (t * (a * t * a⁻¹)) ^ 2 ∉ CFSG.Open.relPPrimeCore 3 H ∧
      (t * (a * t * a⁻¹)) ^ 3 ∉ CFSG.Open.relPPrimeCore 3 H := by
  by_contra hcon
  have hall : ∀ a ∈ H, (t * (a * t * a⁻¹)) ^ 2 ∈ CFSG.Open.relPPrimeCore 3 H ∨
      (t * (a * t * a⁻¹)) ^ 3 ∈ CFSG.Open.relPPrimeCore 3 H := by
    intro a ha
    by_contra hh
    exact hcon ⟨a, ha, fun h2 => hh (Or.inl h2), fun h3 => hh (Or.inr h3)⟩
  have ht2' : (QuotientGroup.mk (⟨t, htH⟩ : ↥H) : ↥H ⧸ CFSG.pPrimeCore 3 ↥H) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨t, htH⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [this]
    rfl
  have ht1' : (QuotientGroup.mk (⟨t, htH⟩ : ↥H) : ↥H ⧸ CFSG.pPrimeCore 3 ↥H) ≠ 1 := by
    intro h1
    exact htK ((mem_relPPrimeCore_iff H ⟨t, htH⟩).mpr ((QuotientGroup.eq_one_iff _).mp h1))
  obtain ⟨b, hb2, hb3⟩ := hcore (↥H ⧸ CFSG.pPrimeCore 3 ↥H)
    ((H₀.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)))
    (QuotientGroup.mk (⟨t, htH⟩ : ↥H))
    (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three) (not_hasE9_quotient_pPrimeCore H hr)
    (isStronglyPEmbedded_map_quotient_pPrimeCore hH₀ hY hne)
    (exists_sylow_two_le_map_quotient hS) ht2' ht1'
  rcases sq_or_cube_quotient_pPrimeCore H ⟨t, htH⟩ (fun a => hall a a.2) b with h2 | h3
  · exact hb2 h2
  · exact hb3 h3

end CFSG.GroupTheory.ThreeTranspositions

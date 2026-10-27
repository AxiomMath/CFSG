module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.GH74.Defs
public import CFSG.Blueprint.Catalog
public import CFSG.GH74.KGroups.Sz8
public import CFSG.GH74.KGroups.Sz8Tables
public import CFSG.GH74.KGroups.CoverRank
import CFSG.Goldschmidt.Steps.GSz8Mult
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.SectionalRank
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.GH74.KGroups.CoverSz8

open CFSG.Blueprint

theorem equiv_sz_of_lieModel {G : Type} [Group G] (h : LieModel G .twistedB2 0 2 3) :
    Nonempty (G ≃* CFSG.Open.Sz 1) := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := hS
    have ha1 : a = 1 := by omega
    subst ha1
    obtain ⟨e1⟩ := Sz8.suz_equiv_matrix F hF
    exact ⟨e.trans (e1.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv 1).symm)⟩

theorem sz8_cover :
    ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → LieModel (K ⧸ Subgroup.center K) .twistedB2 0 2 3 →
      Nat.card (Subgroup.center K) ≤ 2 ∨ ¬ CFSG.GH74.Gen4 K := by
  intro K _ _ hK hZ2 h
  by_cases hle : Nat.card (Subgroup.center K) ≤ 2
  · exact Or.inl hle
  refine Or.inr ?_
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  obtain ⟨eS⟩ := equiv_sz_of_lieModel h
  have hquasi : CFSG.Open.IsQuasisimple K := ⟨hperf, hsimple⟩
  have hle4 : Nat.card (Subgroup.center K) ≤ 4 := CFSG.Goldschmidt.GSz8Mult K hquasi ⟨eS⟩
  have hel := (CFSG.Goldschmidt.GSz8Mult.isElemAbelian_center hquasi eS).2
  set Z : Subgroup K := Subgroup.center K with hZdef
  have hZcard : Nat.card Z = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := hZ2.exists_card_eq
    have hm2 : m = 2 := by
      by_contra hne
      rcases Nat.lt_or_ge m 2 with hm3 | hm3
      · have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    rw [hm, hm2]
    norm_num
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hZc : ∀ z ∈ Z, ∀ g : K, g * z = z * g := fun z hz g => Subgroup.mem_center_iff.1 hz g
  obtain ⟨T⟩ : Nonempty (Sylow 2 (K ⧸ Z)) := inferInstance
  obtain ⟨hT1, hT2, hT3, x, hxN, hxtrans⟩ :=
    Sz8.bender h (T : Subgroup (K ⧸ Z)) T.isPGroup' T.not_dvd_index
  have hEcard := Sz8.bender_card h (T : Subgroup (K ⧸ Z)) T.isPGroup' T.not_dvd_index
  set E : Subgroup (K ⧸ Z) := (T : Subgroup (K ⧸ Z)) ⊓
    Subgroup.centralizer ((T : Subgroup (K ⧸ Z)) : Set (K ⧸ Z)) with hEdef
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have hbT : b ∈ (T : Subgroup (K ⧸ Z)) := (Subgroup.mem_inf.1 hb).1
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ha).2) b hbT).symm
  obtain ⟨e1, e2, e3, h1, h2, h3, i1, i2, i3, i12, i13, i23, i123⟩ :=
    exists_independent_triple E hT2 hEc (by rw [hEcard]; norm_num)
  have hconj : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → ∃ g : K ⧸ Z, g * a * g⁻¹ = b := by
    intro a ha ha1 b hb hb1
    obtain ⟨k, hk⟩ := hxtrans a ha b hb ha1 hb1
    exact ⟨x ^ k, hk⟩
  have hA := preimage_elementary π hπ Z hker hZc hel E hT2 hconj e1 e2 e3 h1 h2 h3 i1 i2 i3 i12
    i13 i23 i123
  have hAcard : Nat.card (E.comap π) = 32 := by
    rw [card_comap_of_surjective π hπ E, hEcard, hker, hZcard]
  exact fun hG => not_genLE4_of_elementary (E.comap π) hA hAcard hG

end CFSG.GH74.KGroups.CoverSz8

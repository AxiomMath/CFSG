module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.SignalizerFunctor.Helpers

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def theta (A : Subgroup G) (b : G) : Subgroup G :=
  ⁅oddCoreOf (cen b), A⁆ ⊔ (oddCoreOf (centralizer (A : Set G)) ⊓ cen b)

section Elementary

variable {B A : Subgroup G}

theorem le_normalizer_oddCore_cen (hB2 : ∀ b ∈ B, b ^ 2 = 1) {b : G} (hb : b ∈ B) :
    B ≤ normalizer (oddCoreOf (cen b) : Set G) :=
  fun _ hx => le_normalizer_oddCoreOf (cen b) (mem_cen_of_mem hB2 hb hx)

theorem N_le_normalizer_S {b : G} :
    (oddCoreOf (centralizer (A : Set G)) ⊓ cen b) ≤
      normalizer ((⁅oddCoreOf (cen b), A⁆ : Subgroup G) : Set G) := by
  intro n hn
  apply mem_normalizer_commutator
  · exact le_normalizer_oddCoreOf (cen b) hn.2
  · exact centralizer_le_normalizer _ (oddCoreOf_le _ hn.1)

end Elementary

section Balance

variable [Finite G] {B A : Subgroup G}

variable {QK XK : G → Subgroup G}

@[expose] def oddTwoCoreOf (H : Subgroup G) : Subgroup G :=
  ((pCore 2 (H ⧸ pPrimeCore 2 H)).comap (QuotientGroup.mk' (pPrimeCore 2 H))).map H.subtype

omit [Finite G] in
theorem oddTwoCoreOf_le (H : Subgroup G) : oddTwoCoreOf H ≤ H := by
  rintro _ ⟨h, -, rfl⟩
  exact h.2

omit [Finite G] in
theorem le_normalizer_oddTwoCoreOf (H : Subgroup G) :
    H ≤ normalizer (oddTwoCoreOf H : Set G) := by
  have hsub : (oddTwoCoreOf H).subgroupOf H =
      (pCore 2 (H ⧸ pPrimeCore 2 H)).comap (QuotientGroup.mk' (pPrimeCore 2 H)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hn : ((oddTwoCoreOf H).subgroupOf H).Normal := by
    rw [hsub]
    exact Subgroup.Normal.comap inferInstance _
  exact (normal_subgroupOf_iff_le_normalizer (oddTwoCoreOf_le H)).mp hn

omit [Finite G] in
theorem oddTwoCoreOf_two (H : Subgroup G) {q : G} (hq : q ∈ oddTwoCoreOf H) :
    ∃ k : ℕ, q ^ (2 ^ k) ∈ oddCoreOf H := by
  obtain ⟨h, hh, rfl⟩ := hq
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := H ⧸ pPrimeCore 2 H))
    ⟨QuotientGroup.mk' (pPrimeCore 2 H) h, hh⟩
  refine ⟨k, ?_⟩
  have h1 : (QuotientGroup.mk' (pPrimeCore 2 H)) (h ^ (2 ^ k)) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have h2 : h ^ (2 ^ k) ∈ pPrimeCore 2 H := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨h ^ (2 ^ k), h2, by simp⟩

end Balance

end CFSG.OddStandard.Solomon75

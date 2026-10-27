module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntTodd
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.MathieuExt

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open Subgroup CFSG.Fischer ToddOrbit CFSG.EvenSmallLie.UnitarySix.MathieuExt
  CFSG.ComponentClassification.WittDesign CFSG.Quasithin

@[expose] def ToddRankBounds :
    Prop :=
  (∀ (X : Subgroup (Equiv.Perm (Fin 22))) (hX : X ≤ hexadAut), (∀ x ∈ X, x * x = 1) →
    ¬ X ≤ M22 →
      Nat.card X * Nat.card {v : toddModule // ∀ x (hx : x ∈ X), toddAct (hX hx) v = v} ≤
        2 ^ 8) ∧
  ∀ (X : Subgroup (Equiv.Perm (Fin 22))) (hX : X ≤ hexadAut), (∀ x ∈ X, x * x = 1) →
    X ≤ M22 → X ≠ ⊥ →
      Nat.card X * Nat.card {v : toddModule // ∀ x (hx : x ∈ X), toddAct (hX hx) v = v} ≤ 2 ^ 9

variable {G : Type*} [Group G] [Finite G] {t : G} {L E : Subgroup G}
  {p : L →* Equiv.Perm (Fin 693)}

omit [Finite G] in
theorem mul_self_of_mem_map {f : orb E t ≃ Fin 22} {B : Subgroup G} (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    ∀ x ∈ (B.subgroupOf (normalizer (E : Set G))).map (rhoF f), x * x = 1 := by
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← sq]
  have : b ^ 2 = 1 := Subtype.ext (by simpa using hB2 _ (mem_subgroupOf.1 hb))
  rw [this, map_one]

omit [Finite G] in
theorem map_le_hexadAut {f : orb E t ≃ Fin 22} (hA : (rhoF f).range = hexadAut)
    (B : Subgroup G) : (B.subgroupOf (normalizer (E : Set G))).map (rhoF f) ≤ hexadAut :=
  hA ▸ map_le_range _ _

section Bounds

variable
    (hR : ToddRankBounds) (H : Hyp t L E p) {f : orb E t ≃ Fin 22}
  (hA : (rhoF f).range = hexadAut)
include hR H hA

theorem Hyp.card_le_of_not_le_M22
    {B : Subgroup G} (hBN : B ≤ normalizer (E : Set G))
    (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hout : ¬ (B.subgroupOf (normalizer (E : Set G))).map (rhoF f) ≤ M22) :
    Nat.card B ≤ 2 ^ 8 :=
  (H.card_le_mul_card_fixed f (hA ▸ M22_le_hexadAut) hBN hB2 (map_le_hexadAut hA B)).trans
    (hR.1 _ _ (mul_self_of_mem_map hB2) hout)

theorem Hyp.card_le_of_le_M22
    {B : Subgroup G} (hBN : B ≤ normalizer (E : Set G))
    (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hin : (B.subgroupOf (normalizer (E : Set G))).map (rhoF f) ≤ M22)
    (hne : (B.subgroupOf (normalizer (E : Set G))).map (rhoF f) ≠ ⊥) :
    Nat.card B ≤ 2 ^ 9 :=
  (H.card_le_mul_card_fixed f (hA ▸ M22_le_hexadAut) hBN hB2 (map_le_hexadAut hA B)).trans
    (hR.2 _ _ (mul_self_of_mem_map hB2) hin hne)

theorem Hyp.conj_eq_of_hexadAut
    {g : G} (hg : conjSubgroup E g ≤ normalizer (E : Set G)) :
    conjSubgroup E g = E := by
  have hB2 := SolomonWong.conjSubgroup_sq H.todd.E_sq g
  have hcard : Nat.card (conjSubgroup E g) = 2 ^ 10 := by
    rw [SolomonWong.card_conjSubgroup, H.todd.card_E]
  by_cases hin : ((conjSubgroup E g).subgroupOf (normalizer (E : Set G))).map (rhoF f) ≤ M22
  · by_cases hne : ((conjSubgroup E g).subgroupOf (normalizer (E : Set G))).map (rhoF f) = ⊥
    · have hBE : conjSubgroup E g ≤ E := fun b hb => by
        have hb' : (⟨b, hg hb⟩ : normalizer (E : Set G)) ∈ (rhoF f).ker := by
          rw [MonoidHom.mem_ker]
          have h1 : rhoF f ⟨b, hg hb⟩ ∈ ((conjSubgroup E g).subgroupOf
              (normalizer (E : Set G))).map (rhoF f) := ⟨⟨b, hg hb⟩, mem_subgroupOf.2 hb, rfl⟩
          rw [hne] at h1
          exact h1
        rw [H.ker_rhoF f (hA ▸ M22_le_hexadAut)] at hb'
        exact mem_subgroupOf.1 hb'
      exact eq_of_le_of_card_ge hBE (by rw [hcard, H.todd.card_E])
    · have := H.card_le_of_le_M22 hR hA hg hB2 hin hne
      omega
  · have := H.card_le_of_not_le_M22 hR hA hg hB2 hin
    omega

omit hR in
theorem Hyp.comap_le_of_relIndex
    {M₁ : Subgroup G} (hM₁ : M₁.relIndex (normalizer (E : Set G)) = 2)
    (hEM₁ : E ≤ M₁) : M22.comap (rhoF f) ≤ M₁.subgroupOf (normalizer (E : Set G)) := by
  set K := M₁.subgroupOf (normalizer (E : Set G))
  have hker : (rhoF f).ker ≤ K := by
    rw [H.ker_rhoF f (hA ▸ M22_le_hexadAut)]
    exact fun n hn => mem_subgroupOf.2 (hEM₁ (mem_subgroupOf.1 hn))
  have hidx : (K.map (rhoF f).rangeRestrict).index = 2 := by
    rw [index_map_eq _ (rhoF f).rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])]
    exact hM₁
  have hcard : Nat.card (K.map (rhoF f)) = 443520 := by
    have h1 := (K.map (rhoF f).rangeRestrict).card_mul_index
    rw [hidx, show Nat.card (rhoF f).range = 887040 by rw [hA]; exact card_hexadAut.1] at h1
    have h2 : K.map (rhoF f) = (K.map (rhoF f).rangeRestrict).map (rhoF f).range.subtype := by
      rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
    rw [h2, card_map_of_injective (rhoF f).range.subtype_injective]
    omega
  have hKM : K.map (rhoF f) = M22 :=
    eq_M22_of_le_hexadAut (hA ▸ map_le_range _ _) hcard
  rw [← hKM, comap_map_eq_self hker]


end Bounds

theorem Hyp.rhoF_range_ne_hexadAut
    (hR : ToddRankBounds) (H : Hyp t L E p)
    (f : orb E t ≃ Fin 22) : (rhoF f).range ≠ hexadAut := by
  intro hA
  set N := normalizer (E : Set G)
  set M₁ : Subgroup G := (M22.comap (rhoF f)).map N.subtype
  have hidx : M₁.relIndex N = 2 := by
    change (M₁.comap N.subtype).index = 2
    rw [comap_map_eq_self_of_injective N.subtype_injective, index_comap, hA]
    exact card_hexadAut.2
  refine SolomonWong.relIndex_ne_two_of_rank H.index_ne_two H.todd.E_sq
    (fun g hg => ⟨1, one_mem _, by rw [H.conj_eq_of_hexadAut hR hA hg, conjSubgroup_one]⟩)
    (fun M₁' _ hidx' hEM₁' B hBN hB2 hnle => ?_) (map_subtype_le _) hidx
  rw [H.todd.card_E]
  have hout : ¬ (B.subgroupOf N).map (rhoF f) ≤ M22 := by
    intro hin
    refine hnle fun b hb => ?_
    have h1 : (⟨b, hBN hb⟩ : N) ∈ M22.comap (rhoF f) := hin ⟨⟨b, hBN hb⟩, mem_subgroupOf.2 hb, rfl⟩
    exact mem_subgroupOf.1 (H.comap_le_of_relIndex hA hidx' hEM₁' h1)
  have := H.card_le_of_not_le_M22 hR hA hBN hB2 hout
  omega

end CFSG.EvenSmallLie.UnitarySix.Hunt

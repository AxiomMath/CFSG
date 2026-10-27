module

public import CFSG.GH74.Uniqueness.SU.SU8Syl

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU4
  CFSG.GH74.Uniqueness.SU.SU8.Setup CFSG.GH74.Uniqueness.SU.SU8.Burn

section Count

variable {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}

theorem Out203.card_Q (o : Out203 z S L A) (hyp : Hyp20A z S L A) {T : Subgroup G}
    (hT : IsSylowIn ⊤ T) (hAT : A ≤ T)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ T → g⁻¹ * a * g ∈ A)
    (hTQ : Nat.card T = 4 * Nat.card ↥(T ⊓ centralizerBar (Hz z) L)) :
    Nat.card ↥(T ⊓ centralizerBar (Hz z) L) = 2 := by
  set Q : Subgroup G := T ⊓ centralizerBar (Hz z) L with hQ
  have hTH : T ≤ Hz z := o.syl_le_H hT hAT hcl hyp
  have hTI := hyp.Q_tame' (sylowIn_of_le hT hTH le_top)
  have hz : z ∈ A ⊓ centralizerBar (Hz z) L := hyp.z_mem
  have hzQ : z ∈ Q := ⟨hAT hz.1, hz.2⟩
  have hz1 : z ≠ 1 := hyp.z_ne_one
  have hcent : ∀ s ∈ T, ∀ a ∈ A, s * a = a * s := fun s hs a ha =>
    mul_inv_eq_iff_eq_mul.mp (o.syl_centralizes hT hAT hcl s hs a ha)
  have hex : ∀ a : {a : ↥A // a ≠ 1}, ∃ x ∈ normalizer (T : Set G), x * z * x⁻¹ = (a.1 : G) := by
    intro a
    obtain ⟨g, -, hg⟩ := o.trans z hz.1 hz1 (a.1 : G) a.1.2
      (fun h => a.2 (Subtype.ext h))
    exact exists_normalizer_conj_of_central hT (hcent · · z hz.1) (hcent · · a.1 a.1.2) hg
  choose x hxN hxz using hex
  have hxA : ∀ a, x a ∈ normalizer (A : Set G) := fun a =>
    normalizer_le_of_strongly_closed hAT hcl (hxN a)
  have hdisj : ∀ a b : {a : ↥A // a ≠ 1}, a ≠ b → ∀ w ∈ conjSub (x a) Q,
      w ∈ conjSub (x b) Q → w = 1 := by
    intro a b hab w hwa hwb
    obtain ⟨q, hq, rfl⟩ := mem_conjSub.mp hwa
    obtain ⟨q', hq', hqq⟩ := mem_conjSub.mp hwb
    by_cases hyL : (x a)⁻¹ * x b ∈ normalizer (L : Set G)
    · exfalso
      have hyA : (x a)⁻¹ * x b ∈ normalizer (A : Set G) :=
        (normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem (hxA a)) (hxA b)
      have hfix := o.fixes_z hyp hyA hyL
      apply hab
      apply Subtype.ext
      apply Subtype.ext
      rw [← hxz a, ← hxz b]
      calc x a * z * (x a)⁻¹ = x a * ((x a)⁻¹ * x b * z * ((x a)⁻¹ * x b)⁻¹) * (x a)⁻¹ := by
            rw [hfix]
        _ = x b * z * (x b)⁻¹ := by group
    · have hqy : q ∈ conjSub ((x a)⁻¹ * x b) Q := by
        refine mem_conjSub.mpr ⟨q', hq', ?_⟩
        calc (x a)⁻¹ * x b * q' * ((x a)⁻¹ * x b)⁻¹
            = (x a)⁻¹ * (x b * q' * (x b)⁻¹) * x a := by group
          _ = q := by rw [hqq]; group
      have hmem : q ∈ Q ⊓ conjSub ((x a)⁻¹ * x b) Q := ⟨hq, hqy⟩
      have hTI' := hTI _ hyL
      rw [hQ] at hmem
      rw [hTI'] at hmem
      have : q = 1 := (Subgroup.mem_bot).mp hmem
      rw [this]; group
  have hcard := card_le_of_disjoint_conj (S := T) (Q := Q) x hxN inf_le_left hdisj
  have h7 : Nat.card {a : ↥A // a ≠ 1} = 7 := by
    rw [card_subtype_ne_one, o.card_A]
  rw [h7, hTQ] at hcard
  have hq2 : 2 ≤ Nat.card Q := by
    have : 1 < Nat.card Q := (Subgroup.one_lt_card_iff_ne_bot Q).2 (fun h => hz1 (by
      have := hzQ; rw [h] at this; exact (Subgroup.mem_bot).mp this))
    omega
  omega

end Count

end CFSG.GH74.Uniqueness.SU.SU8

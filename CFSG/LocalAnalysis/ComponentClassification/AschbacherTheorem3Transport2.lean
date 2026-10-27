module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineQuotient

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise

variable {X : Type} [Group X]

theorem relativeWeakClosure_le_iff {G T S M : Subgroup X} :
    relativeWeakClosure G T S ≤ M ↔
      ∀ g ∈ G, rightConjugate T g ≤ S → rightConjugate T g ≤ M := by
  constructor
  · intro h g hg hle
    exact (rightConjugate_le_relativeWeakClosure hg hle).trans h
  · intro h
    refine iSup_le fun c => iSup_le fun hc => ?_
    have heq : conjugateSubgroup (c : X) T = rightConjugate T (c : X)⁻¹ := by
      rw [rightConjugate, inv_inv]
    rw [heq] at hc ⊢
    exact h _ (G.inv_mem c.2) hc

variable [Finite X]

theorem exists_rightConjugate_le_of_map_le {N : Subgroup X} [N.Normal] (hodd : Odd (Nat.card N))
    {P S : Subgroup X} (hP : IsPGroup 2 P) (hS : IsPGroup 2 S)
    (hle : P.map (QuotientGroup.mk' N) ≤ S.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, rightConjugate P n ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N
  have hinj : ∀ {R : Subgroup X}, IsPGroup 2 R → ∀ x ∈ R, π x = 1 → x = 1 := by
    intro R hR x hx h1
    obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
    exact eq_one_of_two_pow_of_odd ((QuotientGroup.eq_one_iff x).mp h1) hodd
      (congrArg Subtype.val hk)
  have hPN : P ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (hinj hP x hx.1 ((QuotientGroup.eq_one_iff x).mpr hx.2))
  have hsyl := isSylowOf_sup_odd hP hodd hPN
  set P₂ := S ⊓ (P ⊔ N) with hP₂
  have hP₂2 : IsPGroup 2 P₂ := hS.to_inf_left
  obtain ⟨c, hcL, hcle⟩ := exists_rightConjugate_le_of_isSylowOf hsyl hP₂2 inf_le_right
  have hmap : P.map π ≤ P₂.map π := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨s, hs, hsp⟩ := hle (Subgroup.mem_map_of_mem π hp)
    have hps : p⁻¹ * s ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (π p)⁻¹ * π s = 1
      rw [hsp, inv_mul_cancel]
    have hsL : s ∈ P ⊔ N := by
      have : s = p * (p⁻¹ * s) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hps)
    exact ⟨s, ⟨hs, hsL⟩, hsp⟩
  have hcard : Nat.card P ≤ Nat.card P₂ :=
    calc Nat.card P = Nat.card (P.map π) := (card_map_eq_of_ker π (hinj hP)).symm
      _ ≤ Nat.card (P₂.map π) := Subgroup.card_le_of_le hmap
      _ ≤ Nat.card P₂ := Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have heq : rightConjugate P₂ c = P :=
    Subgroup.eq_of_le_of_card_ge hcle (by rw [rightConjugate_card]; exact hcard)
  have hP₂eq : rightConjugate P c⁻¹ = P₂ := by
    rw [← heq, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hc' : c⁻¹ ∈ (P : Set X) * (N : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right P N
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)]
    exact (P ⊔ N).inv_mem hcL
  obtain ⟨p, hp, n, hn, hpn⟩ := Set.mem_mul.mp hc'
  refine ⟨n, hn, ?_⟩
  have hpP : rightConjugate P p = P :=
    (rightConjugate_eq_self_iff P p).mpr (Subgroup.le_normalizer hp)
  calc rightConjugate P n = rightConjugate (rightConjugate P p) n := by rw [hpP]
    _ = rightConjugate P c⁻¹ := by rw [rightConjugate_mul, hpn]
    _ = P₂ := hP₂eq
    _ ≤ S := inf_le_left

theorem relativeWeakClosure_map_odd {G T S N : Subgroup X} [N.Normal] (hT : IsPGroup 2 T)
    (hS : IsPGroup 2 S) (hNG : N ≤ G) (hodd : Odd (Nat.card N)) :
    relativeWeakClosure (G.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N))
        (S.map (QuotientGroup.mk' N)) =
      (relativeWeakClosure G T S).map (QuotientGroup.mk' N) := by
  set π := QuotientGroup.mk' N
  apply le_antisymm
  · rw [relativeWeakClosure_le_iff]
    rintro _ ⟨x, hx, rfl⟩ hle
    rw [← map_rightConjugate] at hle
    have hTx : IsPGroup 2 (rightConjugate T x) := hT.map _
    obtain ⟨n, hn, hnS⟩ := exists_rightConjugate_le_of_map_le hodd hTx hS hle
    rw [rightConjugate_mul] at hnS
    have h1 := rightConjugate_le_relativeWeakClosure (G.mul_mem hx (hNG hn)) hnS
    have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    calc rightConjugate (T.map π) (π x) = (rightConjugate T (x * n)).map π := by
          rw [map_rightConjugate, map_mul, hπn, mul_one]
      _ ≤ (relativeWeakClosure G T S).map π := Subgroup.map_mono h1
  · rw [Subgroup.map_le_iff_le_comap, relativeWeakClosure_le_iff]
    intro g hg hle
    rw [← Subgroup.map_le_iff_le_comap, map_rightConjugate]
    refine rightConjugate_le_relativeWeakClosure (Subgroup.mem_map_of_mem π hg) ?_
    rw [← map_rightConjugate]
    exact Subgroup.map_mono hle

end CFSG.ComponentClassification.AschbacherTheorem3

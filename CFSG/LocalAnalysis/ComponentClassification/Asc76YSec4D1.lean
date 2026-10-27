module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Quot

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_normalizer_of_odd (hΩ : Assumption41 Ω) {K Y : Subgroup G} (hK : K ∈ Ω)
    (hY : Odd (Nat.card Y)) (hKY : K ≤ normalizer (Y : Set G)) :
    Y ≤ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
  obtain ⟨E, hER, hE2, hE4⟩ := Assumption41.exists_fourGroup hΩ hK hR
  exact le_of_fourGroup hE2 hE4 hY ((hER.trans hR.le).trans hKY) fun e he he1 =>
    inf_le_right.trans (Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hK)
      (hR.le (hER he)) he1 (hE2 e he))

theorem oddCoreIn_le_normalizer_of_le (hΩ : Assumption41 Ω) {K X : Subgroup G} (hK : K ∈ Ω)
    (hKX : K ≤ X) : oddCoreIn X ≤ normalizer (K : Set G) :=
  le_normalizer_of_odd hΩ hK (odd_card_oddCoreIn X) (hKX.trans (le_normalizer_oddCoreIn X))

omit [Finite G] in
theorem exists_mul_pow_eq {K : Subgroup G} {o : G} (ho : o ∈ normalizer (K : Set G)) {k : G}
    (hk : k ∈ K) (m : ℕ) : ∃ k' ∈ K, (k * o) ^ m = k' * o ^ m := by
  induction m with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨k', hk', h⟩ := ih
    refine ⟨k' * (o ^ m * k * (o ^ m)⁻¹), K.mul_mem hk' ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (pow_mem ho m) k).mp hk
    · rw [pow_succ, h]
      group

theorem sec4W_mul_comm (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {a b : G}
    (ha : a ∈ sec4W Ω S) (hb : b ∈ sec4W Ω S) : a * b = b * a :=
  congrArg Subtype.val ((isMulCommutative_sec4W hΩ hS.isPGroup).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

omit [Finite G] in
theorem conj_mem_sup_of_mem_normalizer_imgOf {X K : Subgroup G} (hKX : K ≤ X) {x : G}
    (hxX : x ∈ X)
    (hx : QuotientGroup.mk' (CFSG.Assembly.oddCore X) ⟨x, hxX⟩ ∈
      normalizer ((imgOf X K : Subgroup (X ⧸ CFSG.Assembly.oddCore X)) : Set _)) :
    ∀ k ∈ K, x * k * x⁻¹ ∈ K ⊔ oddCoreIn X := by
  intro k hk
  have hkX := hKX hk
  have h1 : QuotientGroup.mk' (CFSG.Assembly.oddCore X) ⟨x, hxX⟩ *
      QuotientGroup.mk' (CFSG.Assembly.oddCore X) ⟨k, hkX⟩ *
      (QuotientGroup.mk' (CFSG.Assembly.oddCore X) ⟨x, hxX⟩)⁻¹ ∈ imgOf X K :=
    (mem_normalizer_iff.mp hx _).mp (mem_map.mpr ⟨⟨k, hkX⟩, hk, rfl⟩)
  obtain ⟨k', hk', heq⟩ := mem_map.mp h1
  rw [← map_inv, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at heq
  have hk'K : (k' : G) ∈ K := hk'
  have hdecomp : x * k * x⁻¹ = (k' : G) *
      ((k'⁻¹ * (⟨x, hxX⟩ * ⟨k, hkX⟩ * ⟨x, hxX⟩⁻¹) : X) : G) := by
    simp only [coe_mul, coe_inv]
    group
  rw [hdecomp]
  exact mul_mem (mem_sup_left hk'K) (mem_sup_right ⟨_, heq, rfl⟩)

end CFSG.ComponentClassification.Asc76.Sec4

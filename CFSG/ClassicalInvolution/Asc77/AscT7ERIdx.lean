module

public import CFSG.ClassicalInvolution.Asc77.AscT7ERMain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7ER

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem sup_le_normalizer (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) :
    R ⊔ R' ≤ Subgroup.normalizer (R : Set G) := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hs.hne.symm hz hz'
    hRsyl.1 hR'syl.1 (S.isPGroup'.to_le (sup_le hyp.hR.2.2 hyp.hR'.2.2))
  refine sup_le Subgroup.le_normalizer ?_
  intro x hx
  refine Subgroup.mem_normalizer_fintype (fun n hn => ?_)
  have h1 : n * x = x * n := hc n hn x hx
  have hxn : x * n * x⁻¹ = n := by
    calc x * n * x⁻¹ = n * x * x⁻¹ := by rw [h1]
      _ = n := by group
  rw [hxn]
  exact hn

theorem ne_of_hyp25 (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) : R ≠ R' := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  intro h
  have h1 := hΩ.card_le_two_of_le_inf hK hK' hs.hne.symm hRsyl.2.1 hRsyl.1
    (h ▸ hyp.hR'.2.1)
  have h2 := (hΩ.isQuatSub_of_mem_RSet hp hyp.hR.1).eight_le
  omega

theorem card_eq_two_mul_normalizer [IsSimpleGroup G]
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) :
    Nat.card ↥(S : Subgroup G) =
      2 * Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hRR' : R ≠ R' := ne_of_hyp25 hyp
  obtain ⟨t', ht'S, -, hconj⟩ := c25_2_t_proved p f G Ω K K' W S R R' z t u₁ u₂ hyp
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := hyp.hR'.2.2
  have hperm : ∀ B ∈ (S : Subgroup G), conjSub B R = R ∨ conjSub B R = R' := by
    intro B hB
    have hmem : conjSub B R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR.1 B
    have hle : conjSub B R ≤ (S : Subgroup G) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 : B * (B⁻¹ * x * B) * B⁻¹ ∈ (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hB (hRS hx)) (Subgroup.inv_mem _ hB)
      simpa [mul_assoc] using h1
    exact hyp.hRS _ hmem hle
  have hperm' : ∀ B ∈ (S : Subgroup G), conjSub B R' = R ∨ conjSub B R' = R' := by
    intro B hB
    have hmem : conjSub B R' ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR'.1 B
    have hle : conjSub B R' ≤ (S : Subgroup G) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 : B * (B⁻¹ * x * B) * B⁻¹ ∈ (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hB (hR'S hx)) (Subgroup.inv_mem _ hB)
      simpa [mul_assoc] using h1
    exact hyp.hRS _ hmem hle
  have hidx : (Subgroup.normalizer (R : Set G)).relIndex (S : Subgroup G) = 2 := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t', ht'S⟩, fun b => ?_⟩
    have hbS : (b : G) ∈ (S : Subgroup G) := b.2
    have hmemb : b ∈ (Subgroup.normalizer (R : Set G)).subgroupOf (S : Subgroup G) ↔
        conjSub (b : G) R = R := by
      rw [Subgroup.mem_subgroupOf]
      exact mem_normalizer_iff_conjSub_eq
    have hmemba : b * ⟨t', ht'S⟩ ∈ (Subgroup.normalizer (R : Set G)).subgroupOf (S : Subgroup G) ↔
        conjSub (b : G) R' = R := by
      rw [Subgroup.mem_subgroupOf, mem_normalizer_iff_conjSub_eq]
      show conjSub ((b : G) * t') R = R ↔ _
      rw [conjSub_mul, hconj]
    rw [hmemba, hmemb]
    rcases hperm _ hbS with h | h
    ·
      have hne : ¬ conjSub (b : G) R' = R := by
        intro h'
        exact hRR' (conjSub_injective (b : G) (h.trans h'.symm))
      simp [h, hne]
    · have hne : ¬ conjSub (b : G) R = R := by
        rw [h]; exact fun h' => hRR' h'.symm
      rcases hperm' _ hbS with h' | h'
      · simp [h', hne]
      · exact absurd (conjSub_injective (b : G) (h.trans h'.symm)) hRR'
  have hmul := Subgroup.relIndex_mul_card (Subgroup.normalizer (R : Set G)) (S : Subgroup G)
  rw [hidx, inf_comm] at hmul
  exact hmul.symm

end T7ER

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_17_norm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) ≤ 2 * Nat.card ↥(R ⊔ R')

theorem c25_17_idx_of_norm (h : C25_17_norm p f) : C25_17_idx p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  have hS := T7ER.card_eq_two_mul_normalizer hyp
  have hle : R ⊔ R' ≤ (S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) :=
    le_inf (sup_le hyp.hR.2.2 hyp.hR'.2.2) (T7ER.sup_le_normalizer hyp)
  have hbound := h G Ω K K' W S R R' z t u₁ u₂ hyp
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have hm2 : m ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(R ⊔ R') * m := by nlinarith
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) := Nat.card_pos
    omega
  have hm12 : m = 1 ∨ m = 2 := by omega
  rcases hm12 with rfl | rfl
  · left
    rw [hS, hm]
    ring
  · right
    rw [hS, hm]
    ring

theorem c25_17_norm_of_idx (h : C25_17_idx p f) : C25_17_norm p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  have hS := T7ER.card_eq_two_mul_normalizer hyp
  rcases h G Ω K K' W S R R' z t u₁ u₂ hyp with h2 | h4 <;> omega

end CFSG.ClassicalInvolution.Asc77

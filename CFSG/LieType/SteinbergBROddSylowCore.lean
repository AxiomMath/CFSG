module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LieType.SteinbergBR.OddSylow

open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type*} [Group G]

theorem normalizer_eq_of_one [Finite G] {p : ℕ} [Fact p.Prime] (P₀ : Sylow p G)
    (h : Subgroup.normalizer (P₀ : Set G) = P₀) (U : Sylow p G) :
    Subgroup.normalizer (U : Set G) = U := by
  have hidx : (Subgroup.normalizer (U : Set G)).index = (U : Subgroup G).index := by
    rw [← Sylow.card_eq_index_normalizer, Sylow.card_eq_index_normalizer P₀, h]
    have h1 := Subgroup.card_mul_index (P₀ : Subgroup G)
    have h2 := Subgroup.card_mul_index (U : Subgroup G)
    rw [Sylow.card_eq_multiplicity] at h1 h2
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos _) (h1.trans h2.symm)
  refine (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer ?_).symm
  have h1 := Subgroup.card_mul_index (Subgroup.normalizer (U : Set G))
  have h2 := Subgroup.card_mul_index (U : Subgroup G)
  rw [hidx] at h1
  have hpos : 0 < (U : Subgroup G).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact (Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)).le

theorem eq_one_of_odd_of_dvd_two_pow {m k : ℕ} (hm : Odd m) (hdvd : m ∣ 2 ^ k) : m = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hm.coprime_two_right) hdvd

theorem eq_one_of_odd [Finite G] (U : Sylow 2 G) (hN : Subgroup.normalizer (U : Set G) = U)
    (hOut : IsPGroup 2 (Outer G)) (α : MulAut G) (hα : Odd (orderOf α))
    (hαU : (U : Subgroup G).map α.toMonoidHom = U) : α = 1 := by
  have hinn : α ∈ inner G := by
    obtain ⟨k, hk⟩ := hOut (QuotientGroup.mk' (inner G) α)
    have hdvd : orderOf (QuotientGroup.mk' (inner G) α) ∣ orderOf α := orderOf_map_dvd _ α
    have h1 : orderOf (QuotientGroup.mk' (inner G) α) = 1 :=
      eq_one_of_odd_of_dvd_two_pow (hα.of_dvd_nat hdvd) (orderOf_dvd_of_pow_eq_one hk)
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨s, rfl⟩ := hinn
  have hN' : Subgroup.normalizer ((U : Subgroup G) : Set G) = U := hN
  have hs : s ∈ (U : Subgroup G) := by
    rw [← hN', Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hαU]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← hαU] at hh
      obtain ⟨h', hh', he⟩ := hh
      have : h' = h := by
        have he' : s * h' * s⁻¹ = s * h * s⁻¹ := he
        simpa using he'
      exact this ▸ hh'
  obtain ⟨k, hk⟩ := U.isPGroup' ⟨s, hs⟩
  have hsk : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : orderOf (MulAut.conj s) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hsk, map_one])
  exact orderOf_eq_one_iff.1 (eq_one_of_odd_of_dvd_two_pow hα hdvd)

theorem map_inner_congr {H : Type*} [Group H] (e : G ≃* H) :
    (inner G).map (MulAut.congr e).toMonoidHom = inner H := by
  ext f
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, (congr_conj e g).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨MulAut.conj (e.symm h), ⟨e.symm h, rfl⟩, by
      change MulAut.congr e (MulAut.conj (e.symm h)) = MulAut.conj h
      rw [congr_conj, MulEquiv.apply_symm_apply]⟩

theorem card_outer_congr {H : Type*} [Group H] (e : G ≃* H) :
    Nat.card (Outer G) = Nat.card (Outer H) :=
  Nat.card_congr (QuotientGroup.congr (inner G) (inner H) (MulAut.congr e)
    (map_inner_congr e)).toEquiv

theorem exists_selfNormalizing_of_equiv [Finite G] {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (e : G ≃* H) (P₀ : Sylow p H)
    (h : Subgroup.normalizer (P₀ : Set H) = P₀) :
    ∃ P : Sylow p G, Subgroup.normalizer (P : Set G) = P := by
  refine ⟨Sylow.ofCard ((P₀ : Subgroup H).map e.symm.toMonoidHom) ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
  · change Subgroup.normalizer ((P₀ : Subgroup H).map e.symm.toMonoidHom : Set G) =
      (P₀ : Subgroup H).map e.symm.toMonoidHom
    have h' : Subgroup.normalizer ((P₀ : Subgroup H) : Set H) = P₀ := h
    rw [← Subgroup.map_equiv_normalizer_eq, h']

end CFSG.LieType.SteinbergBR.OddSylow

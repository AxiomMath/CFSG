module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.Basic

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

variable {G : Type*} [Group G]

@[expose] def commHom (S J : Subgroup G) (hJc : ∀ a ∈ S, ∀ x ∈ J, a * x = x * a) (hJS : J ≤ S) (n : G)
    (h : ∀ s ∈ S, s * n * s⁻¹ * n⁻¹ ∈ J) : S →* G where
  toFun s := s.1 * n * s.1⁻¹ * n⁻¹
  map_one' := by simp
  map_mul' a b := by
    have hcb := h b.1 b.2
    have hca := h a.1 a.2
    have h1 : a.1 * (b.1 * n * b.1⁻¹ * n⁻¹) = (b.1 * n * b.1⁻¹ * n⁻¹) * a.1 :=
      hJc _ a.2 _ hcb
    have h2 : (b.1 * n * b.1⁻¹ * n⁻¹) * (a.1 * n * a.1⁻¹ * n⁻¹) =
        (a.1 * n * a.1⁻¹ * n⁻¹) * (b.1 * n * b.1⁻¹ * n⁻¹) := hJc _ (hJS hcb) _ hca
    show (a.1 * b.1) * n * (a.1 * b.1)⁻¹ * n⁻¹ = _
    calc (a.1 * b.1) * n * (a.1 * b.1)⁻¹ * n⁻¹
        = (a.1 * (b.1 * n * b.1⁻¹ * n⁻¹)) * a.1⁻¹ * (a.1 * n * a.1⁻¹ * n⁻¹) := by group
      _ = (b.1 * n * b.1⁻¹ * n⁻¹) * a.1 * a.1⁻¹ * (a.1 * n * a.1⁻¹ * n⁻¹) := by rw [h1]
      _ = (b.1 * n * b.1⁻¹ * n⁻¹) * (a.1 * n * a.1⁻¹ * n⁻¹) := by group
      _ = (a.1 * n * a.1⁻¹ * n⁻¹) * (b.1 * n * b.1⁻¹ * n⁻¹) := h2

theorem commHom_apply (S J : Subgroup G) (hJc : ∀ a ∈ S, ∀ x ∈ J, a * x = x * a) (hJS : J ≤ S)
    (n : G) (h : ∀ s ∈ S, s * n * s⁻¹ * n⁻¹ ∈ J) (s : S) :
    commHom S J hJc hJS n h s = s.1 * n * s.1⁻¹ * n⁻¹ := rfl

theorem commHom_range_le (S J : Subgroup G) (hJc : ∀ a ∈ S, ∀ x ∈ J, a * x = x * a)
    (hJS : J ≤ S) (n : G) (h : ∀ s ∈ S, s * n * s⁻¹ * n⁻¹ ∈ J) :
    (commHom S J hJc hJS n h).range ≤ J := by
  rintro _ ⟨s, rfl⟩
  exact h s.1 s.2

theorem card_commHom_ker (S J : Subgroup G) (hJc : ∀ a ∈ S, ∀ x ∈ J, a * x = x * a)
    (hJS : J ≤ S) (n : G) (h : ∀ s ∈ S, s * n * s⁻¹ * n⁻¹ ∈ J) :
    Nat.card (commHom S J hJc hJS n h).ker =
      Nat.card (S ⊓ Subgroup.centralizer {n} : Subgroup G) := by
  have hmap : (commHom S J hJc hJS n h).ker.map S.subtype =
      (S ⊓ Subgroup.centralizer {n} : Subgroup G) := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s.2, ?_⟩
      rw [commHom_apply] at hs
      have : s.1 * n = n * s.1 := by
                calc s.1 * n = s.1 * n * s.1⁻¹ * n⁻¹ * n * s.1 := by group
          _ = n * s.1 := by rw [hs]; group
      exact this.symm
    · rintro ⟨hxS, hx⟩
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      rw [commHom_apply]
      show x * n * x⁻¹ * n⁻¹ = 1
      rw [← hx]; group
  rw [← hmap]
  exact (Subgroup.card_map_of_injective S.subtype_injective).symm

theorem card_le_card_inf_centralizer_mul [Finite G] (S J : Subgroup G)
    (hJc : ∀ a ∈ S, ∀ x ∈ J, a * x = x * a) (hJS : J ≤ S) (n : G)
    (h : ∀ s ∈ S, s * n * s⁻¹ * n⁻¹ ∈ J) :
    Nat.card S ≤ Nat.card (S ⊓ Subgroup.centralizer {n} : Subgroup G) * Nat.card J := by
  set φ := commHom S J hJc hJS n h
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [card_commHom_ker S J hJc hJS n h] at h1
  rw [← h1]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (commHom_range_le S J hJc hJS n h))


theorem exists_commutator_eq [Finite G] (S J : Subgroup G)
    (hJc : ∀ a ∈ S, ∀ x ∈ J, a * x = x * a) (hJS : J ≤ S) (n : G)
    (h : ∀ s ∈ S, s * n * s⁻¹ * n⁻¹ ∈ J)
    (heq : Nat.card S = Nat.card (S ⊓ Subgroup.centralizer {n} : Subgroup G) * Nat.card J) :
    ∀ j ∈ J, ∃ s ∈ S, s * n * s⁻¹ * n⁻¹ = j := by
  set φ := commHom S J hJc hJS n h
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [card_commHom_ker S J hJc hJS n h] at h1
  have hpos : 0 < Nat.card (S ⊓ Subgroup.centralizer {n} : Subgroup G) := Nat.card_pos
  have hrange : Nat.card φ.range = Nat.card J := by
    have : Nat.card (S ⊓ Subgroup.centralizer {n} : Subgroup G) * Nat.card φ.range =
        Nat.card (S ⊓ Subgroup.centralizer {n} : Subgroup G) * Nat.card J := by
      rw [h1, heq]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hle := commHom_range_le S J hJc hJS n h
  have heq' : φ.range = J := Subgroup.eq_of_le_of_card_ge hle hrange.symm.le
  intro j hj
  rw [← heq'] at hj
  obtain ⟨s, hs⟩ := hj
  exact ⟨s.1, s.2, hs⟩

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

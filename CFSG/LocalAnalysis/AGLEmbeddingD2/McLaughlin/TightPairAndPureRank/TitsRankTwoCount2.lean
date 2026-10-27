module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TitsRankTwoCount

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

section Doset

variable {G : Type*} [Group G] [Finite G]

theorem card_doset_isPGroup' {p : ℕ} [Fact p.Prime] {B Q U : Subgroup G} (hU : IsPGroup p U)
    (hUB : U ≤ B) (hBQ : B ≤ Q) (g : G) (hg : ∀ b ∈ B, ∃ u ∈ U, ∃ b' ∈ B, b * g = u * g * b') :
    ∃ j : ℕ, Nat.card (((B : Set G) * {g} * (Q : Set G) : Set G)) = p ^ j * Nat.card Q := by
  have heq : ((B : Set G) * {g} * (Q : Set G) : Set G) = (U : Set G) * {g} * (Q : Set G) := by
    ext x
    simp only [Set.mem_mul, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨b, hb, g', hg', rfl⟩, q, hq, rfl⟩
      subst hg'
      obtain ⟨u, hu, b', hb', hub⟩ := hg b hb
      refine ⟨u * g', ⟨u, hu, g', rfl, rfl⟩, b' * q, Q.mul_mem (hBQ hb') hq, ?_⟩
      rw [← mul_assoc (u * g'), ← hub]
    · rintro ⟨_, ⟨u, hu, g', hg', rfl⟩, q, hq, rfl⟩
      exact ⟨u * g', ⟨u, hUB hu, g', hg', rfl⟩, q, hq, rfl⟩
  rw [heq]
  exact card_doset_isPGroup hU g

end Doset

section Tits

variable {G : Type*} [Group G] [Finite G] {B N : Subgroup G} [(cartan B N).Normal]
  {S : Set (WeylGroup B N)}

theorem card_parabolic_pair_eq (h : CFSG.GroupTheory.TitsSystem.IsBNPair B N S)
    {U : Subgroup G} (hU : IsPGroup 2 U) (hUB : U ≤ B)
    (hUN : ∀ g ∈ N, ∀ b ∈ B, ∃ u ∈ U, ∃ b' ∈ B, b * g = u * g * b')
    {a b : WeylGroup B N} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hbraid : a * b * a = b * a * b) (hPa : Nat.card (parabolic B N {a}) = 3 * Nat.card B)
    (hPb : Nat.card (parabolic B N {b}) = 3 * Nat.card B) :
    ∃ o : ℕ, Nat.card (parabolic B N {a, b}) = 3 * Nat.card B * (3 + 2 ^ o) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa := h.mul_self_eq_one ha
  have hbb := h.mul_self_eq_one hb
  have ha1 : a ≠ 1 := h.ne_one ha
  have hb1 : b ≠ 1 := h.ne_one hb
  obtain ⟨n1a, n1b, n1ba, n1ab, n1aba, nab, nba', nab', naaba, nbba, nbab, nbaba, nbaab, nbaaba,
    nabaaba⟩ := six_distinct haa hbb ha1 hb1 hab hbraid
  have hD : ∀ {u v : WeylGroup B N}, u ≠ v → Disjoint (dc B N u) (dc B N v) :=
    fun huv => h.pairwise_disjoint_dc huv
  have hJS : ({a, b} : Set (WeylGroup B N)) ⊆ S := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  set Q : Subgroup G := parabolic B N {a} with hQ
  have hQS := coe_parabolic_single h ha
  have hPbS := coe_parabolic_single h hb
  have hDB : Disjoint (B : Set G) (dc B N a) := by
    rw [← dc_one (B := B) (N := N)]; exact hD n1a
  have hDBb : Disjoint (B : Set G) (dc B N b) := by
    rw [← dc_one (B := B) (N := N)]; exact hD n1b
  have hcDb : Nat.card (dc B N b) = 2 * Nat.card B := by
    have h1 : Nat.card (parabolic B N {b}) = Nat.card ↥((B : Set G) ∪ dc B N b) := by
      rw [← hPbS]; rfl
    rw [card_union_of_disjoint hDBb] at h1
    have : Nat.card ↥(B : Set G) = Nat.card B := rfl
    omega
  obtain ⟨na, hna⟩ := QuotientGroup.mk_surjective a
  obtain ⟨nb, hnb⟩ := QuotientGroup.mk_surjective b
  have hnab : ((na * nb : N) : WeylGroup B N) = a * b := by rw [QuotientGroup.mk_mul, hna, hnb]
  have hnba : ((nb * na : N) : WeylGroup B N) = b * a := by rw [QuotientGroup.mk_mul, hna, hnb]
  have hJa : a ∈ Subgroup.closure ({a, b} : Set (WeylGroup B N)) := Subgroup.subset_closure (by simp)
  have hJb : b ∈ Subgroup.closure ({a, b} : Set (WeylGroup B N)) := Subgroup.subset_closure (by simp)
  set X₀ : Set G := dc B N 1 ∪ dc B N a with hX₀
  set X₁ : Set G := dc B N b ∪ dc B N (b * a) with hX₁
  set X₂ : Set G := dc B N (a * b) ∪ dc B N (a * b * a) with hX₂
  have hPJ : ((parabolic B N {a, b} : Subgroup G) : Set G) = X₀ ∪ X₁ ∪ X₂ := by
    ext x
    rw [SetLike.mem_coe, h.mem_parabolic_iff hJS]
    constructor
    · rintro ⟨w, hw, hx⟩
      rcases mem_six_of_mem_closure haa hbb hbraid hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl hx))
      · exact Or.inl (Or.inl (Or.inr hx))
      · exact Or.inl (Or.inr (Or.inl hx))
      · exact Or.inl (Or.inr (Or.inr hx))
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · rintro (((hx | hx) | (hx | hx)) | (hx | hx))
      · exact ⟨1, one_mem _, hx⟩
      · exact ⟨a, hJa, hx⟩
      · exact ⟨b, hJb, hx⟩
      · exact ⟨b * a, mul_mem hJb hJa, hx⟩
      · exact ⟨a * b, mul_mem hJa hJb, hx⟩
      · exact ⟨a * b * a, mul_mem (mul_mem hJa hJb) hJa, hx⟩
  have hd01 : Disjoint X₀ X₁ := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨hD n1b, hD n1ba⟩,
      Set.disjoint_union_right.2 ⟨hD nab, hD nba'⟩⟩
  have hd02 : Disjoint X₀ X₂ := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨hD n1ab, hD n1aba⟩,
      Set.disjoint_union_right.2 ⟨hD nab', hD naaba⟩⟩
  have hd12 : Disjoint X₁ X₂ := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨hD nbab, hD nbaba⟩,
      Set.disjoint_union_right.2 ⟨hD nbaab, hD nbaaba⟩⟩
  have hcard : Nat.card (parabolic B N {a, b}) = Nat.card X₀ + Nat.card X₁ + Nat.card X₂ := by
    have h1 : Nat.card (parabolic B N {a, b}) = Nat.card ↥(X₀ ∪ X₁ ∪ X₂) := by
      rw [← hPJ]; rfl
    rw [h1, card_union_of_disjoint (Set.disjoint_union_left.2 ⟨hd02, hd12⟩),
      card_union_of_disjoint hd01]
  have hX₀Q : Nat.card X₀ = Nat.card Q := by
    have : X₀ = (Q : Set G) := by rw [hX₀, hQS, dc_one]
    rw [this]; rfl
  obtain ⟨o₁, ho₁⟩ := card_doset_isPGroup' (p := 2) (Q := Q) hU hUB (h.le_parabolic (Set.singleton_subset_iff.2 ha)) (nb : G) (hUN _ nb.2)
  obtain ⟨o₂, ho₂⟩ := card_doset_isPGroup' (p := 2) (Q := Q) hU hUB (h.le_parabolic (Set.singleton_subset_iff.2 ha)) ((na * nb : N) : G) (hUN _ (na * nb).2)
  have hX1 := dc_union_eq_dcoset h ha hnb
  have hX2 := dc_union_eq_dcoset h ha hnab
  have hX₁c : Nat.card X₁ = 2 ^ o₁ * Nat.card Q := by
    rw [hX₁, hX1]; exact ho₁
  have hX₂c : Nat.card X₂ = 2 ^ o₂ * Nat.card Q := by
    rw [hX₂, hX2]; exact ho₂
  have hDba : dc B N (b * a) = (B : Set G) * {((nb * na : N) : G)} * (B : Set G) := by
    ext x
    rw [mem_dc_of_lift hnba, mem_dcoset_iff]
  obtain ⟨e, he⟩ := card_doset_isPGroup' (p := 2) (Q := B) hU hUB le_rfl ((nb * na : N) : G) (hUN _ (nb * na).2)
  rw [← hDba] at he
  have hlow : Nat.card (dc B N b) ≤ Nat.card (dc B N (b * a)) := by
    have hnaa : (na : G) ∈ dc B N a := by
      rw [mem_dc_of_lift hna]; exact ⟨1, B.one_mem, 1, B.one_mem, by simp⟩
    have hsub : (fun y : G => y * (na : G)) '' (dc B N b) ⊆ dc B N (b * a) := by
      rintro _ ⟨y, hy, rfl⟩
      exact dc_mul_dc_of_ne h hb ha hab.symm (Set.mul_mem_mul hy hnaa)
    simp only [Nat.card_coe_set_eq]
    calc (dc B N b).ncard = ((fun y : G => y * (na : G)) '' (dc B N b)).ncard :=
          (Set.ncard_image_of_injective _ (mul_left_injective (na : G))).symm
      _ ≤ (dc B N (b * a)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hX₁split : Nat.card X₁ = Nat.card (dc B N b) + Nat.card (dc B N (b * a)) :=
    card_union_of_disjoint (hD nbba)
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hBe : 2 ≤ 2 ^ e := by
    have h1 := hlow
    rw [hcDb, he] at h1
    exact Nat.le_of_mul_le_mul_right h1 hBpos
  have heq : 3 * 2 ^ o₁ = 2 + 2 ^ e := by
    have h1 : (3 * 2 ^ o₁) * Nat.card B = (2 + 2 ^ e) * Nat.card B := by
      calc (3 * 2 ^ o₁) * Nat.card B = 2 ^ o₁ * (3 * Nat.card B) := by ring
        _ = 2 ^ o₁ * Nat.card Q := by rw [hPa]
        _ = Nat.card X₁ := hX₁c.symm
        _ = Nat.card (dc B N b) + Nat.card (dc B N (b * a)) := hX₁split
        _ = 2 * Nat.card B + 2 ^ e * Nat.card B := by rw [hcDb, he]
        _ = (2 + 2 ^ e) * Nat.card B := by ring
    exact Nat.eq_of_mul_eq_mul_right hBpos h1
  have ho : 2 ^ o₁ = 2 := arith_pow_two heq hBe
  refine ⟨o₂, ?_⟩
  rw [hcard, hX₀Q, hX₁c, hX₂c, ho, hPa]
  ring

end Tits

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

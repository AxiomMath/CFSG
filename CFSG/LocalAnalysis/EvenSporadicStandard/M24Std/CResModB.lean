module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G}

theorem ncard_invariant (hF : SextetFacts L A) (S : Set G) (hSA : ∀ s ∈ S, s ∈ A ∧ s ≠ 1)
    (hS : ∀ n ∈ egNL L A, ∀ s ∈ S, n * s * n⁻¹ ∈ S) :
    S.ncard = 0 ∨ S.ncard = 18 ∨ S.ncard = 45 ∨ S.ncard = 63 := by
  obtain ⟨a₁, ha₁, a₂, ha₂, h1, h2, hcov, hdisj, c1, c2⟩ := hF.orbits
  have n1 : (egOrb L A a₁).ncard = 45 := by rw [← Nat.card_coe_set_eq]; exact c1
  have n2 : (egOrb L A a₂).ncard = 18 := by rw [← Nat.card_coe_set_eq]; exact c2
  have key : ∀ a : G, ∀ s ∈ S, s ∈ egOrb L A a → egOrb L A a ⊆ S := by
    intro a s hs hsO o ho
    obtain ⟨n, hn, rfl⟩ := hsO
    obtain ⟨m, hm, rfl⟩ := ho
    have h := hS (m * n⁻¹) (mul_mem hm (inv_mem hn)) _ hs
    have e : m * n⁻¹ * (n * a * n⁻¹) * (m * n⁻¹)⁻¹ = m * a * m⁻¹ := by group
    rwa [e] at h
  have hd : Disjoint (egOrb L A a₁) (egOrb L A a₂) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    obtain ⟨n, hn, rfl⟩ := hx1
    obtain ⟨m, hm, hmx⟩ := hx2
    apply hdisj
    refine ⟨m⁻¹ * n, mul_mem (inv_mem hm) hn, ?_⟩
    calc m⁻¹ * n * a₁ * (m⁻¹ * n)⁻¹ = m⁻¹ * (n * a₁ * n⁻¹) * m := by group
      _ = a₂ := by rw [← hmx]; group
  have hS1 : S ∩ egOrb L A a₁ = ∅ ∨ S ∩ egOrb L A a₁ = egOrb L A a₁ := by
    by_cases h : (S ∩ egOrb L A a₁).Nonempty
    · right
      obtain ⟨s, hs, hsO⟩ := h
      exact Set.Subset.antisymm Set.inter_subset_right
        (fun o ho => ⟨key a₁ s hs hsO ho, ho⟩)
    · left
      exact Set.not_nonempty_iff_eq_empty.1 h
  have hS2 : S ∩ egOrb L A a₂ = ∅ ∨ S ∩ egOrb L A a₂ = egOrb L A a₂ := by
    by_cases h : (S ∩ egOrb L A a₂).Nonempty
    · right
      obtain ⟨s, hs, hsO⟩ := h
      exact Set.Subset.antisymm Set.inter_subset_right
        (fun o ho => ⟨key a₂ s hs hsO ho, ho⟩)
    · left
      exact Set.not_nonempty_iff_eq_empty.1 h
  have hSeq : S = (S ∩ egOrb L A a₁) ∪ (S ∩ egOrb L A a₂) := by
    ext s
    constructor
    · intro hs
      rcases hcov s (hSA s hs).1 (hSA s hs).2 with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
    · rintro (h | h) <;> exact h.1
  have hdis : Disjoint (S ∩ egOrb L A a₁) (S ∩ egOrb L A a₂) :=
    hd.mono Set.inter_subset_right Set.inter_subset_right
  have hcard : S.ncard = (S ∩ egOrb L A a₁).ncard + (S ∩ egOrb L A a₂).ncard := by
    conv_lhs => rw [hSeq]
    exact Set.ncard_union_eq hdis
  rcases hS1 with h | h <;> rcases hS2 with h' | h' <;> simp [hcard, h, h', n1, n2]

theorem exists_rep_of_index_two {X : Type*} [Group X] {H : Subgroup X} (hH : H.index = 2) :
    ∃ n₀ : X, n₀ ∉ H ∧ n₀ * n₀ ∈ H ∧ ∀ g : X, g ∈ H ∨ g * n₀⁻¹ ∈ H := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hH
  have h1 : a ∉ H := by
    intro h
    have := ha 1
    simp only [one_mul, H.one_mem, h, xor_self] at this
  refine ⟨a, h1, ?_, fun g => ?_⟩
  · rcases ha a with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h h1
  · have := ha (g * a⁻¹)
    simp only [inv_mul_cancel_right] at this
    rcases this with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h

theorem irreducible_of_index_two (hF : SextetFacts L A) {H : Subgroup (egNL L A)}
    (hH : H.index = 2) {B : Subgroup G} (hBA : B ≤ A)
    (hB : ∀ n ∈ H, ∀ b ∈ B, (n : G) * b * (n : G)⁻¹ ∈ B) : B = ⊥ ∨ B = A := by
  obtain ⟨n₀, hn₀, hn₀2, hrep⟩ := exists_rep_of_index_two hH
  have hHn : H.Normal := Subgroup.normal_of_index_eq_two hH
  let B' : Subgroup G := B.map (MulAut.conj (n₀ : G)).toMonoidHom
  have hB'mem : ∀ x : G, x ∈ B' ↔ ∃ b ∈ B, (n₀ : G) * b * (n₀ : G)⁻¹ = x := by
    intro x
    simp [B', Subgroup.mem_map, MulAut.conj_apply]
  have hn₀A : ∀ a : G, a ∈ A → (n₀ : G) * a * (n₀ : G)⁻¹ ∈ A := fun a ha =>
    (mem_normalizer_iff.1 (mem_inf.1 n₀.2).1 a).1 ha
  have hB'A : B' ≤ A := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (hB'mem x).1 hx
    exact hn₀A b (hBA hb)
  have ha : ∀ h : egNL L A, h ∈ H → ∀ b ∈ B, (h : G) * b * (h : G)⁻¹ ∈ B := hB
  have hb : ∀ h : egNL L A, h ∈ H → ∀ b' ∈ B', (h : G) * b' * (h : G)⁻¹ ∈ B' := by
    intro h hh b' hb'
    obtain ⟨b, hbB, rfl⟩ := (hB'mem b').1 hb'
    have hm : n₀⁻¹ * h * n₀⁻¹⁻¹ ∈ H := hHn.conj_mem h hh n₀⁻¹
    have h1 := ha _ hm b hbB
    refine (hB'mem _).2 ⟨_, h1, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  have hc : ∀ b ∈ B, (n₀ : G) * b * (n₀ : G)⁻¹ ∈ B' := fun b hbB => (hB'mem _).2 ⟨b, hbB, rfl⟩
  have hd : ∀ b' ∈ B', (n₀ : G) * b' * (n₀ : G)⁻¹ ∈ B := by
    intro b' hb'
    obtain ⟨b, hbB, rfl⟩ := (hB'mem b').1 hb'
    have h1 := ha (n₀ * n₀) hn₀2 b hbB
    have e : (n₀ : G) * ((n₀ : G) * b * (n₀ : G)⁻¹) * (n₀ : G)⁻¹ =
        ((n₀ * n₀ : egNL L A) : G) * b * ((n₀ * n₀ : egNL L A) : G)⁻¹ := by
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    rw [e]
    exact h1
  have hinv : ∀ g : egNL L A, ∀ u ∈ (B : Set G) ∪ (B' : Set G),
      (g : G) * u * (g : G)⁻¹ ∈ (B : Set G) ∪ (B' : Set G) := by
    intro g u hu
    rcases hrep g with hg | hg
    · rcases hu with hu | hu
      · exact Or.inl (ha g hg u hu)
      · exact Or.inr (hb g hg u hu)
    · have e : (g : G) * u * (g : G)⁻¹ = ((g * n₀⁻¹ : egNL L A) : G) *
          ((n₀ : G) * u * (n₀ : G)⁻¹) * ((g * n₀⁻¹ : egNL L A) : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
        group
      rw [e]
      rcases hu with hu | hu
      · exact Or.inr (hb _ hg _ (hc u hu))
      · exact Or.inl (ha _ hg _ (hd u hu))
  set S : Set G := ((B : Set G) ∪ (B' : Set G)) \ {1} with hS
  have hSA : ∀ s ∈ S, s ∈ A ∧ s ≠ 1 := by
    rintro s ⟨hs | hs, hs1⟩
    · exact ⟨hBA hs, hs1⟩
    · exact ⟨hB'A hs, hs1⟩
  have hSinv : ∀ n ∈ egNL L A, ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
    rintro n hn s ⟨hs, hs1⟩
    refine ⟨hinv ⟨n, hn⟩ s hs, fun h1 => hs1 ?_⟩
    have : n * s * n⁻¹ = 1 := h1
    simpa using this
  have h4 := ncard_invariant hF S hSA hSinv
  have hA64 : Nat.card A = 2 ^ 6 := by rw [hF.card_A]; norm_num
  obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hA64 ▸ Subgroup.card_dvd_of_le hBA)
  have hB'card : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj (n₀ : G)).injective
  obtain ⟨m, hm6, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hA64 ▸ Subgroup.card_dvd_of_le ((inf_le_left : B ⊓ B' ≤ B).trans hBA))
  have c1 : (B : Set G).ncard = 2 ^ k := by rw [← Nat.card_coe_set_eq]; exact hk
  have c2 : (B' : Set G).ncard = 2 ^ k := by rw [← Nat.card_coe_set_eq]; exact hB'card.trans hk
  have c3 : ((B : Set G) ∩ (B' : Set G)).ncard = 2 ^ m := by
    rw [← Nat.card_coe_set_eq]
    exact hm
  have e1 := Set.ncard_union_add_ncard_inter (B : Set G) (B' : Set G)
  have hU1 : ((B : Set G) ∪ (B' : Set G)).ncard ≥ 2 ^ k := by
    rw [← c1]
    exact Set.ncard_le_ncard Set.subset_union_left (Set.toFinite _)
  have hSc : S.ncard = ((B : Set G) ∪ (B' : Set G)).ncard - 1 :=
    Set.ncard_sdiff_singleton_of_mem (Or.inl B.one_mem)
  rw [c1, c2, c3] at e1
  have hk' : k = 0 ∨ k = 6 := by
    rcases h4 with h | h | h | h <;> rw [hSc] at h <;>
      interval_cases k <;> interval_cases m <;> simp at e1 hU1 h ⊢ <;> omega
  rcases hk' with rfl | rfl
  · left
    exact Subgroup.eq_bot_of_card_eq B (by rw [hk]; rfl)
  · right
    exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hk, hA64])

end CFSG.EvenSporadicStandard.M24Std

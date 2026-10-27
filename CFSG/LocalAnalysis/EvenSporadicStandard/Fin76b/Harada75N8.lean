module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75F3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section NormalIndexTwo

theorem index_subgroupOf_eq_of_card_mul {S : Type} [Group S] [Finite S] {A M : Subgroup S}
    (k : ℕ) (hAM : A ≤ M) (hc : Nat.card M = k * Nat.card A) :
    (A.subgroupOf M).index = k := by
  have h1 : Nat.card (A.subgroupOf M) * (A.subgroupOf M).index = Nat.card M :=
    Subgroup.card_mul_index (A.subgroupOf M)
  have h2 : Nat.card (A.subgroupOf M) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  have hpos : 0 < Nat.card A := Nat.card_pos
  rw [h2, hc] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))

theorem subgroupOf_normal_of_normal {S : Type} [Group S] {N A : Subgroup S}
    (hAn : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A) : (A.subgroupOf N).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hAn (g : S) g.2 (n : S) hn⟩

theorem card_center_le_two_of_card_eight {G : Type} [Group G] [Finite G] (h8 : Nat.card G = 8)
    (hnc : ∃ a b : G, a * b ≠ b * a) : Nat.card (Subgroup.center G) ≤ 2 := by
  by_contra hlt
  have hlt' : 2 < Nat.card (Subgroup.center G) := not_le.mp hlt
  have hmul : Nat.card (Subgroup.center G) * (Subgroup.center G).index = 8 := by
    rw [← h8]
    exact Subgroup.card_mul_index (Subgroup.center G)
  have hidx : (Subgroup.center G).index ≤ 2 := by
    by_contra h3
    have h3' : 2 < (Subgroup.center G).index := not_le.mp h3
    nlinarith
  have : IsCyclic (G ⧸ Subgroup.center G) :=
    isCyclic_of_natCard_le_two (show Nat.card (G ⧸ Subgroup.center G) ≤ 2 from hidx)
  have hcomm : IsMulCommutative G :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center G)) (QuotientGroup.ker_mk' (Subgroup.center G)).le
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (hcomm.is_comm.comm a b)

theorem exists_noncomm_quotient_subgroupOf {S : Type} [Group S] {N A : Subgroup S}
    [(A.subgroupOf N).Normal] (hAn : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    (hnc : ∃ s ∈ N, ∃ t ∈ N, s * t * s⁻¹ * t⁻¹ ∉ A) :
    ∃ a b : ↥N ⧸ A.subgroupOf N, a * b ≠ b * a := by
  obtain ⟨s, hs, t, ht, hst⟩ := hnc
  refine ⟨QuotientGroup.mk (⟨s, hs⟩ : ↥N), QuotientGroup.mk (⟨t, ht⟩ : ↥N), fun h => hst ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at h
  dsimp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
  have hts : t * s ∈ N := N.mul_mem ht hs
  have h2 := hAn (t * s) hts _ h
  have hx : s * t * s⁻¹ * t⁻¹ = ((t * s) * ((s * t)⁻¹ * (t * s)) * (t * s)⁻¹)⁻¹ := by
    group
  rw [hx]
  exact A.inv_mem h2

theorem card_comap_center_le {S : Type} [Group S] [Finite S] {N A : Subgroup S}
    [(A.subgroupOf N).Normal] (hAN : A ≤ N) (hAn : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    (hNA : Nat.card N = 8 * Nat.card A)
    (hnc : ∃ s ∈ N, ∃ t ∈ N, s * t * s⁻¹ * t⁻¹ ∉ A) :
    Nat.card ((Subgroup.center (↥N ⧸ A.subgroupOf N)).comap
      (QuotientGroup.mk' (A.subgroupOf N))) ≤ 2 * Nat.card A := by
  have hQ : Nat.card (↥N ⧸ A.subgroupOf N) = 8 := by
    rw [← Subgroup.index_eq_card]
    exact index_subgroupOf_eq_of_card_mul 8 hAN hNA
  have hZ : Nat.card (Subgroup.center (↥N ⧸ A.subgroupOf N)) ≤ 2 :=
    card_center_le_two_of_card_eight hQ (exists_noncomm_quotient_subgroupOf hAn hnc)
  set Z := Subgroup.center (↥N ⧸ A.subgroupOf N) with hZdef
  set Zc := Z.comap (QuotientGroup.mk' (A.subgroupOf N)) with hZc
  have hkpos : 0 < Z.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have e1 : Nat.card Zc * Zc.index = Nat.card N := Subgroup.card_mul_index Zc
  have e2 : Zc.index = Z.index :=
    Subgroup.index_comap_of_surjective Z (QuotientGroup.mk'_surjective (A.subgroupOf N))
  have e3 : Nat.card Z * Z.index = 8 := (Subgroup.card_mul_index Z).trans hQ
  rw [e2, hNA] at e1
  have e4 : Nat.card Z * Nat.card A * Z.index = 8 * Nat.card A := by
    rw [mul_right_comm, e3]
  have e5 : Nat.card Zc * Z.index = Nat.card Z * Nat.card A * Z.index := by
    rw [e1, e4]
  have e6 : Nat.card Zc = Nat.card Z * Nat.card A := Nat.eq_of_mul_eq_mul_right hkpos e5
  rw [e6]
  exact Nat.mul_le_mul_right _ hZ

theorem inv_mul_conj_mem_of_card_two_mul {S : Type} [Group S] [Finite S] {N A M : Subgroup S}
    (hAn : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    (hMn : ∀ n ∈ N, ∀ x ∈ M, n * x * n⁻¹ ∈ M)
    (hAM : A ≤ M) (hc : Nat.card M = 2 * Nat.card A) :
    ∀ n ∈ N, ∀ x ∈ M, x⁻¹ * (n⁻¹ * x * n) ∈ A := by
  intro n hn x hx
  have hi : (A.subgroupOf M).index = 2 := index_subgroupOf_eq_of_card_mul 2 hAM hc
  by_cases hxA : x ∈ A
  · have h1 : n⁻¹ * x * n ∈ A := by
      simpa using hAn n⁻¹ (N.inv_mem hn) x hxA
    exact A.mul_mem (A.inv_mem hxA) h1
  · have hy : n⁻¹ * x * n ∈ M := by
      simpa using hMn n⁻¹ (N.inv_mem hn) x hx
    have hyA : n⁻¹ * x * n ∉ A := by
      intro h
      apply hxA
      have h2 := hAn n hn _ h
      have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
      rwa [e] at h2
    have key := inv_mul_mem_of_not_mem_of_index_le_two (P := ↥M) (C := A.subgroupOf M) hi.le
      (u := ⟨x, hx⟩) (v := ⟨n⁻¹ * x * n, hy⟩)
      (Subgroup.mem_subgroupOf.not.mpr hxA) (Subgroup.mem_subgroupOf.not.mpr hyA)
    have key' := Subgroup.mem_subgroupOf.mp key
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using key'

theorem subgroupOf_le_comap_center {S : Type} [Group S] {N A M : Subgroup S}
    [(A.subgroupOf N).Normal] (hcomm : ∀ n ∈ N, ∀ x ∈ M, x⁻¹ * (n⁻¹ * x * n) ∈ A) :
    M.subgroupOf N ≤ (Subgroup.center (↥N ⧸ A.subgroupOf N)).comap
      (QuotientGroup.mk' (A.subgroupOf N)) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro g
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective g
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have key : (((n * x)⁻¹ * (x * n) : ↥N) : S) = (x : S)⁻¹ * ((n : S)⁻¹ * (x : S) * (n : S)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [key]
  exact hcomm (n : S) n.2 (x : S) hx

end NormalIndexTwo

theorem eq_of_normal_index_two {S : Type} [Group S] [Finite S] {N A M₁ M₂ : Subgroup S}
    (hAN : A ≤ N) (hAn : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    (hNA : Nat.card N = 8 * Nat.card A)
    (hnc : ∃ s ∈ N, ∃ t ∈ N, s * t * s⁻¹ * t⁻¹ ∉ A)
    (hM₁A : A ≤ M₁) (hM₁N : M₁ ≤ N) (hM₁n : ∀ n ∈ N, ∀ x ∈ M₁, n * x * n⁻¹ ∈ M₁)
    (hM₁c : Nat.card M₁ = 2 * Nat.card A)
    (hM₂A : A ≤ M₂) (hM₂N : M₂ ≤ N) (hM₂n : ∀ n ∈ N, ∀ x ∈ M₂, n * x * n⁻¹ ∈ M₂)
    (hM₂c : Nat.card M₂ = 2 * Nat.card A) :
    M₁ = M₂ := by
  have : (A.subgroupOf N).Normal := subgroupOf_normal_of_normal hAn
  have hbound := card_comap_center_le hAN hAn hNA hnc
  have hM₁Zc := subgroupOf_le_comap_center
    (inv_mul_conj_mem_of_card_two_mul hAn hM₁n hM₁A hM₁c)
  have hM₂Zc := subgroupOf_le_comap_center
    (inv_mul_conj_mem_of_card_two_mul hAn hM₂n hM₂A hM₂c)
  have hM₁card : Nat.card (M₁.subgroupOf N) = 2 * Nat.card A := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM₁N).toEquiv, hM₁c]
  have hM₂card : Nat.card (M₂.subgroupOf N) = 2 * Nat.card A := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM₂N).toEquiv, hM₂c]
  have e₁ := Subgroup.eq_of_le_of_card_ge hM₁Zc (by omega)
  have e₂ := Subgroup.eq_of_le_of_card_ge hM₂Zc (by omega)
  have e : M₁.subgroupOf N = M₂.subgroupOf N := e₁.trans e₂.symm
  ext x
  constructor
  · intro hx
    have h : (⟨x, hM₁N hx⟩ : ↥N) ∈ M₁.subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
    rw [e] at h
    exact Subgroup.mem_subgroupOf.mp h
  · intro hx
    have h : (⟨x, hM₂N hx⟩ : ↥N) ∈ M₂.subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
    rw [← e] at h
    exact Subgroup.mem_subgroupOf.mp h

end CFSG.EvenSporadicStandard.Fin76b

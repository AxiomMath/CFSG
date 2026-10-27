module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmPBlk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open QuadraticMap (polarBilin)
open LinearMap (BilinForm)

section Count

variable {G : Type*} [Group G]

private theorem not_le_of_index_three {D E : Subgroup G} (hD : D.index = 3) (hE : E.index = 3)
    (hDE : D ≠ E) : ¬ E ≤ D := fun h => hDE (le_antisymm (Subgroup.relIndex_eq_one.1 (by
  have := Subgroup.relIndex_mul_index h
  rw [hD, hE] at this
  omega)) h)

private theorem card_inf_sup_zpowers [IsMulCommutative G] (hcard : Nat.card G = 3 ^ 3)
    {D E : Subgroup G} (hD : D.index = 3) (hE : E.index = 3) (hDE : D ≠ E) {t : G}
    (ht : t ^ 3 = 1) (htD : t ∉ D) : Nat.card ↥(D ⊓ E ⊔ Subgroup.zpowers t) = 3 ^ 2 := by
  have hEc : Nat.card E = 9 := by
    have := E.card_mul_index
    rw [hE, hcard] at this
    omega
  have hL : Nat.card ↥(D ⊓ E) = 3 := by
    have h1 := Subgroup.relIndex_mul_card D E
    have h2 : D.relIndex E = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (hD ▸ D.relIndex_dvd_index_of_normal E) with h | h
      · exact absurd (Subgroup.relIndex_eq_one.1 h) (not_le_of_index_three hD hE hDE)
      · exact h
    rw [h2, hEc] at h1
    omega
  have hZ : Nat.card ↥(Subgroup.zpowers t) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ht fun h1 => htD (by rw [h1]; exact D.one_mem)]
  have h3 : (D ⊓ E).relIndex (Subgroup.zpowers t) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1
        (hZ ▸ (D ⊓ E).relIndex_dvd_card (Subgroup.zpowers t)) with h | h
    · exact absurd ((Subgroup.relIndex_eq_one.1 h) (Subgroup.mem_zpowers t)) fun h' => htD h'.1
    · exact h
  have h4 := Subgroup.relIndex_mul_card (D ⊓ E) (D ⊓ E ⊔ Subgroup.zpowers t)
  rw [Subgroup.relIndex_sup_left, h3, inf_of_le_left le_sup_left, hL] at h4
  omega

end Count

private theorem exists_merge_elem {G : Type*} [Group G] {D E : Subgroup G} (hD : D.index = 3)
    (hE : E.index = 3) (hDE : D ≠ E) {d : G} (hd : d ∈ D ↔ d ∈ E) :
    ∃ t : G, t ∉ D ∧ t ∉ E ∧ d ∈ D ⊓ E ⊔ Subgroup.zpowers t := by
  by_cases hdD : d ∈ D
  · obtain ⟨a, haD, haE⟩ := SetLike.not_le_iff_exists.1 (not_le_of_index_three hE hD hDE.symm)
    obtain ⟨b, hbE, hbD⟩ := SetLike.not_le_iff_exists.1 (not_le_of_index_three hD hE hDE)
    refine ⟨a * b, fun h => hbD ?_, fun h => haE ?_,
      Subgroup.mem_sup_left ⟨hdD, hd.1 hdD⟩⟩
    · simpa using D.mul_mem (D.inv_mem haD) h
    · simpa using E.mul_mem h (E.inv_mem hbE)
  · exact ⟨d, hdD, fun h => hdD (hd.2 h), Subgroup.mem_sup_right (Subgroup.mem_zpowers d)⟩

theorem SG.exists_merged_block {F V : Type} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate)
    {X : Subgroup (V ≃ₗ[F] V)} (hXO : X ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hX : IsElemAbelian 3 X) (hcard : Nat.card X = 3 ^ 3) {d : V ≃ₗ[F] V} (hd : d ∈ X) :
    ∃ Y ≤ X, d ∈ Y ∧ Nat.card Y = 3 ^ 2 ∧ ∃ (U : Submodule F V), ∃ t ∈ Y,
      4 ≤ Module.finrank F U ∧ (BilinForm.restrict (polarBilin Q) U).Nondegenerate ∧
      (∀ u ∈ U, t u ∈ U) ∧ (∀ u ∈ U, t u = u → u = 0) ∧
      ∀ y ∈ Y, ∃ k : ℕ, ∀ u ∈ U, y u = (t ^ k) u := by
  have hpF : ((3 : ℕ) : F) ≠ 0 := fun h =>
    absurd ((CharP.cast_eq_zero_iff F 2 3).1 h) (by norm_num)
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : Fintype X := Fintype.ofFinite _
  haveI : IsMulCommutative ↥X := hX.1
  obtain ⟨D, E, hDE, hD, hE, hdDE⟩ := SG.exists_blockPair X hpF hX hcard ⟨d, hd⟩
  obtain ⟨hU4, hUnd, hUinv, hUfix, hUL⟩ := SG.blockPair_spec X hQ hXO hX hDE hD hE
  have hDE' : D.1 ≠ E.1 := fun h => hDE (Subtype.ext h)
  obtain ⟨t, htD, htE, hdY⟩ := exists_merge_elem D.2 E.2 hDE' hdDE
  refine ⟨(D.1 ⊓ E.1 ⊔ Subgroup.zpowers t).map X.subtype, Subgroup.map_subtype_le _,
    ⟨⟨d, hd⟩, hdY, rfl⟩, ?_, blockSpace X D.1 ⊔ blockSpace X E.1, (t : V ≃ₗ[F] V),
    ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t), rfl⟩, hU4, hUnd,
    fun u hu => by simpa using hUinv t 1 u hu, hUfix t htD htE, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact card_inf_sup_zpowers hcard D.2 E.2 hDE' (pow_eq_one X hX t) htD
  · rintro y ⟨y', hy', rfl⟩
    obtain ⟨l, hl, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy'
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1
      ((isOfFinOrder_of_finite t).mem_powers_iff_mem_zpowers.2 hz)
    refine ⟨k, fun u hu => ?_⟩
    change ((l * t ^ k : ↥X) : V ≃ₗ[F] V) u = _
    rw [Subgroup.coe_mul, Subgroup.coe_pow, LinearEquiv.mul_apply]
    exact hUL l hl _ (hUinv t k u hu)

end CFSG.LocalAnalysis.GLTheoremA.S265

end

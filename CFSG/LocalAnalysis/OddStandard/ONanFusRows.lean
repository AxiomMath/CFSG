module

public import CFSG.LocalAnalysis.OddStandard.ONanFusClasses

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

@[expose] def FusABC (_D : FusCtx G v1 v2 v3 s t) (i : Fin 7) : Prop :=
  _D.Fus i 0 ∨ _D.Fus i 1 ∨ _D.Fus i 2

theorem FusABC.of_fus {i j : Fin 7} (hij : D.Fus i j) (hj : D.FusABC j) : D.FusABC i := by
  rcases hj with h | h | h
  · exact Or.inl (hij.trans D h)
  · exact Or.inr (Or.inl (hij.trans D h))
  · exact Or.inr (Or.inr (hij.trans D h))

theorem fusABC_of_le_two {i k : Fin 7} (hk : k.val ≤ 2) (h : D.Fus i k) : D.FusABC i := by
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem fus_of_row {r j i : Fin 7}
    (hrow : ∀ k : Fin 7, maxTable r k = true → k.val ≤ 2 ∨ k = j) (h : ¬ D.FusABC i) :
    D.Fus i j := by
  obtain ⟨k, hk, hik⟩ := D.thompson_row r i
  rcases hrow k hk with hk' | rfl
  · exact absurd (D.fusABC_of_le_two hk' hik) h
  · exact hik

omit D in
theorem row0 : ∀ k : Fin 7, maxTable 0 k = true → k.val ≤ 2 ∨ k = 3 := by decide

omit D in
theorem row4 : ∀ k : Fin 7, maxTable 4 k = true → k.val ≤ 2 ∨ k = 6 := by decide

omit D in
theorem row5 : ∀ k : Fin 7, maxTable 5 k = true → k.val ≤ 2 ∨ k = 5 := by decide

theorem fus_E (h : ¬ D.FusABC 4) : D.Fus 4 3 ∧ D.Fus 4 5 ∧ D.Fus 4 6 :=
  ⟨D.fus_of_row row0 h, D.fus_of_row row5 h, D.fus_of_row row4 h⟩

theorem fus_D (h : ¬ D.FusABC 3) : D.Fus 3 5 ∧ D.Fus 3 6 :=
  ⟨D.fus_of_row row5 h, D.fus_of_row row4 h⟩

theorem fus_F (h : ¬ D.FusABC 5) : D.Fus 5 3 ∧ D.Fus 5 6 :=
  ⟨D.fus_of_row row0 h, D.fus_of_row row4 h⟩

theorem fus_G (h : ¬ D.FusABC 6) : D.Fus 6 3 ∧ D.Fus 6 5 :=
  ⟨D.fus_of_row row0 h, D.fus_of_row row5 h⟩

theorem orderOf_s : orderOf s = 2 ^ 4 := by
  rw [← Nat.card_zpowers, AlpEmb.card_R D.E D.hF]
  norm_num

theorem s_pow_eight : s ^ 2 ^ (4 - 1) = invRep v1 v2 v3 s t 0 := by
  have h16 := D.orderOf_s
  have hmem : s ^ 2 ^ (4 - 1) ∈ zpowers s := npow_mem_zpowers s _
  have hsq : s ^ 2 ^ (4 - 1) * s ^ 2 ^ (4 - 1) = 1 := by
    rw [← pow_add, show 2 ^ (4 - 1) + 2 ^ (4 - 1) = 2 ^ 4 by norm_num, ← h16,
      pow_orderOf_eq_one]
  have hne : s ^ 2 ^ (4 - 1) ≠ 1 := by
    intro h1
    have := orderOf_le_of_pow_eq_one (by norm_num) h1
    rw [h16] at this
    norm_num at this
  rcases AlpEmb.involution_zpowers_s D.E D.hF hmem hsq with h | h
  · exact absurd h hne
  · rw [h]
    rfl

theorem fus_A_BCE : D.Fus 0 1 ∨ D.Fus 0 2 ∨ D.Fus 0 4 := by
  have hcard : Nat.card (alpP v1 v2 v3 s t) =
      Nat.card (closure {g : G | g ∈ genQ v1 v2 s t}) * 2 ^ 4 := by
    rw [AlpEmb.card_alpP D.E, AlpEmb.card_Q D.E D.hF]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_mem_of_cyclic_complement D.noIdx D.not_two_dvd_index_P
    (by norm_num) D.orderOf_s hcard
  rw [D.s_pow_eight] at hg
  set u := g⁻¹ * invRep v1 v2 v3 s t 0 * g with hu
  have hu2 : u * u = 1 := by
    rw [hu]
    calc g⁻¹ * invRep v1 v2 v3 s t 0 * g * (g⁻¹ * invRep v1 v2 v3 s t 0 * g)
        = g⁻¹ * (invRep v1 v2 v3 s t 0 * invRep v1 v2 v3 s t 0) * g := by group
      _ = 1 := by rw [D.rep_sq 0]; group
  have hu1 : u ≠ 1 := by
    intro h
    apply D.rep_ne_one 0
    calc invRep v1 v2 v3 s t 0 = g * u * g⁻¹ := by rw [hu]; group
      _ = 1 := by rw [h]; group
  obtain ⟨j, hj, hju⟩ := AlpEmb.involutions_Q_alpP D.E D.hF hg hu2 hu1
  have hfus : D.Fus 0 j := D.inClass_fus (D.inClass_rep 0) hju g rfl
  rcases hj with rfl | rfl | rfl
  · exact Or.inl hfus
  · exact Or.inr (Or.inl hfus)
  · exact Or.inr (Or.inr hfus)

end FusCtx

end CFSG.OddStandard.ONanRec

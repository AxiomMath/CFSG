module

public import CFSG.ClassicalInvolution.Q3.TL3T16

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

theorem ncard_conjugatesOf_le_seven {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hE : CFSG.ClassicalInvolution.Q3.TC.Thin.E8Struct (⊤ : Subgroup X) E) {t : X} (htE : t ∈ E)
    (ht1 : t ≠ 1) : (conjugatesOf t).ncard ≤ 7 := by
  have hsub : conjugatesOf t ⊆ (E : Set X) \ {1} := by
    intro x hx
    have hx' : IsConj t x := hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx'
    rw [Set.mem_diff, Set.mem_singleton_iff, SetLike.mem_coe]
    refine ⟨hE.normal c (Subgroup.mem_top c) t htE, fun h => ht1 ?_⟩
    simpa using h
  have hEcard : (E : Set X).ncard = 8 :=
    (Nat.card_coe_set_eq (E : Set X)).symm.trans hE.card
  calc (conjugatesOf t).ncard ≤ ((E : Set X) \ {1}).ncard := Set.ncard_le_ncard hsub
    _ = (E : Set X).ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem (show (1 : X) ∈ (E : Set X) from E.one_mem)
    _ = 7 := by simp [hEcard]

theorem false_of_e8Struct {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hE : CFSG.ClassicalInvolution.Q3.TC.Thin.E8Struct (⊤ : Subgroup X) E) {t : X} (htE : t ∈ E)
    (ht1 : t ≠ 1) (h2 : ∀ g : X, g * t = t * g → ∃ k : ℕ, g ^ 2 ^ k = 1) : False := by
  have hidx : E.index = 168 := by
    rw [← Subgroup.relIndex_top_right]
    exact hE.index
  have hX : Nat.card X = 1344 := by
    have h := Subgroup.card_mul_index (H := E)
    rw [hE.card, hidx] at h
    omega
  have hC2 : IsPGroup 2 (Subgroup.centralizer {t}) := by
    intro g
    obtain ⟨k, hk⟩ := h2 (g : X) (Subgroup.mem_centralizer_iff.1 g.2 t (Set.mem_singleton t)).symm
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hC2
  have hmul := Subgroup.card_mul_index (H := Subgroup.centralizer {t})
  rw [hn, Subgroup.index_centralizer_eq_ncard t, hX] at hmul
  have hm := ncard_conjugatesOf_le_seven hE htE ht1
  have hn6 : n ≤ 6 := by
    by_contra hlt
    have h7 : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have h1344 : 2 ^ 7 ∣ 1344 := by
      rw [← hmul]
      exact Dvd.dvd.mul_right h7 _
    exact absurd h1344 (by decide)
  have h64 : 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
  have hprod := Nat.mul_le_mul h64 hm
  rw [hmul] at hprod
  norm_num at hprod

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

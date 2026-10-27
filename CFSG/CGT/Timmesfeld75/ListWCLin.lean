module

public import CFSG.CGT.Timmesfeld75.ListWCLinPSL
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem isConj_of_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {T : Subgroup G}
    (h : ∀ x ∈ T.map e.toMonoidHom, x ≠ 1 → ∀ y ∈ T.map e.toMonoidHom, y ≠ 1 → IsConj x y) :
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y := by
  intro x hx hx1 y hy hy1
  have hc := h (e x) ⟨x, hx, rfl⟩ (fun h1 => hx1 (e.injective (h1.trans (map_one e).symm)))
    (e y) ⟨y, hy, rfl⟩ (fun h1 => hy1 (e.injective (h1.trans (map_one e).symm)))
  simpa using MonoidHom.map_isConj e.symm.toMonoidHom hc

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])

theorem lin_wc {G : Type} [Group G] {m : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] (e : G ≃* StatedProj (StatedSL m K)) {T : Subgroup G} (hT : IsWC T)
    (hT1 : T ≠ ⊥) :
    Nat.card T = Nat.card K ^ (m - 1) ∧
    ((∃ c : Fin m → K, c ≠ 0 ∧ T.map e.toMonoidHom = transvImage m K (transvCenter m K c)) ∨
      (∃ a : Fin m → K, a ≠ 0 ∧ T.map e.toMonoidHom = transvImage m K (transvAxis m K a))) ∧
    (∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y) := by
  have hT' := hT.map_mulEquiv e
  have hT'1 : T.map e.toMonoidHom ≠ ⊥ := fun h =>
    hT1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h)
  obtain ⟨hcard, hid, hconj⟩ := psl_wc hm hT' hT'1
  exact ⟨by rw [← hcard, Subgroup.card_map_of_injective e.injective], hid,
    isConj_of_map_mulEquiv e hconj⟩

theorem nonempty_mulEquiv_psl_of_alt_eight {A : Type} [Group A]
    (e : A ≃* alternatingGroup (Fin 8)) :
    Nonempty (A ≃* StatedProj (StatedSL 4 (ZMod 2))) :=
  CFSG.GH74.Exceptional.nonempty_mulEquiv_statedProj_of_alternating_eight e

theorem alt8_wc {G : Type} [Group G] (e : G ≃* alternatingGroup (Fin 8)) {T : Subgroup G}
    (hT : IsWC T) (hT1 : T ≠ ⊥) :
    Nat.card T = 8 ∧ ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y := by
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl_of_alt_eight e
  obtain ⟨hcard, -, hconj⟩ := lin_wc (by norm_num : 3 ≤ 4) e' hT hT1
  refine ⟨?_, hconj⟩
  rw [hcard]
  simp

end CFSG.CGT.Timmesfeld75

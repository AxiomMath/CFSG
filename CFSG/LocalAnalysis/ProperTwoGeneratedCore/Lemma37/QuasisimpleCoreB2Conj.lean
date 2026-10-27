module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem exists_pow_not_mem_mul_self_mem {G : Type} [Group G] {R T : Subgroup G}
    (hR : IsPGroup 2 R) {r : G} (hr : r ∈ R) (hrT : r ∉ T) :
    ∃ n ∈ R, n ∉ T ∧ n * n ∈ T := by
  classical
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  have hex : ∃ j, r ^ 2 ^ j ∈ T := ⟨k, by
    have h1 : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [h1]
    exact T.one_mem⟩
  have hspec := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := fun h0 => hrT (by rw [h0, pow_zero, pow_one] at hspec; exact hspec)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨r ^ 2 ^ j, R.pow_mem hr _, Nat.find_min hex (by omega), ?_⟩
  rw [hj, pow_succ, pow_mul, pow_two] at hspec
  exact hspec

namespace PartC

variable {G : Type} [Group G] {T Q P : Subgroup G} {e u : G} (Z : Subgroup G) [Z.Normal]

theorem conj_eq_or_of_caseB2 (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {t w : G} (ht : t ∈ T)
    (hw : w ∈ T) : t * w * t⁻¹ = w ∨ t * w * t⁻¹ = w * e := by
  have h := hc.comm_map_of_caseB2 Z hT φ hZ (a := (t : G ⧸ Z)) (b := (w : G ⧸ Z)) ⟨t, ht, rfl⟩
    ⟨w, hw, rfl⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hZ] at h
  rcases h with h | h
  · left
    rw [inv_mul_eq_one] at h
    rw [h, mul_inv_cancel_right]
  · right
    rw [inv_mul_eq_iff_eq_mul] at h
    calc t * w * t⁻¹ = t * w * e * e * t⁻¹ := by rw [hc.mul_centralElt_mul_centralElt]
      _ = w * t * e * t⁻¹ := by rw [← h]
      _ = w * e := by rw [mul_assoc w t e, hc.commute_centralElt t]; group

theorem exists_conj_eq_of_caseB2 (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {n : G}
    (hnP : ∀ p ∈ P, n * p * n⁻¹ ∈ P) (hnn : n * n ∈ T) :
    ∃ w ∈ P, w * w = e ∧ (n * w * n⁻¹ = w ∨ n * w * n⁻¹ = w * e) := by
  have hne : n * e * n⁻¹ = e := hc.conj_centralElt n
  set a := n * u * n⁻¹ with ha
  have haP : a ∈ P := hnP u hc.self_mem
  have haa : a * a = e := by rw [ha, ← conj_mul_eq_mul_conj, hc.sq, hne]
  by_cases hau : a = u ∨ a = u * e
  · exact ⟨u, hc.self_mem, hc.sq, hau⟩
  push Not at hau
  have huu := hc.sq
  have hee := hc.centralElt_mul_self
  have hinv : u⁻¹ = u * e := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, huu, hee]
  have hw1 : u * a ≠ 1 := fun h => hau.2 (by rw [← hinv]; exact eq_inv_of_mul_eq_one_right h)
  have hwe : u * a ≠ e := fun h => hau.1 (by
    have h' : a = u⁻¹ * e := by rw [← h]; group
    rw [h', hinv, mul_assoc, hee, mul_one])
  have hwP : u * a ∈ P := P.mul_mem hc.self_mem haP
  refine ⟨u * a, hwP, quaternion_mul_self_of_ne φ hc.mem_right hc.order hwP hw1 hwe, ?_⟩
  have hanti := quaternion_anticomm φ hc.mem_right hc.order hc.self_mem haP huu haa hau.1 hau.2
  have hau' : a * u = u * a * e := by
    calc a * u = a * u * e * e := (hc.mul_centralElt_mul_centralElt _).symm
      _ = u * a * e := by rw [← hanti]
  have hna : n * a * n⁻¹ = n * n * u * (n * n)⁻¹ := by rw [ha]; group
  have hconj : n * (u * a) * n⁻¹ = a * (n * a * n⁻¹) := by rw [conj_mul_eq_mul_conj]
  rcases hc.conj_eq_or_of_caseB2 Z hT φ hZ hnn (hc.right_le hc.self_mem) with h | h <;>
    rw [hconj, hna, h]
  · right
    exact hau'
  · left
    rw [← mul_assoc, hau', hc.mul_centralElt_mul_centralElt]

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

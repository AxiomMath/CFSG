module

public import CFSG.LargeExtraspecial.DWSm77Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

section Comm

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem commute_mul_of_not_commute {a b c : G} (ha : a ∈ S.QG) (hb : b ∈ S.QG) (hc : c ∈ S.QG)
    (hac : a * c ≠ c * a) (hbc : b * c ≠ c * b) : a * b * c = c * (a * b) := by
  have h1 := (S.polar_cl_eq_one_iff ha hc).mpr hac
  have h2 := (S.polar_cl_eq_one_iff hb hc).mpr hbc
  refine (S.polar_cl_eq_zero_iff (S.QG.mul_mem ha hb) hc).mp ?_
  rw [S.cl_mul ha hb, polar_add_left, h1, h2]
  decide

omit [Finite G] in
theorem commutator_eq_z_of_not_commute {a b : G} (ha : a ∈ S.QG) (hb : b ∈ S.QG)
    (hab : a * b ≠ b * a) : a * b * a⁻¹ * b⁻¹ = S.z := by
  rcases S.commutator_eq_one_or_z ha hb with h | h
  · exfalso
    apply hab
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  · exact h

end Comm

namespace Decomp

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (D : Decomp S)

section Nine

variable (hB : ∀ h : G, h * S.z * h⁻¹ ∈ D.B → h * S.z * h⁻¹ = S.z) (h8 : 8 < Nat.card D.A)
  (hB8 : 8 < Nat.card D.B ∨ ∀ b ∈ D.B, b ^ 2 = 1 → b = 1 ∨ b = S.z)

include hB h8 hB8

theorem mul_conj_of_commute' {x y : G} (hx : x ∈ D.A) (hx' : ∃ k : G, k * S.z * k⁻¹ = x)
    (hy : y ∈ D.A) (hy' : ∃ k : G, k * S.z * k⁻¹ = y) (hne : x ≠ y) (hxy : x * y = y * x) :
    ∃ k : G, k * S.z * k⁻¹ = x * y := by
  obtain ⟨g, rfl⟩ := hx'
  obtain ⟨h, rfl⟩ := hy'
  obtain ⟨k, hk⟩ := D.mul_conj_of_commute hB h8 hB8 hx hy hne hxy
  exact ⟨k, hk.symm⟩

theorem false_of_commute_of_not_commute {u v w : G} (hu : u ∈ D.A)
    (hu' : ∃ k : G, k * S.z * k⁻¹ = u) (hv : v ∈ D.A) (hv' : ∃ k : G, k * S.z * k⁻¹ = v)
    (huv : u * v ≠ v * u) (hw : w ∈ D.A) (hw' : ∃ k : G, k * S.z * k⁻¹ = w) (hwz : w ≠ S.z)
    (hwu : w * u = u * w) (hwv : w * v = v * w) : False := by
  obtain ⟨k, rfl⟩ := hw'
  obtain ⟨ku, rfl⟩ := hu'
  obtain ⟨kv, rfl⟩ := hv'
  have huA := D.mem_conj_A_of_commute hB h8 hB8 hw hwz hu hwu
  have hvA := D.mem_conj_A_of_commute hB h8 hB8 hw hwz hv hwv
  have h1 := commutator_eq_z_of_not_commute S (D.A_le hu) (D.A_le hv) huv
  rcases (S.conjBy k).commutator_eq_one_or_z ((D.conj k).A_le huA) ((D.conj k).A_le hvA) with
    h | h
  · rw [h1] at h
    exact S.z_ne_one h
  · rw [h1, Setting.conjBy_z] at h
    exact hwz h.symm

theorem eq_or_eq_mul_z_of_commute {u v : G} (hu : u ∈ D.A) (hu' : ∃ k : G, k * S.z * k⁻¹ = u)
    (hv : v ∈ D.A) (hv' : ∃ k : G, k * S.z * k⁻¹ = v) (huv : u * v ≠ v * u) {x y : G}
    (hx : x ∈ D.A) (hx' : ∃ k : G, k * S.z * k⁻¹ = x) (hxz : x ≠ S.z) (hy : y ∈ D.A)
    (hy' : ∃ k : G, k * S.z * k⁻¹ = y) (hyz : y ≠ S.z) (hxy : x * y = y * x) :
    y = x ∨ y = x * S.z := by
  by_contra hne
  push Not at hne
  obtain ⟨hyx, hyxz⟩ := hne
  have hinv : ∀ w : G, (∃ k : G, k * S.z * k⁻¹ = w) → w * w = 1 := by
    rintro w ⟨k, rfl⟩
    exact (S.conjBy k).z_mul_z
  have hxQ := D.A_le hx
  have hyQ := D.A_le hy
  have huQ := D.A_le hu
  have hvQ := D.A_le hv
  have hA : ∀ w : G, w ∈ D.A → (∃ k : G, k * S.z * k⁻¹ = w) → w ≠ S.z → w * u = u * w →
      w * v = v * w → False := fun w hw hw' hwz hwu hwv =>
    D.false_of_commute_of_not_commute hB h8 hB8 hu hu' hv hv' huv hw hw' hwz hwu hwv
  have hcand : ∀ t : G, (t = x ∨ t = y ∨ t = x * y) →
      t ∈ D.A ∧ (∃ k : G, k * S.z * k⁻¹ = t) ∧ t ≠ S.z := by
    rintro t (rfl | rfl | rfl)
    · exact ⟨hx, hx', hxz⟩
    · exact ⟨hy, hy', hyz⟩
    · refine ⟨D.A.mul_mem hx hy, D.mul_conj_of_commute' hB h8 hB8 hx hx' hy hy' hyx.symm hxy,
        fun h => hyxz ?_⟩
      calc y = x * x * y := by rw [hinv x hx', one_mul]
        _ = x * S.z := by rw [mul_assoc, h]
  have hcandQ : ∀ t : G, (t = x ∨ t = y ∨ t = x * y) → t ∈ S.QG := fun t ht =>
    D.A_le (hcand t ht).1
  have select : ∀ p q : G, p ∈ S.QG → (∀ t : G, (t = x ∨ t = y ∨ t = x * y) →
      t * p = p * t → t * q = q * t → False) →
      ∃ t : G, (t = x ∨ t = y ∨ t = x * y) ∧ t * p = p * t ∧ t * q ≠ q * t := by
    intro p q hp hpq
    by_cases hxp : x * p = p * x
    · exact ⟨x, Or.inl rfl, hxp, fun h => hpq x (Or.inl rfl) hxp h⟩
    by_cases hyp : y * p = p * y
    · exact ⟨y, Or.inr (Or.inl rfl), hyp, fun h => hpq y (Or.inr (Or.inl rfl)) hyp h⟩
    have h := commute_mul_of_not_commute S hxQ hyQ hp hxp hyp
    exact ⟨x * y, Or.inr (Or.inr rfl), h, fun h' => hpq _ (Or.inr (Or.inr rfl)) h h'⟩
  obtain ⟨t, ht, htu, htv⟩ := select u v huQ fun t ht h1 h2 =>
    hA t (hcand t ht).1 (hcand t ht).2.1 (hcand t ht).2.2 h1 h2
  obtain ⟨t', ht', ht'v, ht'u⟩ := select v u hvQ fun t ht h1 h2 =>
    hA t (hcand t ht).1 (hcand t ht).2.1 (hcand t ht).2.2 h2 h1
  have htt' : t * t' = t' * t := by
    have hc : Commute x y := hxy
    rcases ht with rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl
    · exact (Commute.refl _).eq
    · exact hc.eq
    · exact ((Commute.refl _).mul_right hc).eq
    · exact hc.symm.eq
    · exact (Commute.refl _).eq
    · exact (hc.symm.mul_right (Commute.refl _)).eq
    · exact ((Commute.refl _).mul_right hc).symm.eq
    · exact (hc.symm.mul_right (Commute.refl _)).symm.eq
    · exact (Commute.refl _).eq
  have ht'Q := hcandQ t' ht'
  have htu1 : t ≠ u := by
    rintro rfl
    exact ht'u htt'.symm
  have htuz : t ≠ u * S.z := by
    intro h
    apply ht'u
    have e : t' * (u * S.z) = u * S.z * t' := by rw [← h]; exact htt'.symm
    apply mul_right_cancel (b := S.z)
    calc t' * u * S.z = t' * (u * S.z) := mul_assoc _ _ _
      _ = u * S.z * t' := e
      _ = u * (S.z * t') := mul_assoc _ _ _
      _ = u * (t' * S.z) := by rw [S.z_comm_QG ht'Q]
      _ = u * t' * S.z := (mul_assoc _ _ _).symm
  obtain ⟨htA, ht'', -⟩ := hcand t ht
  have htQ := D.A_le htA
  have hconj := D.mul_conj_of_commute' hB h8 hB8 htA ht'' hu hu' htu1 htu
  refine hA (t * u) (D.A.mul_mem htA hu) hconj (fun h => htuz ?_) ?_
    (commute_mul_of_not_commute S htQ huQ hvQ htv huv)
  · calc t = t * u * u := by rw [mul_assoc, hinv u hu', mul_one]
      _ = S.z * u := by rw [h]
      _ = u * S.z := (S.z_comm_QG huQ).symm
  · calc t * u * u = u * t * u := by rw [htu]
      _ = u * (t * u) := mul_assoc _ _ _

end Nine

end Decomp

end Sm77

end CFSG.LargeExtraspecial.DW

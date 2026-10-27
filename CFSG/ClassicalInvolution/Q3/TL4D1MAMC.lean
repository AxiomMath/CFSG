module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAMA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Generic Wr Equiv

variable {n : ℕ}

@[expose] def vbar (n : ℕ) (x : Fin n → ZMod 2) : AEQ n := mkQ n (ofVec x)

theorem vbar_add (x y : Fin n → ZMod 2) : vbar n (x + y) = vbar n x * vbar n y := by
  rw [vbar, vbar, vbar, ← map_mul, ofVec_mul_ofVec]

theorem vbar_zero : vbar n 0 = 1 := by
  rw [vbar, show ofVec (0 : Fin n → ZMod 2) = 1 from rfl, map_one]

theorem permBar_vbar (x : Fin n → ZMod 2) : permBar n (vbar n x) = 1 := permBar_mkQ (ofVec x)

theorem vbar_eq_iff {x y : Fin n → ZMod 2} : vbar n x = vbar n y ↔ ModPi x y := by
  rw [vbar, vbar, mkQ_eq_iff, inv_eq_of_mul_eq_one_right (ofVec_mul_self x), ofVec_mul_ofVec]
  constructor
  · rintro (h | h)
    · left
      funext i
      have h' := congrFun (congrArg Wr.vec h) i
      revert h'
      show x i + y i = 0 → x i = y i
      generalize x i = c
      generalize y i = d
      revert c d
      decide
    · right
      funext i
      have h' := congrFun (congrArg Wr.vec h) i
      revert h'
      show x i + y i = 1 → x i = y i + 1
      generalize x i = c
      generalize y i = d
      revert c d
      decide
  · rintro (rfl | rfl)
    · left
      rw [add_self_vec]
      rfl
    · right
      refine Wr.ext (funext fun i => ?_) rfl
      show y i + 1 + y i = 1
      generalize y i = c
      revert c
      decide

theorem conj_vbar {g : AEQ n} {σ : Perm (Fin n)} (hg : permBar n g = σ) (x : Fin n → ZMod 2) :
    g * vbar n x * g⁻¹ = vbar n (actV σ x) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  rw [show (QuotientGroup.mk a : AEQ n) = mkQ n a from rfl, permBar_mkQ] at hg
  subst hg
  rw [show (QuotientGroup.mk a : AEQ n) = mkQ n a from rfl, vbar, vbar, ← map_inv, ← map_mul,
    ← map_mul, conj_ofVec]
  rfl

theorem exists_vbar_of_permBar_eq_one {g : AEQ n} (hg : permBar n g = 1) : ∃ x, g = vbar n x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  have ha : a.perm = 1 := by rw [← permBar_mkQ]; exact hg
  have h2 : a = ofVec a.vec := by
    calc a = ofVec a.vec * ofPerm a.perm := eq_ofVec_mul_ofPerm a
      _ = ofVec a.vec := by rw [ha]; exact mul_one _
  exact ⟨a.vec, congrArg (mkQ n) h2⟩

theorem vbar_mem_aeBarOver {P : Subgroup (Perm (Fin n))} {x : Fin n → ZMod 2}
    (hx : ∑ i, x i = 0) : vbar n x ∈ aeBarOver P :=
  mkQ_mem_aeBarOver (ofVec_mem_aeSubOver hx)

section Quat

variable {G : Type} [Group G] {B : Subgroup G} {w : G}

theorem sq_eq_of_isUniqueInvolution (hz : IsUniqueInvolution B w) (hc : Nat.card B = 8)
    (hnc : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) {g : G} (hg : g ∈ B) (h1 : g ≠ 1) (hw : g ≠ w) :
    g * g = w := by
  have hdvd : orderOf g ∣ 2 ^ 3 := by
    have := orderOf_dvd_natCard (⟨g, hg⟩ : B)
    rwa [Subgroup.orderOf_mk, hc] at this
  obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases i <;> norm_num at hgi
  · exact absurd hgi h1
  · have h2 : g * g = 1 := by rw [← pow_two, ← hgi, pow_orderOf_eq_one]
    rcases hz.unique g hg h2 with h | h
    · exact absurd h h1
    · exact absurd h hw
  · have h4 : g * g * (g * g) = 1 := by
      rw [show g * g * (g * g) = g ^ 4 by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two],
        ← hgi, pow_orderOf_eq_one]
    have h2 : g * g ≠ 1 := fun h => by
      have := orderOf_dvd_of_pow_eq_one (show g ^ 2 = 1 by rw [pow_two]; exact h)
      rw [hgi] at this
      norm_num at this
    exact (hz.unique _ (B.mul_mem hg hg) h4).resolve_left h2
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    have : Finite B := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    have hzp : Subgroup.zpowers g = B := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr hg) (by rw [Nat.card_zpowers, hgi, hc])
    rw [← hzp] at hx hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hxy (by rw [← zpow_add, ← zpow_add, add_comm])

theorem exists_q8_gens (hz : IsUniqueInvolution B w) (hc : Nat.card B = 8)
    (hnc : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) :
    ∃ x ∈ B, ∃ y ∈ B, x * x = w ∧ y * y = w ∧ x * y = w * (y * x) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  have hwc : ∀ k ∈ B, k * w = w * k := fun k hk => TC.Thin.isUniqueInvolution_comm hz hk
  have hsq : ∀ {g : G}, g ∈ B → g ≠ 1 → g ≠ w → g * g = w := fun hg h1 hw =>
    sq_eq_of_isUniqueInvolution hz hc ⟨x, hx, y, hy, hxy⟩ hg h1 hw
  have hx1 : x ≠ 1 := fun h => hxy (by rw [h, one_mul, mul_one])
  have hxw : x ≠ w := fun h => hxy (by rw [h]; exact (hwc y hy).symm)
  have hy1 : y ≠ 1 := fun h => hxy (by rw [h, one_mul, mul_one])
  have hyw : y ≠ w := fun h => hxy (by rw [h]; exact hwc x hx)
  have hxy1 : x * y ≠ 1 := fun h => hxy (by
    rw [eq_inv_of_mul_eq_one_right h, mul_inv_cancel, inv_mul_cancel])
  have hxyw : x * y ≠ w := fun h => hxy (by
    have hy' : y = x⁻¹ * w := by rw [← h]; group
    rw [hy', ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, ← hwc x hx, ← mul_assoc,
      inv_mul_cancel, one_mul])
  have h3 := hsq (B.mul_mem hx hy) hxy1 hxyw
  have hx2 := hsq hx hx1 hxw
  have hy2 := hsq hy hy1 hyw
  refine ⟨x, hx, y, hy, hx2, hy2, ?_⟩
  have h4 : y * x * y = x := by
    have : x * (y * x * y) = x * x := by rw [hx2, ← h3]; group
    exact mul_left_cancel this
  calc x * y = y * x * y * y := by rw [h4]
    _ = y * x * w := by rw [mul_assoc, hy2]
    _ = w * (y * x) := (hwc _ (B.mul_mem hy hx))

end Quat

end CFSG.ClassicalInvolution.Q3.TL4

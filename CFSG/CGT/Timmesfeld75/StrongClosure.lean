module

public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def StrongWC (T : Subgroup G) : Prop :=
  IsElemAbelian 2 T ∧ ∀ t ∈ T, t ≠ 1 → ∀ a ∈ T, ∀ g : G,
    g⁻¹ * a * g ∈ Subgroup.centralizer ({t} : Set G) → g⁻¹ * a * g ∈ T

@[expose] def classD (T : Subgroup G) : Set G :=
  {x | ∃ g : G, ∃ t ∈ T, t ≠ 1 ∧ x = g⁻¹ * t * g}

section Basic

variable {T : Subgroup G}

theorem StrongWC.isWC [Finite G] (h : StrongWC T) : IsWC T := by
  refine ⟨h.1, fun t ht ht1 => ⟨fun x hx => ?_, fun g hg => conjSubgroup_eq_of_le fun x hx => ?_⟩⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact elemAbelian_mul_comm h.1 ht hx
  · have hx' : g⁻¹ * x * g ∈ T := mem_conjSubgroup.1 hx
    have key : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    have := h.2 t ht ht1 (g⁻¹ * x * g) hx' g⁻¹ (by rw [key]; exact hg hx)
    rwa [key] at this

theorem classD_conj {x : G} (hx : x ∈ classD T) (g : G) : g⁻¹ * x * g ∈ classD T := by
  obtain ⟨k, t, ht, ht1, rfl⟩ := hx
  exact ⟨k * g, t, ht, ht1, by group⟩

theorem mem_classD_of_mem {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) : t ∈ classD T :=
  ⟨1, t, ht, ht1, by group⟩

theorem orderOf_inv_mul_mul_eq (g t : G) : orderOf (g⁻¹ * t * g) = orderOf t := by
  simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t

theorem classD_orderOf (h : StrongWC T) {x : G} (hx : x ∈ classD T) : orderOf x = 2 := by
  obtain ⟨g, t, ht, ht1, rfl⟩ := hx
  rw [orderOf_inv_mul_mul_eq]
  exact orderOf_eq_prime (h.1.2 t ht) ht1

theorem classD_mul_self (h : StrongWC T) {x : G} (hx : x ∈ classD T) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [classD_orderOf h hx, pow_two] at this

theorem commute_classD_le (h : StrongWC T) {y x : G} (hy : y ∈ T) (hy1 : y ≠ 1)
    (hx : x ∈ classD T) (hc : x * y = y * x) : x ∈ T := by
  obtain ⟨g, t, ht, ht1, rfl⟩ := hx
  refine h.2 y hy hy1 t ht g (Subgroup.mem_centralizer_iff.2 fun z hz => ?_)
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact hc.symm

end Basic

section Dihedral

theorem inv_pow_mul_mul_pow_of_inverts {a w : G} (h : a * w * a⁻¹ = w⁻¹) (j : ℕ) :
    (w ^ j)⁻¹ * a * w ^ j = (w ^ (2 * j))⁻¹ * a := by
  have h1 : a * w ^ j * a⁻¹ = (w ^ j)⁻¹ := by rw [← conj_pow, h, inv_pow]
  have h2 : a * w ^ j = (w ^ j)⁻¹ * a := mul_inv_eq_iff_eq_mul.1 h1
  calc (w ^ j)⁻¹ * a * w ^ j = (w ^ j)⁻¹ * (a * w ^ j) := mul_assoc _ _ _
    _ = (w ^ j)⁻¹ * ((w ^ j)⁻¹ * a) := by rw [h2]
    _ = ((w ^ j)⁻¹ * (w ^ j)⁻¹) * a := (mul_assoc _ _ _).symm
    _ = (w ^ (2 * j))⁻¹ * a := by rw [← mul_inv_rev, ← pow_add, two_mul]

variable {x y : G}

theorem left_invol_inverts (hx : x * x = 1) (hy : y * y = 1) :
    x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy, ← mul_assoc, hx,
    one_mul]

theorem right_invol_inverts (hx : x * x = 1) (hy : y * y = 1) :
    y * (x * y) * y⁻¹ = (x * y)⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  simp only [mul_assoc, hy, mul_one]

theorem invol_eq_inv_mul_mul (hy : y * y = 1) : y = (x * y)⁻¹ * x := by
  rw [mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right hy]

theorem orderOf_mul_dvd_two_iff_commute (hx : x * x = 1) (hy : y * y = 1) :
    orderOf (x * y) ∣ 2 ↔ x * y = y * x := by
  rw [orderOf_dvd_iff_pow_eq_one, pow_two]
  constructor
  · intro h
    have h1 := eq_inv_of_mul_eq_one_left h
    rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy] at h1
  · intro h
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [h]
      _ = 1 := by rw [← mul_assoc x x y, hx, one_mul, hy]

theorem dihedral_central_of_even_order (hx : x * x = 1) (hy : y * y = 1) {m : ℕ} (hm0 : 0 < m)
    (hm : orderOf (x * y) = 2 * m) :
    ∃ z : G, z * z = 1 ∧ z ≠ 1 ∧ x * z = z * x ∧ y * z = z * y ∧
      ((∃ g : G, y * z = g⁻¹ * x * g) ∨ ∃ g : G, y * z = g⁻¹ * y * g) := by
  have hzz : (x * y) ^ m * (x * y) ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← hm]
    exact pow_orderOf_eq_one _
  have hzinv : ((x * y) ^ m)⁻¹ = (x * y) ^ m := inv_eq_of_mul_eq_one_right hzz
  have hxz : x * (x * y) ^ m = (x * y) ^ m * x := by
    have h1 : x * (x * y) ^ m * x⁻¹ = (x * y) ^ m := by
      rw [← conj_pow, left_invol_inverts hx hy, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hxw : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have hyz : y * (x * y) ^ m = (x * y) ^ m * y := by
    calc y * (x * y) ^ m = x * (x * y) * (x * y) ^ m := by rw [hxw]
      _ = x * ((x * y) * (x * y) ^ m) := mul_assoc _ _ _
      _ = x * ((x * y) ^ m * (x * y)) := by rw [(Commute.self_pow (x * y) m).eq]
      _ = (x * (x * y) ^ m) * (x * y) := (mul_assoc _ _ _).symm
      _ = ((x * y) ^ m * x) * (x * y) := by rw [hxz]
      _ = (x * y) ^ m * (x * (x * y)) := mul_assoc _ _ _
      _ = (x * y) ^ m * y := by rw [hxw]
  refine ⟨(x * y) ^ m, hzz, pow_ne_one_of_lt_orderOf hm0.ne' (by omega), hxz, hyz, ?_⟩
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · right
    refine ⟨(x * y) ^ k, ?_⟩
    rw [inv_pow_mul_mul_pow_of_inverts (right_invol_inverts hx hy) k,
      show 2 * k = m by omega, hzinv, hyz]
  · left
    refine ⟨(x * y) ^ (k + 1), ?_⟩
    have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hx hy) (k + 1)
    calc y * (x * y) ^ m = (x * y)⁻¹ * x * (x * y) ^ m := by rw [← invol_eq_inv_mul_mul hy]
      _ = (x * y)⁻¹ * ((x * y) ^ m * x) := by rw [mul_assoc, hxz]
      _ = (x * y)⁻¹ * (x * y) ^ m * x := (mul_assoc _ _ _).symm
      _ = ((x * y) ^ m * (x * y))⁻¹ * x := by rw [mul_inv_rev ((x * y) ^ m) (x * y), hzinv]
      _ = ((x * y) ^ (2 * (k + 1)))⁻¹ * x := by
        rw [show 2 * (k + 1) = m + 1 by omega, pow_succ]
      _ = ((x * y) ^ (k + 1))⁻¹ * x * (x * y) ^ (k + 1) := h1.symm

theorem isConj_of_odd_orderOf_mul (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y))) : IsConj x y := by
  obtain ⟨k, hk⟩ := hodd
  have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hx hy) (k + 1)
  have hpow : (x * y) ^ (2 * (k + 1)) = x * y := by
    rw [show 2 * (k + 1) = orderOf (x * y) + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hpow] at h1
  refine isConj_iff.2 ⟨((x * y) ^ (k + 1))⁻¹, ?_⟩
  rw [inv_inv, h1]
  exact (invol_eq_inv_mul_mul hy).symm

end Dihedral

section Fusion

variable {T : Subgroup G}

theorem odd_orderOf_mul_of_not_mem [Finite G] (h : StrongWC T) {x y : G} (hx : x ∈ classD T)
    (hxT : x ∉ T) (hy : y ∈ T) (hy1 : y ≠ 1) : Odd (orderOf (x * y)) := by
  rcases Nat.even_or_odd (orderOf (x * y)) with ⟨m, hm⟩ | hodd
  swap
  · exact hodd
  have hyD : y ∈ classD T := mem_classD_of_mem hy hy1
  have hxx : x * x = 1 := classD_mul_self h hx
  have hyy : y * y = 1 := classD_mul_self h hyD
  have hm0 : 0 < m := by
    have := orderOf_pos (x * y)
    omega
  obtain ⟨z, -, hz1, hxz, hyz, hconj⟩ :=
    dihedral_central_of_even_order hxx hyy hm0 (by omega)
  have hyzD : y * z ∈ classD T := by
    rcases hconj with ⟨g, hg⟩ | ⟨g, hg⟩
    · rw [hg]
      exact classD_conj hx g
    · rw [hg]
      exact classD_conj hyD g
  have hyzT : y * z ∈ T := by
    refine commute_classD_le h hy hy1 hyzD ?_
    calc y * z * y = y * (z * y) := mul_assoc _ _ _
      _ = y * (y * z) := by rw [hyz]
  have hzT : z ∈ T := by
    have := T.mul_mem hy hyzT
    rwa [← mul_assoc, hyy, one_mul] at this
  exact absurd (commute_classD_le h hzT hz1 hx hxz) hxT

theorem orderOf_mul_classD [Finite G] (h : StrongWC T) {x y : G} (hx : x ∈ classD T)
    (hy : y ∈ classD T) : orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)) := by
  obtain ⟨g, t, ht, ht1, rfl⟩ := hx
  have hy' : g * y * g⁻¹ ∈ classD T := by
    have := classD_conj hy g⁻¹
    rwa [inv_inv] at this
  have hord : orderOf (g⁻¹ * t * g * y) = orderOf (t * (g * y * g⁻¹)) := by
    rw [← orderOf_inv_mul_mul_eq g (t * (g * y * g⁻¹))]
    congr 1
    group
  rw [hord]
  have htt : t * t = 1 := classD_mul_self h (mem_classD_of_mem ht ht1)
  have hy'y' : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := classD_mul_self h hy'
  by_cases hyT : g * y * g⁻¹ ∈ T
  · left
    exact (orderOf_mul_dvd_two_iff_commute htt hy'y').2 (elemAbelian_mul_comm h.1 ht hyT)
  · right
    have hodd := odd_orderOf_mul_of_not_mem h hy' hyT ht ht1
    have hinv : g * y * g⁻¹ * t = (t * (g * y * g⁻¹))⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right htt, inv_eq_of_mul_eq_one_right hy'y']
    rwa [hinv, orderOf_inv] at hodd

theorem conj_mem_of_not_isConj [Finite G] (h : StrongWC T) {a b : G} (ha : a ∈ T) (ha1 : a ≠ 1)
    (hb : b ∈ T) (hb1 : b ≠ 1) (hnc : ¬ IsConj a b) (g : G) : g⁻¹ * a * g ∈ T := by
  have hx : g⁻¹ * a * g ∈ classD T := ⟨g, a, ha, ha1, rfl⟩
  have hbD : b ∈ classD T := mem_classD_of_mem hb hb1
  have hxx : g⁻¹ * a * g * (g⁻¹ * a * g) = 1 := classD_mul_self h hx
  have hbb : b * b = 1 := classD_mul_self h hbD
  rcases orderOf_mul_classD h hx hbD with hd | hodd
  · exact commute_classD_le h hb hb1 hx ((orderOf_mul_dvd_two_iff_commute hxx hbb).1 hd)
  · exact absurd ((isConj_iff.2 ⟨g⁻¹, by simp⟩).trans (isConj_of_odd_orderOf_mul hxx hbb hodd)) hnc

theorem single_class_or_normal [Finite G] (h : StrongWC T) (hT : T ≠ ⊥) :
    (∃ d₀ : G, classD T = {g | IsConj d₀ g}) ∨ (∀ g : G, conjSubgroup g T = T) := by
  by_cases hconj : ∀ a ∈ T, a ≠ 1 → ∀ b ∈ T, b ≠ 1 → IsConj a b
  · left
    obtain ⟨t₀, ht₀, ht₀1⟩ : ∃ t₀ ∈ T, t₀ ≠ 1 := by
      obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hT
      exact ⟨t, ht, fun h' => ht1 (Subtype.ext h')⟩
    refine ⟨t₀, Set.ext fun x => ⟨?_, fun hx => ?_⟩⟩
    · rintro ⟨g, t, ht, ht1, rfl⟩
      exact (hconj t₀ ht₀ ht₀1 t ht ht1).trans (isConj_iff.2 ⟨g⁻¹, by simp⟩)
    · obtain ⟨c, hc⟩ := isConj_iff.1 hx
      exact ⟨c⁻¹, t₀, ht₀, ht₀1, by rw [← hc]; group⟩
  · right
    push Not at hconj
    obtain ⟨t₁, ht₁, ht₁1, t₂, ht₂, ht₂1, hnc⟩ := hconj
    have hall : ∀ a ∈ T, ∀ g : G, g⁻¹ * a * g ∈ T := by
      intro a ha g
      by_cases ha1 : a = 1
      · subst ha1
        simp
      · by_cases h1 : IsConj a t₁
        · exact conj_mem_of_not_isConj h ha ha1 ht₂ ht₂1 (fun h2 => hnc (h1.symm.trans h2)) g
        · exact conj_mem_of_not_isConj h ha ha1 ht₁ ht₁1 h1 g
    intro g
    refine conjSubgroup_eq_of_le fun x hx => ?_
    have key : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    have := hall _ (mem_conjSubgroup.1 hx) g⁻¹
    rwa [key] at this

end Fusion

end CFSG.CGT.Timmesfeld75

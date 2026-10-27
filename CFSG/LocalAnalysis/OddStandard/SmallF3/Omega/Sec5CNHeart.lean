module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888G1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure Sec5CNHeart (φ : (Fin 8 → ZMod 2) → G) (A : Subgroup G) : Prop where
  mem : ∀ v, IsEvenVec v → φ v ∈ A
  mul : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w
  eq_one : ∀ v, IsEvenVec v → (φ v = 1 ↔ (v = 0 ∨ v = fun _ => 1))
  surj : ∀ x ∈ A, ∃ v, IsEvenVec v ∧ φ v = x

theorem sec5cn_heart_of {φ : (Fin 8 → ZMod 2) → G} {A H : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))}
    (hpm : IsPermModuleMod (n := 8) IsEvenVec ({0, fun _ => 1} : Set (Fin 8 → ZMod 2)) φ A ⊥ H
      Alt) : Sec5CNHeart φ A := by
  obtain ⟨-, -, -, -, hmem, hmul, hker, hsurj, -, -⟩ := hpm
  refine ⟨hmem, fun v w hv hw => ?_, fun v hv => ?_, fun x hx => ?_⟩
  · have h1 := hmul v w hv hw
    rw [Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  · have h1 := hker v hv
    rw [Subgroup.mem_bot] at h1
    simpa using h1
  · obtain ⟨v, hv, h1⟩ := hsurj x hx
    rw [Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact ⟨v, hv, h1⟩

theorem sec5cn_isEvenVec_zero : IsEvenVec (0 : Fin 8 → ZMod 2) := by
  simp [IsEvenVec]

theorem sec5cn_isEvenVec_add {v w : Fin 8 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp only [Pi.add_apply, Finset.sum_add_distrib, hv, hw, add_zero]

variable {φ : (Fin 8 → ZMod 2) → G} {A : Subgroup G}

theorem Sec5CNHeart.zero (h : Sec5CNHeart φ A) : φ 0 = 1 :=
  (h.eq_one 0 sec5cn_isEvenVec_zero).mpr (Or.inl rfl)

theorem Sec5CNHeart.sq (h : Sec5CNHeart φ A) {v : Fin 8 → ZMod 2} (hv : IsEvenVec v) :
    φ v * φ v = 1 := by
  rw [← h.mul v v hv hv]
  have : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  rw [this, h.zero]

theorem Sec5CNHeart.comm (h : Sec5CNHeart φ A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x := by
  obtain ⟨v, hv, rfl⟩ := h.surj x hx
  obtain ⟨w, hw, rfl⟩ := h.surj y hy
  rw [← h.mul v w hv hw, ← h.mul w v hw hv, add_comm]

theorem Sec5CNHeart.sq_mem (h : Sec5CNHeart φ A) {x : G} (hx : x ∈ A) : x * x = 1 := by
  obtain ⟨v, hv, rfl⟩ := h.surj x hx
  exact h.sq hv

theorem Sec5CNHeart.ne_of (h : Sec5CNHeart φ A) {v w : Fin 8 → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) (h1 : v + w ≠ 0) (h2 : v + w ≠ fun _ => 1) : φ v ≠ φ w := by
  intro heq
  have h3 : φ (v + w) = 1 := by
    rw [h.mul v w hv hw, heq]
    exact h.sq hw
  rcases (h.eq_one _ (sec5cn_isEvenVec_add hv hw)).mp h3 with h4 | h4
  exacts [h1 h4, h2 h4]

private def sec5cnVec (S : Finset (Fin 8)) : Fin 8 → ZMod 2 := fun i => if i ∈ S then 1 else 0

private theorem sec5cn_vec_facts :
    IsFirstBlockVec (sec5cnVec {0, 1}) ∧ IsFirstBlockVec (sec5cnVec {0, 2}) ∧
      IsSecondBlockVec (sec5cnVec {4, 5}) ∧ IsSecondBlockVec (sec5cnVec {4, 6}) ∧
      IsEvenVec heartZVec := by
  unfold IsFirstBlockVec IsSecondBlockVec IsEvenVec heartZVec sec5cnVec
  decide

private theorem sec5cn_vec_notN :
    (sec5cnVec {0, 1} + heartZVec ≠ 0 ∧ sec5cnVec {0, 1} + heartZVec ≠ fun _ => 1) ∧
    (sec5cnVec {0, 2} + heartZVec ≠ 0 ∧ sec5cnVec {0, 2} + heartZVec ≠ fun _ => 1) ∧
    (sec5cnVec {0, 2} + sec5cnVec {0, 1} ≠ 0 ∧
      sec5cnVec {0, 2} + sec5cnVec {0, 1} ≠ fun _ => 1) ∧
    (sec5cnVec {0, 2} + (sec5cnVec {0, 1} + heartZVec) ≠ 0 ∧
      sec5cnVec {0, 2} + (sec5cnVec {0, 1} + heartZVec) ≠ fun _ => 1) ∧
    (sec5cnVec {0, 1} + 0 ≠ 0 ∧ sec5cnVec {0, 1} + 0 ≠ fun _ => 1) ∧
    (sec5cnVec {0, 2} + 0 ≠ 0 ∧ sec5cnVec {0, 2} + 0 ≠ fun _ => 1) := by
  unfold heartZVec sec5cnVec
  decide

private theorem sec5cn_vec_notN' :
    (sec5cnVec {4, 5} + heartZVec ≠ 0 ∧ sec5cnVec {4, 5} + heartZVec ≠ fun _ => 1) ∧
    (sec5cnVec {4, 6} + heartZVec ≠ 0 ∧ sec5cnVec {4, 6} + heartZVec ≠ fun _ => 1) ∧
    (sec5cnVec {4, 5} + sec5cnVec {4, 6} ≠ 0 ∧
      sec5cnVec {4, 5} + sec5cnVec {4, 6} ≠ fun _ => 1) ∧
    (sec5cnVec {4, 5} + sec5cnVec {4, 6} + heartZVec ≠ 0 ∧
      sec5cnVec {4, 5} + sec5cnVec {4, 6} + heartZVec ≠ fun _ => 1) ∧
    (sec5cnVec {4, 5} + 0 ≠ 0 ∧ sec5cnVec {4, 5} + 0 ≠ fun _ => 1) ∧
    (sec5cnVec {4, 6} + 0 ≠ 0 ∧ sec5cnVec {4, 6} + 0 ≠ fun _ => 1) := by
  unfold heartZVec sec5cnVec
  decide

theorem sec5cn_exists_ab {KK : Subgroup G} {z : G} (h : Sec5CNHeart φ A)
    (hz : z = φ heartZVec)
    (hK : ∀ x : G, x ∈ A ⊓ KK ↔ ∃ v, IsFirstBlockVec v ∧ φ v = x) :
    ∃ a b : G, a ∈ A ⊓ KK ∧ b ∈ A ⊓ KK ∧ a ≠ 1 ∧ a ≠ z ∧ b ≠ 1 ∧ b ≠ z ∧ b ≠ a ∧
      b ≠ a * z := by
  obtain ⟨hA, hB, -, -, hzE⟩ := sec5cn_vec_facts
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨e1, e2⟩, ⟨f1, f2⟩⟩ := sec5cn_vec_notN
  have evA : IsEvenVec (sec5cnVec {0, 1}) := hA.1
  have evB : IsEvenVec (sec5cnVec {0, 2}) := hB.1
  refine ⟨φ (sec5cnVec {0, 1}), φ (sec5cnVec {0, 2}), (hK _).mpr ⟨_, hA, rfl⟩,
    (hK _).mpr ⟨_, hB, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h.ne_of evA sec5cn_isEvenVec_zero e1 e2
    rwa [h.zero] at this
  · rw [hz]
    exact h.ne_of evA hzE a1 a2
  · have := h.ne_of evB sec5cn_isEvenVec_zero f1 f2
    rwa [h.zero] at this
  · rw [hz]
    exact h.ne_of evB hzE b1 b2
  · exact h.ne_of evB evA c1 c2
  · rw [hz, ← h.mul _ _ evA hzE]
    exact h.ne_of evB (sec5cn_isEvenVec_add evA hzE) d1 d2

theorem sec5cn_mul_mem_pair {z t u₁ u₂ : G} (ht2 : t * t = 1) (hz2 : z * z = 1)
    (htz : t * z = z * t) (h1 : u₁ = t ∨ u₁ = t * z) (h2 : u₂ = t ∨ u₂ = t * z) :
    u₁ * u₂ = 1 ∨ u₁ * u₂ = z := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · left
    exact ht2
  · right
    rw [← mul_assoc, ht2, one_mul]
  · right
    rw [htz, mul_assoc, ht2, mul_one]
  · left
    calc t * z * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [← htz]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [ht2, hz2, mul_one]

theorem sec5cn_exists_a1 {PP : Subgroup G} {z t : G} (h : Sec5CNHeart φ A)
    (hz : z = φ heartZVec)
    (hP : ∀ x : G, x ∈ A ⊓ PP ↔ ∃ v, IsSecondBlockVec v ∧ φ v = x) (ht2 : t * t = 1)
    (htz : t * z = z * t) :
    ∃ a₁ ∈ A ⊓ PP, a₁ ≠ 1 ∧ a₁ ≠ z ∧ a₁ ≠ t ∧ a₁ ≠ t * z := by
  obtain ⟨-, -, hC, hD, hzE⟩ := sec5cn_vec_facts
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨e1, e2⟩, ⟨f1, f2⟩⟩ := sec5cn_vec_notN'
  have evC : IsEvenVec (sec5cnVec {4, 5}) := hC.1
  have evD : IsEvenVec (sec5cnVec {4, 6}) := hD.1
  have hz2 : z * z = 1 := by
    rw [hz]
    exact h.sq hzE
  have hu₁1 : φ (sec5cnVec {4, 5}) ≠ 1 := by
    have := h.ne_of evC sec5cn_isEvenVec_zero e1 e2
    rwa [h.zero] at this
  have hu₂1 : φ (sec5cnVec {4, 6}) ≠ 1 := by
    have := h.ne_of evD sec5cn_isEvenVec_zero f1 f2
    rwa [h.zero] at this
  have hu₁z : φ (sec5cnVec {4, 5}) ≠ z := by
    rw [hz]
    exact h.ne_of evC hzE a1 a2
  have hu₂z : φ (sec5cnVec {4, 6}) ≠ z := by
    rw [hz]
    exact h.ne_of evD hzE b1 b2
  have hu₁₂1 : φ (sec5cnVec {4, 5}) * φ (sec5cnVec {4, 6}) ≠ 1 := by
    rw [← h.mul _ _ evC evD]
    have := h.ne_of (sec5cn_isEvenVec_add evC evD) sec5cn_isEvenVec_zero
      (by simpa using c1) (by simpa using c2)
    rwa [h.zero] at this
  have hu₁₂z : φ (sec5cnVec {4, 5}) * φ (sec5cnVec {4, 6}) ≠ z := by
    rw [hz, ← h.mul _ _ evC evD]
    exact h.ne_of (sec5cn_isEvenVec_add evC evD) hzE d1 d2
  by_contra hcon
  have key : ∀ u : G, u ∈ A ⊓ PP → u ≠ 1 → u ≠ z → (u = t ∨ u = t * z) := by
    intro u hu hu1 huz
    by_contra hn
    push_neg at hn
    exact hcon ⟨u, hu, hu1, huz, hn.1, hn.2⟩
  rcases sec5cn_mul_mem_pair ht2 hz2 htz
      (key _ ((hP _).mpr ⟨_, hC, rfl⟩) hu₁1 hu₁z) (key _ ((hP _).mpr ⟨_, hD, rfl⟩) hu₂1 hu₂z) with
    h1 | h1
  exacts [hu₁₂1 h1, hu₁₂z h1]

end CFSG.OddStandard.SmallF3.Omega

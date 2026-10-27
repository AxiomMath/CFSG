module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4HexLong

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.GH74.GLS.SP CFSG.GH74.BNPair

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem ActsPos.of_eq {n : ℕ} {m : X} {f g : ℤ → ℤ} (h : ActsPos n root m f)
    (hfg : ∀ q, f q = g q) : ActsPos n root m g := fun q x hx => by
  have := h q x hx
  rwa [hfg q] at this

theorem root_le_of_actsPos_inv {n : ℕ} {P : Subgroup X} {w : X} (hw : w ∈ P) {g : ℤ → ℤ}
    (hg : ActsPos n root w⁻¹ g) {q q' : ℤ} (hq : Rt n (g q') = Rt n q)
    (hP : root (Rt n q) ≤ P) : root (Rt n q') ≤ P := by
  intro x hx
  have h1 := hg q' x hx
  rw [hq] at h1
  have h2 := hP h1
  have e : x = w * (w⁻¹ * x * (w⁻¹)⁻¹) * w⁻¹ := by group
  rw [e]
  exact P.mul_mem (P.mul_mem hw h2) (P.inv_mem hw)

section Weyl

variable (R : RGD2 6 H r₁ r₂ U root)

include R in
theorem exists_weyl_long (P : Subgroup X) (h6 : root 6 ≤ P) (hm6 : root (-6) ≤ P) :
    ∃ w ∈ P, ActsPos 6 root w (fun q => 4 - q) ∧ ActsPos 6 root w⁻¹ (fun q => 4 - q) := by
  have hroot : IsRoot 6 (-6 : ℤ) := ⟨by norm_num, by norm_num⟩
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (R.ne_bot (-6) hroot)
  have hmem := R.rank₂ (y : X) y.2 (fun h => hy1 (Subtype.ext h))
  obtain ⟨u, hu, b, hb, hub⟩ := Set.mem_mul.1 hmem
  obtain ⟨v, hv, c, hc, hvc⟩ := Set.mem_mul.1 hu
  obtain ⟨a, ha, h, hh, hah⟩ := Set.mem_mul.1 hv
  rw [Set.mem_singleton_iff] at hc
  subst hc
  have hw : a⁻¹ * (y : X) * b⁻¹ = h * c := by
    rw [← hub, ← hvc, ← hah]
    group
  have hwP : a⁻¹ * (y : X) * b⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.inv_mem (h6 ha)) (hm6 y.2)) (P.inv_mem (h6 hb))
  rw [hw] at hwP
  refine ⟨h * c, hwP, ?_, ?_⟩
  · refine ActsPos.of_eq (ActsPos.mul (R.actsPos_of_mem_H hh) R.actsPos_r₂) fun q => ?_
    push_cast
    ring
  · rw [mul_inv_rev]
    refine ActsPos.of_eq (ActsPos.mul (R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂)
      (R.actsPos_of_mem_H (H.inv_mem hh))) fun q => ?_
    push_cast
    ring

theorem Rt6_values : Rt 6 0 = 1 ∧ Rt 6 2 = 3 ∧ Rt 6 4 = 5 ∧ Rt 6 6 = -1 ∧ Rt 6 8 = -3 ∧
    Rt 6 10 = -5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num

include R in
theorem exists_three_weyl :
    ∃ w₅ ∈ longSub 6 root, ∃ w₁ ∈ longSub 6 root, ∃ w₃ ∈ longSub 6 root,
      (ActsPos 6 root w₅ (fun q => 4 - q) ∧ ActsPos 6 root w₅⁻¹ (fun q => 4 - q)) ∧
      (ActsPos 6 root w₁ (fun q => 8 - q) ∧ ActsPos 6 root w₁⁻¹ (fun q => 8 - q)) ∧
      (ActsPos 6 root w₃ (fun q => -q) ∧ ActsPos 6 root w₃⁻¹ (fun q => -q)) := by
  have h6 : root 6 ≤ longSub 6 root :=
    root_le_longSub (⟨by norm_num, by norm_num⟩ : IsRoot 6 (6 : ℤ)) (by norm_num)
  have hm6 : root (-6) ≤ longSub 6 root :=
    root_le_longSub (⟨by norm_num, by norm_num⟩ : IsRoot 6 (-6 : ℤ)) (by norm_num)
  obtain ⟨w₅, hw₅, hf₅, hg₅⟩ := exists_weyl_long R (longSub 6 root) h6 hm6
  have hr₁ := R.goodActEven_r₁ (by norm_num : 6 % 2 = 0)
  have hr₂ := R.goodActEven_r₂ (by norm_num : 6 % 2 = 0)
  have hw₁ : r₁ * w₅ * r₁⁻¹ ∈ longSub 6 root :=
    conj_mem_longSub (by norm_num) (by norm_num) hr₁ hw₅
  have hw₃ : r₂ * (r₁ * w₅ * r₁⁻¹) * r₂⁻¹ ∈ longSub 6 root :=
    conj_mem_longSub (by norm_num) (by norm_num) hr₂ hw₁
  have a₁ : ActsPos 6 root r₁ (fun q => 6 - q) := by
    simpa using R.actsPos_r₁
  have a₁' : ActsPos 6 root r₁⁻¹ (fun q => 6 - q) := by
    simpa using R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁
  have a₂ : ActsPos 6 root r₂ (fun q => 4 - q) := by
    simpa using R.actsPos_r₂
  have a₂' : ActsPos 6 root r₂⁻¹ (fun q => 4 - q) := by
    simpa using R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂
  have c₁ : ActsPos 6 root (r₁ * w₅ * r₁⁻¹) (fun q => 8 - q) :=
    ActsPos.of_eq (ActsPos.mul (ActsPos.mul a₁ hf₅) a₁') fun q => by ring
  have c₁' : ActsPos 6 root (r₁ * w₅⁻¹ * r₁⁻¹) (fun q => 8 - q) :=
    ActsPos.of_eq (ActsPos.mul (ActsPos.mul a₁ hg₅) a₁') fun q => by ring
  have e₁ : (r₁ * w₅ * r₁⁻¹)⁻¹ = r₁ * w₅⁻¹ * r₁⁻¹ := by group
  have e₃ : (r₂ * (r₁ * w₅ * r₁⁻¹) * r₂⁻¹)⁻¹ = r₂ * (r₁ * w₅⁻¹ * r₁⁻¹) * r₂⁻¹ := by group
  refine ⟨w₅, hw₅, _, hw₁, _, hw₃, ⟨hf₅, hg₅⟩, ⟨c₁, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [e₁]; exact c₁'
  · exact ActsPos.of_eq (ActsPos.mul (ActsPos.mul a₂ c₁) a₂') fun q => by ring
  · rw [e₃]
    exact ActsPos.of_eq (ActsPos.mul (ActsPos.mul a₂ c₁') a₂') fun q => by ring

include R in
theorem root_five_le (P : Subgroup X) (hl : longSub 6 root ≤ P) (h0 : root 1 ≤ P) :
    root 5 ≤ P := by
  obtain ⟨w₅, hw₅, -, -, -, -, ⟨-, g₅⟩, -, -⟩ := exists_three_weyl R
  obtain ⟨v0, -, v4, -⟩ := Rt6_values
  have p0 : root (Rt 6 0) ≤ P := by rw [v0]; exact h0
  have := root_le_of_actsPos_inv (hl hw₅) g₅ (q := 0) (q' := 4)
    (by rw [show (4 : ℤ) - 4 = 0 by norm_num]) p0
  rwa [v4] at this

include R in
theorem root_le_of_two (P : Subgroup X) (hl : longSub 6 root ≤ P) (h0 : root 1 ≤ P)
    (h2 : root 3 ≤ P) : ∀ k : ℤ, IsRoot 6 k → root k ≤ P := by
  obtain ⟨w₅, hw₅, w₁, hw₁, w₃, hw₃, ⟨-, g₅⟩, ⟨-, g₁⟩, ⟨-, g₃⟩⟩ := exists_three_weyl R
  obtain ⟨v0, v2, v4, v6, v8, v10⟩ := Rt6_values
  have p0 : root (Rt 6 0) ≤ P := by rw [v0]; exact h0
  have p2 : root (Rt 6 2) ≤ P := by rw [v2]; exact h2
  intro k hk
  have hk1 := hk.1
  have hk2 : k.natAbs ≤ 6 := hk.2
  have hcases : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = -1 ∨ k = -3 ∨ k = -5 ∨ k % 2 = 0 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | hev
  · exact h0
  · exact h2
  · have := root_le_of_actsPos_inv (hl hw₅) g₅
      (q := 0) (q' := 4) (by rw [show (4 : ℤ) - 4 = 0 by norm_num]) p0
    rwa [v4] at this
  · have := root_le_of_actsPos_inv (hl hw₁) g₁ (q := 2) (q' := 6)
      (by rw [show (8 : ℤ) - 6 = 2 by norm_num]) p2
    rwa [v6] at this
  · have := root_le_of_actsPos_inv (hl hw₁) g₁ (q := 0) (q' := 8)
      (by rw [show (8 : ℤ) - 8 = 0 by norm_num]) p0
    rwa [v8] at this
  · have := root_le_of_actsPos_inv (hl hw₃) g₃ (q := 2) (q' := 10)
      (by
        have := Rt_add_mul 6 2 (-1)
        rw [show (2 : ℤ) + 2 * ((6 : ℕ) : ℤ) * (-1) = -10 by norm_num] at this
        simpa using this) p2
    rwa [v10] at this
  · exact (root_le_longSub hk hev).trans hl

end Weyl

section Centralizer

variable (R : RGD2 6 H r₁ r₂ U root)

theorem commute_conj_of_inv {z y m : X} (hz : z * m = m * z⁻¹) (hy : Commute z y) :
    Commute z (m * y * m⁻¹) := by
  have e1 : z * (m * y * m⁻¹) * z⁻¹ = (z * m) * y * (z * m)⁻¹ := by group
  have e2 : m * z⁻¹ * y * (m * z⁻¹)⁻¹ = m * (z⁻¹ * y * z) * m⁻¹ := by group
  have e3 : z⁻¹ * y * z = y := by
    rw [hy.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have e : z * (m * y * m⁻¹) * z⁻¹ = m * y * m⁻¹ := by
    rw [e1, hz, e2, e3]
  exact mul_inv_eq_iff_eq_mul.1 e

theorem commute_conj_of_commute {z y m : X} (hz : Commute z m) (hy : Commute z y) :
    Commute z (m * y * m⁻¹) :=
  (hz.mul_right hy).mul_right hz.inv_right

include R in
theorem commute_of_long (z : X) (h6 : ∀ x ∈ root 6, Commute z x)
    (hm6 : ∀ x ∈ root (-6), Commute z x) (hr₂ : Commute z r₂) (hr₁ : z * r₁ = r₁ * z⁻¹) :
    ∀ k : ℤ, IsRoot 6 k → k % 2 = 0 → ∀ x ∈ root k, Commute z x := by
  have a₁' : ActsPos 6 root r₁⁻¹ (fun q => 6 - q) := by
    simpa using R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁
  have a₂' : ActsPos 6 root r₂⁻¹ (fun q => 4 - q) := by
    simpa using R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂
  have via₁ : ∀ {q : ℤ} {x : X}, x ∈ root (Rt 6 q) →
      (∀ y ∈ root (Rt 6 (6 - q)), Commute z y) → Commute z x := by
    intro q x hx hy
    have h := a₁' q x hx
    have e : x = r₁ * (r₁⁻¹ * x * (r₁⁻¹)⁻¹) * r₁⁻¹ := by group
    rw [e]
    exact commute_conj_of_inv hr₁ (hy _ h)
  have via₂ : ∀ {q : ℤ} {x : X}, x ∈ root (Rt 6 q) →
      (∀ y ∈ root (Rt 6 (4 - q)), Commute z y) → Commute z x := by
    intro q x hx hy
    have h := a₂' q x hx
    have e : x = r₂ * (r₂⁻¹ * x * (r₂⁻¹)⁻¹) * r₂⁻¹ := by group
    rw [e]
    exact commute_conj_of_commute hr₂ (hy _ h)
  have v6 : Rt 6 5 = 6 := by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  have v2 : Rt 6 1 = 2 := by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  have v4 : Rt 6 3 = 4 := by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  have vm6 : Rt 6 11 = -6 := by rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num
  have vm2 : Rt 6 7 = -2 := by rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num
  have vm4 : Rt 6 9 = -4 := by rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num
  have c2 : ∀ x ∈ root 2, Commute z x := fun x hx => by
    refine via₁ (q := 1) (by rwa [v2]) fun y hy => ?_
    rw [show (6 : ℤ) - 1 = 5 by norm_num, v6] at hy
    exact h6 y hy
  have cm2 : ∀ x ∈ root (-2), Commute z x := fun x hx => by
    refine via₁ (q := 7) (by rwa [vm2]) fun y hy => ?_
    rw [show (6 : ℤ) - 7 = -1 by norm_num] at hy
    have : Rt 6 (-1) = Rt 6 11 := Rt_congr (by norm_num)
    rw [this, vm6] at hy
    exact hm6 y hy
  have c4 : ∀ x ∈ root 4, Commute z x := fun x hx => by
    refine via₂ (q := 3) (by rwa [v4]) fun y hy => ?_
    rw [show (4 : ℤ) - 3 = 1 by norm_num, v2] at hy
    exact c2 y hy
  have cm4 : ∀ x ∈ root (-4), Commute z x := fun x hx => by
    refine via₂ (q := 9) (by rwa [vm4]) fun y hy => ?_
    rw [show (4 : ℤ) - 9 = -5 by norm_num] at hy
    have : Rt 6 (-5) = Rt 6 7 := Rt_congr (by norm_num)
    rw [this, vm2] at hy
    exact cm2 y hy
  intro k hk hk2 x hx
  have hk1 := hk.1
  have hk3 : k.natAbs ≤ 6 := hk.2
  have : k = 6 ∨ k = -6 ∨ k = 2 ∨ k = -2 ∨ k = 4 ∨ k = -4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h6 x hx
  · exact hm6 x hx
  · exact c2 x hx
  · exact cm2 x hx
  · exact c4 x hx
  · exact cm4 x hx

include R in
theorem longSub_le_centralizer (z : X) (h6 : ∀ x ∈ root 6, Commute z x)
    (hm6 : ∀ x ∈ root (-6), Commute z x) (hr₂ : Commute z r₂) (hr₁ : z * r₁ = r₁ * z⁻¹) :
    longSub 6 root ≤ Subgroup.centralizer {z} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨k, hk, hk2, hx⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (commute_of_long R z h6 hm6 hr₂ hr₁ k hk hk2 x hx).eq.symm

end Centralizer

section Orbits

variable (R : RGD2 6 H r₁ r₂ U root)

include R in
theorem exists_nonzero_root_one (P : Subgroup X) (hl : longSub 6 root ≤ P) {k : ℤ}
    (hk : k = 1 ∨ k = 5 ∨ k = -3) {x : X} (hx : x ∈ root k) (hxP : x ∈ P) (hx1 : x ≠ 1) :
    ∃ y ∈ root 1, y ∈ P ∧ y ≠ 1 := by
  obtain ⟨w₅, hw₅, w₁, hw₁, -, -, ⟨-, g₅⟩, ⟨-, g₁⟩, -⟩ := exists_three_weyl R
  obtain ⟨v0, -, v4, -, v8, -⟩ := Rt6_values
  rcases hk with rfl | rfl | rfl
  · exact ⟨x, hx, hxP, hx1⟩
  · have h1 : w₅⁻¹ * x * (w₅⁻¹)⁻¹ ∈ root (Rt 6 (4 - 4)) :=
      g₅ 4 x (by rw [v4]; exact hx)
    rw [show (4 : ℤ) - 4 = 0 by norm_num, v0] at h1
    refine ⟨_, h1, ?_, ?_⟩
    · exact P.mul_mem (P.mul_mem (P.inv_mem (hl hw₅)) hxP) (by simpa using hl hw₅)
    · intro h
      apply hx1
      have : w₅ * (w₅⁻¹ * x * (w₅⁻¹)⁻¹) * w₅⁻¹ = x := by group
      rw [← this, h]; group
  · have h1 : w₁⁻¹ * x * (w₁⁻¹)⁻¹ ∈ root (Rt 6 (8 - 8)) :=
      g₁ 8 x (by rw [v8]; exact hx)
    rw [show (8 : ℤ) - 8 = 0 by norm_num, v0] at h1
    refine ⟨_, h1, ?_, ?_⟩
    · exact P.mul_mem (P.mul_mem (P.inv_mem (hl hw₁)) hxP) (by simpa using hl hw₁)
    · intro h
      apply hx1
      have : w₁ * (w₁⁻¹ * x * (w₁⁻¹)⁻¹) * w₁⁻¹ = x := by group
      rw [← this, h]; group

include R in
theorem exists_swap :
    ∃ w : X, GoodActEven 6 root w ∧ ActsPos 6 root w (fun q => 2 - q) ∧
      ActsPos 6 root w⁻¹ (fun q => 2 - q) ∧ (∀ h ∈ H, w * h * w⁻¹ ∈ H) := by
  have hr₁ := R.goodActEven_r₁ (by norm_num : 6 % 2 = 0)
  have hr₂ := R.goodActEven_r₂ (by norm_num : 6 % 2 = 0)
  have a₁ : ActsPos 6 root r₁ (fun q => 6 - q) := by simpa using R.actsPos_r₁
  have a₁' : ActsPos 6 root r₁⁻¹ (fun q => 6 - q) := by
    simpa using R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁
  have a₂ : ActsPos 6 root r₂ (fun q => 4 - q) := by simpa using R.actsPos_r₂
  have a₂' : ActsPos 6 root r₂⁻¹ (fun q => 4 - q) := by
    simpa using R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂
  refine ⟨r₂ * (r₁ * r₂), (hr₂.mul (hr₁.mul hr₂)), ?_, ?_, ?_⟩
  · exact ActsPos.of_eq (ActsPos.mul a₂ (ActsPos.mul a₁ a₂)) fun q => by ring
  · have e : (r₂ * (r₁ * r₂))⁻¹ = r₂⁻¹ * (r₁⁻¹ * r₂⁻¹) := by group
    rw [e]
    exact ActsPos.of_eq (ActsPos.mul a₂' (ActsPos.mul a₁' a₂')) fun q => by ring
  · intro h hh
    have e : r₂ * (r₁ * r₂) * h * (r₂ * (r₁ * r₂))⁻¹ =
        r₂ * (r₁ * (r₂ * h * r₂⁻¹) * r₁⁻¹) * r₂⁻¹ := by group
    rw [e]
    exact R.conj_H₂ _ (R.conj_H₁ _ (R.conj_H₂ _ hh))

end Orbits

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

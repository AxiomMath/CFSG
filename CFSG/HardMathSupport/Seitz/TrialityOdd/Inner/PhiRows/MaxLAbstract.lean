module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ClosingAbstract
public import CFSG.GH74.GLS.Stage4.HexCoord

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex

variable {X : Type*} [Group X]

theorem mem_chainProd_five (A : ℤ → Subgroup X) (y : X) :
    y ∈ chainProd A (intList 2 6) ↔ ∃ a₂ ∈ A 2, ∃ a₃ ∈ A 3, ∃ a₄ ∈ A 4, ∃ a₅ ∈ A 5, ∃ a₆ ∈ A 6,
      y = a₂ * (a₃ * (a₄ * (a₅ * a₆))) := by
  have hl : intList 2 6 = [2, 3, 4, 5, 6] := by decide
  rw [hl]
  simp only [chainProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Set.mem_mul,
    Set.mem_one, SetLike.mem_coe]
  constructor
  · rintro ⟨a₂, h₂, _, ⟨a₃, h₃, _, ⟨a₄, h₄, _, ⟨a₅, h₅, _, ⟨a₆, h₆, _, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, by simp⟩
  · rintro ⟨a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, rfl⟩
    exact ⟨a₂, h₂, _, ⟨a₃, h₃, _, ⟨a₄, h₄, _, ⟨a₅, h₅, _, ⟨a₆, h₆, 1, rfl, by simp⟩, rfl⟩, rfl⟩, rfl⟩,
      rfl⟩

section Move

variable {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}
  (R : RGD2 6 H r₁ r₂ U root)

include R in
theorem U_decomp {v : X} (hv : v ∈ U) :
    ∃ a₁ ∈ root 1, ∃ a₂ ∈ root 2, ∃ a₃ ∈ root 3, ∃ a₄ ∈ root 4, ∃ a₅ ∈ root 5, ∃ a₆ ∈ root 6,
      v = a₁ * (a₂ * (a₃ * (a₄ * (a₅ * a₆)))) := by
  have hv' : v ∈ chainProd root (intList 1 6) := by
    have h := R.carrier_eq
    simp only [Nat.cast_ofNat] at h
    rw [← h]; exact hv
  exact (mem_chainProd_six root v).1 hv'

include R in
theorem U_decomp_right {v : X} (hv : v ∈ U) :
    ∃ a ∈ root 1, ∃ c₂ ∈ root 2, ∃ c₃ ∈ root 3, ∃ c₄ ∈ root 4, ∃ c₅ ∈ root 5, ∃ c₆ ∈ root 6,
      v = (c₂ * (c₃ * (c₄ * (c₅ * c₆)))) * a := by
  obtain ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, rfl⟩ := U_decomp R hv
  obtain ⟨V, hV, -, hl, -⟩ := R.subgroup 2 6 (by norm_num) (by norm_num) (by norm_num)
  have hq : a₂ * (a₃ * (a₄ * (a₅ * a₆))) ∈ V := by
    have : a₂ * (a₃ * (a₄ * (a₅ * a₆))) ∈ chainProd root (intList 2 6) :=
      (mem_chainProd_five root _).2 ⟨a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, rfl⟩
    rw [← hV] at this
    exact this
  have h1 : a₁ * (a₂ * (a₃ * (a₄ * (a₅ * a₆)))) * a₁⁻¹ ∈ V := by
    have := hl (by norm_num) a₁ (by simpa using h₁) _ hq
    exact this
  have h1' : a₁ * (a₂ * (a₃ * (a₄ * (a₅ * a₆)))) * a₁⁻¹ ∈ chainProd root (intList 2 6) := by
    rw [← hV]; exact h1
  obtain ⟨c₂, hc₂, c₃, hc₃, c₄, hc₄, c₅, hc₅, c₆, hc₆, he⟩ := (mem_chainProd_five root _).1 h1'
  refine ⟨a₁, h₁, c₂, hc₂, c₃, hc₃, c₄, hc₄, c₅, hc₅, c₆, hc₆, ?_⟩
  rw [← he]; group

include R in
theorem actsPos_r₁' : ActsPos 6 root r₁ (fun q => 6 - q) := by simpa using R.actsPos_r₁

include R in
theorem actsPos_r₂' : ActsPos 6 root r₂ (fun q => 4 - q) := by simpa using R.actsPos_r₂

include R in
theorem actsPos_r₁_inv' : ActsPos 6 root r₁⁻¹ (fun q => 6 - q) := by
  simpa using R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁

include R in
theorem actsPos_r₂_inv' : ActsPos 6 root r₂⁻¹ (fun q => 4 - q) := by
  simpa using R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂

theorem Rt6_small : Rt 6 0 = 1 ∧ Rt 6 1 = 2 ∧ Rt 6 2 = 3 ∧ Rt 6 3 = 4 ∧ Rt 6 4 = 5 ∧ Rt 6 5 = 6 ∧
    Rt 6 6 = -1 ∧ Rt 6 (-1) = -6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_neg (by norm_num) (by norm_num)]; norm_num

include R in
theorem move_r₂ {k k' : ℤ} (hk : ∀ y ∈ root k, r₂ * y * r₂⁻¹ ∈ root k')
    (hc : ∀ b ∈ root (-6), ∀ z ∈ root k', b * z = z * b) {v : X} (hv : v ∈ U) :
    ∃ v' ∈ U, ∀ y ∈ root k, r₂ * (v * y * v⁻¹) * r₂⁻¹ = v' * (r₂ * y * r₂⁻¹) * v'⁻¹ := by
  obtain ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, rfl⟩ := U_decomp R hv
  obtain ⟨-, -, -, -, -, -, -, hm1⟩ := Rt6_small
  have a₂c := actsPos_r₂' R
  have move : ∀ (q : ℤ) (j : ℤ) (x : X), Rt 6 q = j → x ∈ root j → ∀ j', Rt 6 (4 - q) = j' →
      r₂ * x * r₂⁻¹ ∈ root j' := by
    intro q j x hq hx j' hj'
    have := a₂c q x (by rw [hq]; exact hx)
    rwa [hj'] at this
  obtain ⟨-, -, -, -, -, -, -, -⟩ := Rt6_small
  have e1 : r₂ * a₁ * r₂⁻¹ ∈ root 5 := move 0 1 a₁ (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num) h₁ 5 (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num)
  have e2 : r₂ * a₂ * r₂⁻¹ ∈ root 4 := move 1 2 a₂ (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num) h₂ 4 (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num)
  have e3 : r₂ * a₃ * r₂⁻¹ ∈ root 3 := move 2 3 a₃ (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num) h₃ 3 (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num)
  have e4 : r₂ * a₄ * r₂⁻¹ ∈ root 2 := move 3 4 a₄ (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num) h₄ 2 (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num)
  have e5 : r₂ * a₅ * r₂⁻¹ ∈ root 1 := move 4 5 a₅ (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num) h₅ 1 (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num)
  have e6 : r₂ * a₆ * r₂⁻¹ ∈ root (-6) := move 5 6 a₆ (by rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num) h₆ (-6) (by rw [show (4 : ℤ) - 5 = -1 by norm_num]; exact hm1)
  have u5 : ∀ {j : ℤ}, 1 ≤ j → j ≤ 6 → ∀ x ∈ root j, x ∈ U := fun hj1 hj6 x hx =>
    R.root_le_U hj1 hj6 hx
  refine ⟨(r₂ * a₁ * r₂⁻¹) * ((r₂ * a₂ * r₂⁻¹) * ((r₂ * a₃ * r₂⁻¹) *
    ((r₂ * a₄ * r₂⁻¹) * (r₂ * a₅ * r₂⁻¹)))), ?_, ?_⟩
  · exact mul_mem (u5 (by norm_num) (by norm_num) _ e1) (mul_mem (u5 (by norm_num) (by norm_num) _ e2)
      (mul_mem (u5 (by norm_num) (by norm_num) _ e3) (mul_mem (u5 (by norm_num) (by norm_num) _ e4)
        (u5 (by norm_num) (by norm_num) _ e5))))
  · intro y hy
    have hz := hk y hy
    have hb := hc _ e6 _ hz
    calc r₂ * (a₁ * (a₂ * (a₃ * (a₄ * (a₅ * a₆)))) * y * (a₁ * (a₂ * (a₃ * (a₄ * (a₅ * a₆)))))⁻¹) * r₂⁻¹
        = ((r₂ * a₁ * r₂⁻¹) * ((r₂ * a₂ * r₂⁻¹) * ((r₂ * a₃ * r₂⁻¹) *
          ((r₂ * a₄ * r₂⁻¹) * (r₂ * a₅ * r₂⁻¹))))) * ((r₂ * a₆ * r₂⁻¹) * (r₂ * y * r₂⁻¹) *
            (r₂ * a₆ * r₂⁻¹)⁻¹) * ((r₂ * a₁ * r₂⁻¹) * ((r₂ * a₂ * r₂⁻¹) * ((r₂ * a₃ * r₂⁻¹) *
          ((r₂ * a₄ * r₂⁻¹) * (r₂ * a₅ * r₂⁻¹)))))⁻¹ := by group
      _ = _ := by
        have : (r₂ * a₆ * r₂⁻¹) * (r₂ * y * r₂⁻¹) * (r₂ * a₆ * r₂⁻¹)⁻¹ = r₂ * y * r₂⁻¹ := by
          rw [hb]; group
        rw [this]

include R in
theorem move_r₁ {k k' : ℤ} (hk : ∀ y ∈ root k, r₁ * y * r₁⁻¹ ∈ root k')
    (hc : ∀ b ∈ root (-1), ∀ z ∈ root k', b * z = z * b) {v : X} (hv : v ∈ U) :
    ∃ v' ∈ U, ∀ y ∈ root k, r₁ * (v * y * v⁻¹) * r₁⁻¹ = v' * (r₁ * y * r₁⁻¹) * v'⁻¹ := by
  obtain ⟨a, ha, c₂, h₂, c₃, h₃, c₄, h₄, c₅, h₅, c₆, h₆, rfl⟩ := U_decomp_right R hv
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, -⟩ := Rt6_small
  have a₁c := actsPos_r₁' R
  have move : ∀ (q : ℤ) (j : ℤ) (x : X), Rt 6 q = j → x ∈ root j → ∀ j', Rt 6 (6 - q) = j' →
      r₁ * x * r₁⁻¹ ∈ root j' := by
    intro q j x hq hx j' hj'
    have := a₁c q x (by rw [hq]; exact hx)
    rwa [hj'] at this
  have e0 : r₁ * a * r₁⁻¹ ∈ root (-1) :=
    move 0 1 a r0 ha (-1) (by rw [show (6 : ℤ) - 0 = 6 by norm_num]; exact r6)
  have e2 : r₁ * c₂ * r₁⁻¹ ∈ root 6 := move 1 2 c₂ r1 h₂ 6 (by rw [show (6 : ℤ) - 1 = 5 by norm_num]; exact r5)
  have e3 : r₁ * c₃ * r₁⁻¹ ∈ root 5 := move 2 3 c₃ r2 h₃ 5 (by rw [show (6 : ℤ) - 2 = 4 by norm_num]; exact r4)
  have e4 : r₁ * c₄ * r₁⁻¹ ∈ root 4 := move 3 4 c₄ r3 h₄ 4 (by rw [show (6 : ℤ) - 3 = 3 by norm_num]; exact r3)
  have e5 : r₁ * c₅ * r₁⁻¹ ∈ root 3 := move 4 5 c₅ r4 h₅ 3 (by rw [show (6 : ℤ) - 4 = 2 by norm_num]; exact r2)
  have e6 : r₁ * c₆ * r₁⁻¹ ∈ root 2 := move 5 6 c₆ r5 h₆ 2 (by rw [show (6 : ℤ) - 5 = 1 by norm_num]; exact r1)
  have u5 : ∀ {j : ℤ}, 1 ≤ j → j ≤ 6 → ∀ x ∈ root j, x ∈ U := fun hj1 hj6 x hx =>
    R.root_le_U hj1 hj6 hx
  refine ⟨(r₁ * c₂ * r₁⁻¹) * ((r₁ * c₃ * r₁⁻¹) * ((r₁ * c₄ * r₁⁻¹) *
    ((r₁ * c₅ * r₁⁻¹) * (r₁ * c₆ * r₁⁻¹)))), ?_, ?_⟩
  · exact mul_mem (u5 (by norm_num) (by norm_num) _ e2) (mul_mem (u5 (by norm_num) (by norm_num) _ e3)
      (mul_mem (u5 (by norm_num) (by norm_num) _ e4) (mul_mem (u5 (by norm_num) (by norm_num) _ e5)
        (u5 (by norm_num) (by norm_num) _ e6))))
  · intro y hy
    have hz := hk y hy
    have hb := hc _ e0 _ hz
    calc r₁ * ((c₂ * (c₃ * (c₄ * (c₅ * c₆)))) * a * y * ((c₂ * (c₃ * (c₄ * (c₅ * c₆)))) * a)⁻¹) *
          r₁⁻¹
        = ((r₁ * c₂ * r₁⁻¹) * ((r₁ * c₃ * r₁⁻¹) * ((r₁ * c₄ * r₁⁻¹) *
          ((r₁ * c₅ * r₁⁻¹) * (r₁ * c₆ * r₁⁻¹))))) * ((r₁ * a * r₁⁻¹) * (r₁ * y * r₁⁻¹) *
            (r₁ * a * r₁⁻¹)⁻¹) * ((r₁ * c₂ * r₁⁻¹) * ((r₁ * c₃ * r₁⁻¹) * ((r₁ * c₄ * r₁⁻¹) *
          ((r₁ * c₅ * r₁⁻¹) * (r₁ * c₆ * r₁⁻¹)))))⁻¹ := by group
      _ = _ := by
        have : (r₁ * a * r₁⁻¹) * (r₁ * y * r₁⁻¹) * (r₁ * a * r₁⁻¹)⁻¹ = r₁ * y * r₁⁻¹ := by
          rw [hb]; group
        rw [this]

omit R in
theorem actsPos_root {m : X} {f : ℤ → ℤ} (hm : ActsPos 6 root m f) {q k k' : ℤ} (hk : Rt 6 q = k)
    (hk' : Rt 6 (f q) = k') {x : X} (hx : x ∈ root k) : m * x * m⁻¹ ∈ root k' := by
  have := hm q x (by rw [hk]; exact hx)
  rwa [hk'] at this

omit R in
theorem commute_transfer {m : X} {g : ℤ → ℤ} (hm : ActsPos 6 root m g) {q₁ q₂ p₁ p₂ : ℤ}
    (h1 : Rt 6 (g q₁) = Rt 6 p₁) (h2 : Rt 6 (g q₂) = Rt 6 p₂)
    (hc : ∀ x ∈ root (Rt 6 p₁), ∀ y ∈ root (Rt 6 p₂), x * y = y * x) :
    ∀ x ∈ root (Rt 6 q₁), ∀ y ∈ root (Rt 6 q₂), x * y = y * x := by
  intro x hx y hy
  have hx0 := actsPos_root hm rfl h1 hx
  have hy0 := actsPos_root hm rfl h2 hy
  have := hc _ hx0 _ hy0
  have e : m * (x * y) * m⁻¹ = m * (y * x) * m⁻¹ := by
    calc m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
      _ = (m * y * m⁻¹) * (m * x * m⁻¹) := this
      _ = m * (y * x) * m⁻¹ := by group
  have := mul_left_cancel (mul_right_cancel e)
  exact this

include R in
theorem actsPos_rot_two : ActsPos 6 root (r₂ * r₁) (fun q => q - 2) ∧
    ActsPos 6 root (r₂ * r₁)⁻¹ (fun q => q + 2) := by
  have a₁ := actsPos_r₁' R
  have a₁' := actsPos_r₁_inv' R
  have a₂ := actsPos_r₂' R
  have a₂' := actsPos_r₂_inv' R
  refine ⟨ActsPos.of_eq (ActsPos.mul a₂ a₁) fun q => by ring, ?_⟩
  rw [mul_inv_rev]
  exact ActsPos.of_eq (ActsPos.mul a₁' a₂') fun q => by ring

include R in
theorem actsPos_rot_six :
    ActsPos 6 root ((r₂ * r₁) * ((r₂ * r₁) * (r₂ * r₁))) (fun q => q - 6) := by
  obtain ⟨h, -⟩ := actsPos_rot_two R
  exact ActsPos.of_eq (ActsPos.mul h (ActsPos.mul h h)) fun q => by ring

theorem exists_pos_of_isRoot {k : ℤ} (hk : IsRoot 6 k) : ∃ q : ℤ, Rt 6 q = k := by
  by_cases hpos : 0 < k
  · exact ⟨k - 1, by rw [Rt_of_lt (by have := hk.1; omega) (by have := hk.2; omega)]; ring⟩
  · have hk3 : k < 0 := by have := hk.1; omega
    have hk4 : -(6 : ℤ) ≤ k := by have := hk.2; omega
    refine ⟨(6 : ℤ) - k - 1, ?_⟩
    rw [Rt_of_ge (by omega) (by omega)]
    ring

include R in
theorem exists_conj_to_four {k : ℤ} (hk : IsRoot 6 k) (hk2 : k % 2 = 0) :
    ∃ m ∈ longSub 6 root, ∀ y ∈ root k, m * y * m⁻¹ ∈ root 4 := by
  obtain ⟨w₅, hw₅, w₁, hw₁, w₃, hw₃, ⟨a₅, -⟩, ⟨a₁, -⟩, ⟨a₃, -⟩⟩ := exists_three_weyl R
  have hk' : -6 ≤ k ∧ k ≤ 6 ∧ k ≠ 0 := by
    have h1 := hk.1; have h2 := hk.2; omega
  obtain ⟨hl, hu, hne⟩ := hk'
  have h1 : ∀ {m : X} {f : ℤ → ℤ}, ActsPos 6 root m f → ∀ {q : ℤ}, Rt 6 q = k → Rt 6 (f q) = 4 →
      ∀ y ∈ root k, m * y * m⁻¹ ∈ root 4 := fun hm q hq hq' y hy => actsPos_root hm hq hq' hy
  interval_cases k <;> first | omega | skip
  ·
    refine ⟨w₁ * w₅, mul_mem hw₁ hw₅, h1 (ActsPos.mul a₁ a₅) (q := 11) (by decide) (by decide)⟩
  ·
    exact ⟨w₃, hw₃, h1 a₃ (q := 9) (by decide) (by decide)⟩
  ·
    refine ⟨w₅ * w₁, mul_mem hw₅ hw₁, h1 (ActsPos.mul a₅ a₁) (q := 7) (by decide) (by decide)⟩
  ·
    exact ⟨w₅, hw₅, h1 a₅ (q := 1) (by decide) (by decide)⟩
  ·
    exact ⟨1, one_mem _, fun y hy => by simpa using hy⟩
  ·
    exact ⟨w₁, hw₁, h1 a₁ (q := 5) (by decide) (by decide)⟩

end Move

section Chain

variable {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}

@[expose] def PLset (root : ℤ → Subgroup X) : Set X :=
  {z | ∃ ℓ ∈ longSub 6 root, ∃ k : ℤ, IsRoot 6 k ∧ k % 2 = 0 ∧ ∃ y ∈ root k, z = ℓ * y * ℓ⁻¹}

theorem PLset_conj {m : X} (hm : GoodActEven 6 root m) {z : X} (hz : z ∈ PLset root) :
    m * z * m⁻¹ ∈ PLset root := by
  obtain ⟨ℓ, hℓ, k, hk, hk2, y, hy, rfl⟩ := hz
  obtain ⟨f, g, hf, hg, hmf, hmg⟩ := hm
  obtain ⟨q, hq⟩ := exists_pos_of_isRoot hk
  have hqodd : q % 2 = 1 := (Rt_even_iff (by norm_num) q).1 (hq ▸ hk2)
  refine ⟨m * ℓ * m⁻¹, conj_mem_longSub (by norm_num) (by norm_num) ⟨f, g, hf, hg, hmf, hmg⟩ hℓ,
    Rt 6 (f q), Rt_isRoot (by norm_num) _, ?_, m * y * m⁻¹, hmf q y (hq ▸ hy), by group⟩
  rw [Rt_even_iff (by norm_num), hf.parity]
  exact hqodd

@[expose] def PointClosed (H : Subgroup X) (U : Subgroup X) (root : ℤ → Subgroup X) (k : ℤ) : Prop :=
  ∀ H₀ : Subgroup X, longSub 6 root ≤ H₀ → H ≤ H₀ → ∀ v ∈ U, (∀ y ∈ root k, v * y * v⁻¹ ∈ H₀) →
    (∃ y ∈ root k, v * y * v⁻¹ ∉ PLset root) → H₀ = ⊤

theorem PointClosed_of_move {r : X} {k k' : ℤ}
    (hr : GoodActEven 6 root r) (hrH : ∀ t ∈ H, r⁻¹ * t * r ∈ H)
    (hk : ∀ y ∈ root k, r * y * r⁻¹ ∈ root k') (hk' : ∀ z ∈ root k', r⁻¹ * z * r ∈ root k)
    (hmove : ∀ v ∈ U, ∃ v' ∈ U, ∀ y ∈ root k, r * (v * y * v⁻¹) * r⁻¹ = v' * (r * y * r⁻¹) * v'⁻¹)
    (hS : PointClosed H U root k') : PointClosed H U root k := by
  intro H₀ hL hT v hv hH hnP
  obtain ⟨v', hv', hvv⟩ := hmove v hv
  set H₁ : Subgroup X := H₀.map (MulAut.conj r).toMonoidHom with hH₁
  have memH₁ : ∀ z, r⁻¹ * z * r ∈ H₀ → z ∈ H₁ := fun z hz =>
    ⟨r⁻¹ * z * r, hz, by show r * (r⁻¹ * z * r) * r⁻¹ = z; group⟩
  have hL₁ : longSub 6 root ≤ H₁ := fun ℓ hℓ => by
    have h1 := conj_mem_longSub (by norm_num) (by norm_num) hr.inv hℓ
    rw [inv_inv] at h1
    exact memH₁ ℓ (hL h1)
  have hT₁ : H ≤ H₁ := fun t ht => memH₁ t (hT (hrH t ht))
  have hS₁ := hS H₁ hL₁ hT₁ v' hv'
  have hres : (∀ z ∈ root k', v' * z * v'⁻¹ ∈ H₁) := by
    intro z hz
    have hy := hk' z hz
    have e : v' * z * v'⁻¹ = r * (v * (r⁻¹ * z * r) * v⁻¹) * r⁻¹ := by
      rw [hvv _ hy]; group
    rw [e]
    exact ⟨_, hH _ hy, rfl⟩
  obtain ⟨y₀, hy₀, hy₀n⟩ := hnP
  have hz₀ := hk y₀ hy₀
  have hn : v' * (r * y₀ * r⁻¹) * v'⁻¹ ∉ PLset root := by
    intro hmem
    apply hy₀n
    have e : r * (v * y₀ * v⁻¹) * r⁻¹ = v' * (r * y₀ * r⁻¹) * v'⁻¹ := hvv y₀ hy₀
    rw [← e] at hmem
    have := PLset_conj hr.inv hmem
    simpa [mul_assoc] using this
  have htop := hS₁ hres ⟨_, hz₀, hn⟩
  refine eq_top_iff.2 fun g _ => ?_
  have : r * g * r⁻¹ ∈ H₁ := by rw [htop]; trivial
  obtain ⟨g', hg', hgg⟩ := this
  have : g' = g := by
    have h2 : r * g' * r⁻¹ = r * g * r⁻¹ := hgg
    exact mul_left_cancel (mul_right_cancel h2)
  rw [← this]
  exact hg'

theorem torus_conj_inv {r : X} (hsq : r * r ∈ H) (hconj : ∀ h ∈ H, r * h * r⁻¹ ∈ H)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : ∀ t ∈ H, r⁻¹ * t * r ∈ H := by
  intro t ht
  have e : r⁻¹ * t * r = r * ((r * r)⁻¹ * t * (r * r)) * r⁻¹ := by group
  have h1 : (r * r)⁻¹ * t * (r * r) = t := by
    have := hcomm t ht (r * r) hsq
    calc (r * r)⁻¹ * t * (r * r) = (r * r)⁻¹ * (t * (r * r)) := by group
      _ = (r * r)⁻¹ * ((r * r) * t) := by rw [this]
      _ = t := by group
  rw [e, h1]
  exact hconj t ht

variable (R : RGD2 6 H r₁ r₂ U root)

include R in
theorem pointClosed_chain
    (c66 : ∀ b ∈ root (-6), ∀ z ∈ root (-6), b * z = z * b)
    (c64 : ∀ b ∈ root (-6), ∀ z ∈ root (-4), b * z = z * b)
    (c16 : ∀ b ∈ root (-1), ∀ z ∈ root 6, b * z = z * b)
    (c12 : ∀ b ∈ root (-1), ∀ z ∈ root (-2), b * z = z * b)
    (hS4 : PointClosed H U root (-4)) :
    PointClosed H U root (-2) ∧ PointClosed H U root (-6) ∧ PointClosed H U root 6 ∧
      PointClosed H U root 2 := by
  have hr₁ := R.goodActEven_r₁ (by norm_num : 6 % 2 = 0)
  have hr₂ := R.goodActEven_r₂ (by norm_num : 6 % 2 = 0)
  have hH₁ := torus_conj_inv R.sq₁ R.conj_H₁ R.comm_H
  have hH₂ := torus_conj_inv R.sq₂ R.conj_H₂ R.comm_H
  have a₁ := actsPos_r₁' R
  have a₁' := actsPos_r₁_inv' R
  have a₂ := actsPos_r₂' R
  have a₂' := actsPos_r₂_inv' R
  have p24 : PointClosed H U root (-2) := by
    have hk : ∀ y ∈ root (-2), r₂ * y * r₂⁻¹ ∈ root (-4) := fun y hy =>
      actsPos_root a₂ (q := 7) (k := -2) (k' := -4) (by decide) (by decide) hy
    have hk' : ∀ z ∈ root (-4), r₂⁻¹ * z * r₂ ∈ root (-2) := fun z hz => by
      have := actsPos_root a₂' (q := 9) (k := -4) (k' := -2) (by decide) (by decide) hz
      rwa [inv_inv] at this
    exact PointClosed_of_move hr₂ hH₂ hk hk' (fun v hv => move_r₂ R hk c64 hv) hS4
  have p62 : PointClosed H U root (-6) := by
    have hk : ∀ y ∈ root (-6), r₁ * y * r₁⁻¹ ∈ root (-2) := fun y hy =>
      actsPos_root a₁ (q := 11) (k := -6) (k' := -2) (by decide) (by decide) hy
    have hk' : ∀ z ∈ root (-2), r₁⁻¹ * z * r₁ ∈ root (-6) := fun z hz => by
      have := actsPos_root a₁' (q := 7) (k := -2) (k' := -6) (by decide) (by decide) hz
      rwa [inv_inv] at this
    exact PointClosed_of_move hr₁ hH₁ hk hk' (fun v hv => move_r₁ R hk c12 hv) p24
  have p6 : PointClosed H U root 6 := by
    have hk : ∀ y ∈ root 6, r₂ * y * r₂⁻¹ ∈ root (-6) := fun y hy =>
      actsPos_root a₂ (q := 5) (k := 6) (k' := -6) (by decide) (by decide) hy
    have hk' : ∀ z ∈ root (-6), r₂⁻¹ * z * r₂ ∈ root 6 := fun z hz => by
      have := actsPos_root a₂' (q := 11) (k := -6) (k' := 6) (by decide) (by decide) hz
      rwa [inv_inv] at this
    exact PointClosed_of_move hr₂ hH₂ hk hk' (fun v hv => move_r₂ R hk c66 hv) p62
  have p2 : PointClosed H U root 2 := by
    have hk : ∀ y ∈ root 2, r₁ * y * r₁⁻¹ ∈ root 6 := fun y hy =>
      actsPos_root a₁ (q := 1) (k := 2) (k' := 6) (by decide) (by decide) hy
    have hk' : ∀ z ∈ root 6, r₁⁻¹ * z * r₁ ∈ root 2 := fun z hz => by
      have := actsPos_root a₁' (q := 5) (k := 6) (k' := 2) (by decide) (by decide) hz
      rwa [inv_inv] at this
    exact PointClosed_of_move hr₁ hH₁ hk hk' (fun v hv => move_r₁ R hk c16 hv) p6
  exact ⟨p24, p62, p6, p2⟩

end Chain


end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

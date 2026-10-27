module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B4End

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section N₂Action

theorem mat_N₂sub_mul_e₁ {n : hypSU h 2 1} (hn : n ∈ N₂sub h)
    (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (l : HypIndex 2 1) :
    (mat n * M) ιe₁ l = M ιe₁ l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun k _ hk => by
      rw [(N₂sub_rows hn k).1, one_apply_ne (Ne.symm hk), zero_mul]) (by simp),
    (N₂sub_rows hn _).1, one_apply_eq, one_mul]

theorem mat_conj_N₂sub_e₁ {n : hypSU h 2 1} (hn : n ∈ N₂sub h) (g : hypSU h 2 1)
    (j : HypIndex 2 1) : mat (n * g * n⁻¹) ιe₁ j = ∑ l, mat g ιe₁ l * mat n⁻¹ l j := by
  rw [mat_mul, mat_mul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [mat_N₂sub_mul_e₁ hn]

theorem conj_N₂sub_mem_A₂sub {n g : hypSU h 2 1} (hn : n ∈ N₂sub h) (hg : g ∈ A₂sub h) :
    n * g * n⁻¹ ∈ A₂sub h := by
  rw [mem_A₂sub_iff, mat_mul, mat_mul]
  refine isFlagUni_mul_mul ιe₁_ne_ιf₁ (by rw [← mat_mul, mul_inv_cancel, mat_one])
    (by rw [← mat_mul, inv_mul_cancel, mat_one]) (fun c hc => ?_) (fun k hk => ?_)
    (mem_A₂sub_iff.1 hg)
  · rw [(mem_N₂sub.1 hn).1 c, one_apply_ne hc]
  · rw [(N₂sub_rows hn k).2, one_apply_ne (Ne.symm hk)]

end N₂Action

section Generation

theorem conj_mem_closure_conj_Z₂Psub {m x : hypSU h 2 1} (hm : m ∈ N₂sub h)
    (hx : x ∈ closure {y | ∃ n ∈ N₂sub h, ∃ w ∈ Z₂Psub h, y = n * w * n⁻¹}) :
    m * x * m⁻¹ ∈ closure {y | ∃ n ∈ N₂sub h, ∃ w ∈ Z₂Psub h, y = n * w * n⁻¹} := by
  set X := closure {y | ∃ n ∈ N₂sub h, ∃ w ∈ Z₂Psub h, y = n * w * n⁻¹}
  have hle : X ≤ X.comap (MulAut.conj m).toMonoidHom := by
    refine (closure_le _).2 fun y ⟨n, hn, w, hw, hy⟩ => ?_
    change m * y * m⁻¹ ∈ X
    rw [hy, show m * (n * w * n⁻¹) * m⁻¹ = (m * n) * w * (m * n)⁻¹ by group]
    exact subset_closure ⟨m * n, mul_mem hm hn, w, hw, rfl⟩
  exact hle hx

theorem A₂sub_le_closure_conj_Z₂Psub :
    A₂sub h ≤ closure {y | ∃ n ∈ N₂sub h, ∃ w ∈ Z₂Psub h, y = n * w * n⁻¹} := by
  have := h.charP
  set X := closure {y | ∃ n ∈ N₂sub h, ∃ w ∈ Z₂Psub h, y = n * w * n⁻¹} with hX
  have hconj : ∀ n ∈ N₂sub h, ∀ w ∈ Z₂Psub h, n * w * n⁻¹ ∈ X := fun n hn w hw =>
    subset_closure ⟨n, hn, w, hw, rfl⟩
  have hZ₂ : ∀ w ∈ Z₂Psub h, w ∈ X := fun w hw => by
    simpa using hconj 1 (one_mem _) w hw
  have h2 : ∀ a : K, a + a = 0 := CharTwo.add_self_eq_zero
  have hs : ∀ c : K, ∃ y ∈ X, y ∈ A₂sub h ∧ mat y ιe₁ ιe₂ = c ∧ mat y ιe₁ ιz = 0 ∧
      mat y ιe₁ ιf₂ = 0 := by
    intro c
    obtain ⟨w, hwA, e1, e2, e3⟩ := exists_A₂sub_coord h 0 0 c
    have hwZ := mem_Z₂Psub_of_A₂ hwA e1 e2
    refine ⟨sSU h * w * (sSU h)⁻¹, hconj _ sSU_mem_N₂sub w hwZ,
      conj_N₂sub_mem_A₂sub sSU_mem_N₂sub hwA, ?_, ?_, ?_⟩
    · rw [conj_sSU_apply, show σs ιe₁ = ιe₁ by decide, show σs ιe₂ = ιf₂ by decide, e3]
    · rw [conj_sSU_apply, show σs ιe₁ = ιe₁ by decide, show σs ιz = ιz by decide, e2]
    · rw [conj_sSU_apply, show σs ιe₁ = ιe₁ by decide, show σs ιf₂ = ιe₂ by decide, e1]
  have hβ : ∀ β : K, ∃ y ∈ X, y ∈ A₂sub h ∧ mat y ιe₁ ιe₂ = 0 ∧ mat y ιe₁ ιz = β := by
    intro β
    obtain ⟨y, hyX, hyA, y1, y2, y3⟩ := hs 1
    obtain ⟨d, hd⟩ := trace_surj (hK := h) (a := β * h.bar β)
      (by rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨g, hg, g1, g2⟩ := exists_rootI₂ h hd
    have hgN := patSub_sI₂_le_N₂sub hg
    obtain ⟨hgU, k1, -, k3, -, k5, -, -⟩ := mem_patSub_sI₂.1 hg
    obtain ⟨⟨-, d2, d3, -, -⟩, ⟨-, -, -, l4, l5, l6, l7, l8, l9, -⟩⟩ := U_entries hgU
    obtain ⟨-, -, -, a3⟩ := mem_A₂sub.1 hyA
    have hxA := conj_N₂sub_mem_A₂sub (inv_mem hgN) hyA
    have hxX := conj_mem_closure_conj_Z₂Psub (inv_mem hgN) hyX
    have hx : ∀ j, mat (g⁻¹ * y * g⁻¹⁻¹) ιe₁ j = mat y ιe₁ ιe₁ * mat g ιe₁ j +
        mat y ιe₁ ιe₂ * mat g ιe₂ j + mat y ιe₁ ιz * mat g ιz j +
        mat y ιe₁ ιf₁ * mat g ιf₁ j + mat y ιe₁ ιf₂ * mat g ιf₂ j := fun j => by
      rw [mat_conj_N₂sub_e₁ (inv_mem hgN), sum_hypIndex_two, inv_inv]
    obtain ⟨m1, m2, -⟩ := A₂_inv_mul hyA hxA
    refine ⟨y⁻¹ * (g⁻¹ * y * g⁻¹⁻¹), mul_mem (inv_mem hyX) hxX, mul_mem (inv_mem hyA) hxA, ?_, ?_⟩
    · rw [m1, hx, y1, y2, y3, k1, d2, l5, l7, l6]
      simp only [mul_zero, one_mul, add_zero, zero_add]
      exact h2 1
    · rw [m2, hx, y1, y2, y3, k3, g1, d3, l9, l8]
      simp only [mul_zero, zero_mul, one_mul, add_zero, zero_add]
  intro a ha
  obtain ⟨y₁, hy₁X, hy₁A, p1, p2, -⟩ := hs (mat a ιe₁ ιe₂)
  obtain ⟨y₂, hy₂X, hy₂A, q1, q2⟩ := hβ (mat a ιe₁ ιz)
  have hyA := mul_mem hy₁A hy₂A
  obtain ⟨r1, r2, -⟩ := A₂_mul hy₁A hy₂A
  obtain ⟨s1, s2, -⟩ := A₂_inv_mul ha hyA
  have hZ : a⁻¹ * (y₁ * y₂) ∈ Z₂Psub h := mem_Z₂Psub_of_A₂ (mul_mem (inv_mem ha) hyA)
    (by rw [s1, r1, p1, q1, add_zero, h2]) (by rw [s2, r2, p2, q2, zero_add, h2])
  have e : a = (y₁ * y₂) * (a⁻¹ * (y₁ * y₂))⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hy₁X hy₂X) (inv_mem (hZ₂ _ hZ))

end Generation

section Commutators

theorem mul_comm_iff_coord {m a : hypSU h 2 1} (hm : m ∈ A₂sub h) (ha : a ∈ A₂sub h) :
    m * a = a * m ↔
      mat m ιe₁ ιe₂ * h.bar (mat a ιe₁ ιf₂) + mat m ιe₁ ιz * h.bar (mat a ιe₁ ιz) +
          mat m ιe₁ ιf₂ * h.bar (mat a ιe₁ ιe₂) =
        h.bar (mat m ιe₁ ιe₂ * h.bar (mat a ιe₁ ιf₂) + mat m ιe₁ ιz * h.bar (mat a ιe₁ ιz) +
          mat m ιe₁ ιf₂ * h.bar (mat a ιe₁ ιe₂)) := by
  rw [A₂_mul_comm_iff hm ha]
  simp only [map_add, map_mul, h.bar_bar]
  constructor <;> intro e <;> linear_combination e

theorem exists_A₂sub_not_comm (hf : 2 ≤ f) {a : hypSU h 2 1} (ha : a ∈ A₂sub h)
    (haZ : a ∉ ZPsub h) : ∃ m₁ ∈ A₂sub h, ∃ m₂ ∈ A₂sub h, m₁ * a ≠ a * m₁ ∧
      m₂ * a ≠ a * m₂ ∧ m₁ * a * m₁⁻¹ ≠ m₂ * a * m₂⁻¹ := by
  have := h.charP
  set α := mat a ιe₁ ιe₂ with hα
  set β := mat a ιe₁ ιz with hβ
  set c := mat a ιe₁ ιf₂ with hc
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  obtain ⟨μ₁, μ₂, μ₃, hμ⟩ : ∃ μ₁ μ₂ μ₃ : K,
      μ₁ * h.bar c + μ₂ * h.bar β + μ₃ * h.bar α = ω := by
    by_cases hc0 : c = 0
    · by_cases hβ0 : β = 0
      · have hα0 : α ≠ 0 := fun hα0 => haZ (mem_ZPsub_of_A₂ ha hα0 hβ0 hc0)
        have : h.bar α ≠ 0 := (map_ne_zero h.bar).2 hα0
        exact ⟨0, 0, ω / h.bar α, by field_simp; ring⟩
      · have : h.bar β ≠ 0 := (map_ne_zero h.bar).2 hβ0
        exact ⟨0, ω / h.bar β, 0, by field_simp; ring⟩
    · have : h.bar c ≠ 0 := (map_ne_zero h.bar).2 hc0
      exact ⟨ω / h.bar c, 0, 0, by field_simp; ring⟩
  have := Data.finite_fixedField h
  have := Data.charP_fixedField h
  have hK2 : 2 < Nat.card h.fixedField := by
    rw [h.card_fixedField]
    have : 4 ≤ 2 ^ f := (Nat.pow_le_pow_right two_pos hf).trans_eq' (by norm_num)
    omega
  obtain ⟨l, hl0, hl1⟩ := Common.exists_ne_zero_ne_one hK2
  have hl0' : (l : K) ≠ 0 := fun e0 => hl0 (Subtype.ext e0)
  have hl1' : (l : K) + 1 ≠ 0 := by
    intro e0
    apply hl1
    apply Subtype.ext
    change (l : K) = 1
    linear_combination e0 - (CharTwo.two_eq_zero : (2 : K) = 0)
  have hlb : h.bar (l : K) = l := h.mem_fixedField.1 l.2
  obtain ⟨m₁, hm₁, e1, e2, e3⟩ := exists_A₂sub_coord h μ₁ μ₂ μ₃
  obtain ⟨m₂, hm₂, f1, f2, f3⟩ := exists_A₂sub_coord h (l * μ₁) (l * μ₂) (l * μ₃)
  have key : ∀ {m : hypSU h 2 1}, m ∈ A₂sub h → ∀ t : K, h.bar t ≠ t →
      mat m ιe₁ ιe₂ * h.bar c + mat m ιe₁ ιz * h.bar β + mat m ιe₁ ιf₂ * h.bar α = t →
      m * a ≠ a * m := by
    intro m hm t ht hB hma
    rw [mul_comm_iff_coord hm ha, ← hα, ← hβ, ← hc, hB] at hma
    exact ht hma.symm
  have hbl : ∀ t : K, h.bar t ≠ t → ∀ s : K, s ≠ 0 → h.bar s = s → h.bar (s * t) ≠ s * t :=
    fun t ht s hs hsb e => ht (mul_left_cancel₀ hs (by rw [← e, map_mul, hsb]))
  refine ⟨m₁, hm₁, m₂, hm₂, key hm₁ ω hω (by rw [e1, e2, e3, hμ]),
    key hm₂ (l * ω) (hbl ω hω l hl0' hlb) (by rw [f1, f2, f3, ← hμ]; ring), fun e => ?_⟩
  have hcomm : (m₂⁻¹ * m₁) * a = a * (m₂⁻¹ * m₁) := by
    calc (m₂⁻¹ * m₁) * a = m₂⁻¹ * (m₁ * a * m₁⁻¹) * m₁ := by group
      _ = m₂⁻¹ * (m₂ * a * m₂⁻¹) * m₁ := by rw [e]
      _ = a * (m₂⁻¹ * m₁) := by group
  obtain ⟨g1, g2, g3⟩ := A₂_inv_mul hm₂ hm₁
  refine key (mul_mem (inv_mem hm₂) hm₁) ((l + 1) * ω)
    (hbl ω hω _ hl1' (by rw [map_add, hlb, map_one])) ?_ hcomm
  rw [g1, g2, g3, f1, f2, f3, e1, e2, e3, ← hμ]
  ring

end Commutators

section Aut

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

theorem A₂sub_entries {a : hypSU h 2 1} (ha : a ∈ A₂sub h) :
    mat a ιe₁ ιe₁ = 1 ∧
      (mat a ιe₂ ιe₂ = 1 ∧ mat a ιz ιe₂ = 0 ∧ mat a ιf₁ ιe₂ = 0 ∧ mat a ιf₂ ιe₂ = 0) ∧
      (mat a ιe₂ ιz = 0 ∧ mat a ιz ιz = 1 ∧ mat a ιf₁ ιz = 0 ∧ mat a ιf₂ ιz = 0) ∧
      (mat a ιe₂ ιf₂ = 0 ∧ mat a ιz ιf₂ = 0 ∧ mat a ιf₁ ιf₂ = 0 ∧ mat a ιf₂ ιf₂ = 1) ∧
      mat a ιf₁ ιe₁ = 0 ∧ mat a ιf₁ ιf₁ = 1 := by
  obtain ⟨haU, a1, a2, a3⟩ := mem_A₂sub.1 ha
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨-, -, -, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries haU
  exact ⟨d1, ⟨d2, l5, l7, l6⟩, ⟨a1, d3, l9, l8⟩, ⟨a3, a2, l10, d5⟩, l4, d4⟩

theorem lmat_row_e₁_of_fixes {x : Gam h} (hrow : ∀ b, b ≠ ιf₁ → lmat x ιf₁ b = 0)
    {a z : hypSU h 2 1} (ha : a ∈ A₂sub h) (hz : z ∈ ZPsub h) (hxa : actΓ h x a = z * a)
    {j : HypIndex 2 1} (hj : j = ιe₂ ∨ j = ιz ∨ j = ιf₂) :
    lmat x ιe₁ ιe₁ * x.1.right (mat a ιe₁ j) =
      mat a ιe₁ ιe₂ * lmat x ιe₂ j + mat a ιe₁ ιz * lmat x ιz j +
        mat a ιe₁ ιf₂ * lmat x ιf₂ j := by
  have hrel := congrFun (congrFun (lmat_mul_map x a) ιe₁) j
  rw [hxa, mat_mul, mat_eq_of_mem_ZPsub hz, Matrix.mul_assoc, Matrix.add_mul, Matrix.one_mul,
    Matrix.add_apply, single_mul_apply_same] at hrel
  obtain ⟨e11, ⟨d22, l32, l42, l52⟩, ⟨u23, d33, l43, l53⟩, ⟨u25, u35, l45, d55⟩, l41, d44⟩ :=
    A₂sub_entries ha
  have hjf : j ≠ ιf₁ := by rcases hj with rfl | rfl | rfl <;> decide
  have hf : (mat a * lmat x) ιf₁ j = 0 := by
    rw [Matrix.mul_apply, sum_hypIndex_two, l41, l42, l43, d44, l45, hrow j hjf]
    ring
  rw [hf, mul_zero, add_zero, Matrix.mul_apply, Matrix.mul_apply, sum_hypIndex_two,
    sum_hypIndex_two, e11, hrow j hjf] at hrel
  rcases hj with rfl | rfl | rfl
  · simp only [Matrix.map_apply, d22, l32, l42, l52, map_one, map_zero, mul_one, mul_zero,
      add_zero] at hrel
    linear_combination hrel
  · simp only [Matrix.map_apply, u23, d33, l43, l53, map_one, map_zero, mul_one, mul_zero,
      add_zero] at hrel
    linear_combination hrel
  · simp only [Matrix.map_apply, u25, u35, l45, d55, map_one, map_zero, mul_one, mul_zero,
      add_zero] at hrel
    linear_combination hrel

theorem mul_one_add_single_apply_of_ne (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (d : K)
    (a : HypIndex 2 1) {b : HypIndex 2 1} (hb : b ≠ ιf₁) :
    (M * (1 + Matrix.single ιe₁ ιf₁ d)) a b = M a b := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_zero fun k _ => by rw [Matrix.single_apply, ite_eq_right (fun e => hb e.2.symm),
      mul_zero], add_zero]

theorem mul_one_add_single_apply_f₁ (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (d : K)
    (a : HypIndex 2 1) :
    (M * (1 + Matrix.single ιe₁ ιf₁ d)) a ιf₁ = M a ιf₁ + M a ιe₁ * d := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, mul_single_apply_same]

theorem exists_eq_innM_of_fixes_A₂ {x : Gam h} (hcol : ∀ a, a ≠ ιe₁ → lmat x a ιe₁ = 0)
    (hrow : ∀ b, b ≠ ιf₁ → lmat x ιf₁ b = 0)
    (hA : ∀ a ∈ A₂sub h, ∃ z ∈ ZPsub h, actΓ h x a = z * a) :
    ∃ u ∈ A₂sub h, Phi h x = innM h u := by
  have := h.charP
  have h2 : ∀ a : K, a + a = 0 := CharTwo.add_self_eq_zero
  set A := lmat x with hAdef
  set σ := x.1.right with hσdef
  set l := A ιe₁ ιe₁ with hl
  have hl0 : l ≠ 0 := lmat_e₁e₁_ne_zero hcol
  have hbl0 : h.bar l ≠ 0 := (map_ne_zero h.bar).2 hl0
  have key : ∀ a ∈ A₂sub h, ∀ j, (j = ιe₂ ∨ j = ιz ∨ j = ιf₂) →
      l * σ (mat a ιe₁ j) = mat a ιe₁ ιe₂ * A ιe₂ j + mat a ιe₁ ιz * A ιz j +
        mat a ιe₁ ιf₂ * A ιf₂ j := fun a ha j hj => by
    obtain ⟨z, hz, hxa⟩ := hA a ha
    exact lmat_row_e₁_of_fixes hrow ha hz hxa hj
  obtain ⟨g₁, hg₁, p1, p2, p3⟩ := exists_A₂sub_coord h 1 0 0
  obtain ⟨g₂, hg₂, q1, q2, q3⟩ := exists_A₂sub_coord h 0 1 0
  obtain ⟨g₃, hg₃, r1, r2, r3⟩ := exists_A₂sub_coord h 0 0 1
  have k11 := key g₁ hg₁ ιe₂ (Or.inl rfl)
  have k12 := key g₁ hg₁ ιz (Or.inr (Or.inl rfl))
  have k13 := key g₁ hg₁ ιf₂ (Or.inr (Or.inr rfl))
  have k21 := key g₂ hg₂ ιe₂ (Or.inl rfl)
  have k22 := key g₂ hg₂ ιz (Or.inr (Or.inl rfl))
  have k23 := key g₂ hg₂ ιf₂ (Or.inr (Or.inr rfl))
  have k31 := key g₃ hg₃ ιe₂ (Or.inl rfl)
  have k32 := key g₃ hg₃ ιz (Or.inr (Or.inl rfl))
  have k33 := key g₃ hg₃ ιf₂ (Or.inr (Or.inr rfl))
  simp only [p1, p2, p3, map_one, map_zero, mul_one, mul_zero, one_mul, zero_mul,
    add_zero] at k11 k12 k13
  simp only [q1, q2, q3, map_one, map_zero, mul_one, mul_zero, one_mul, zero_mul, add_zero,
    zero_add] at k21 k22 k23
  simp only [r1, r2, r3, map_one, map_zero, mul_one, mul_zero, one_mul, zero_mul, add_zero,
    zero_add] at k31 k32 k33
  have hσ : σ = 1 := by
    apply RingEquiv.ext
    intro u
    obtain ⟨g, hg, s1, s2, s3⟩ := exists_A₂sub_coord h u 0 0
    have k := key g hg ιe₂ (Or.inl rfl)
    rw [s1, s2, s3, ← k11] at k
    simp only [zero_mul, add_zero] at k
    exact mul_left_cancel₀ hl0 (k.trans (mul_comm _ _))
  obtain ⟨μ, -, -, hsim⟩ := x.2
  have hs : ∀ a b, h.bar (A ιf₁ a) * A ιe₁ b + h.bar (A ιf₂ a) * A ιe₂ b +
      h.bar (A ιz a) * A ιz b + h.bar (A ιe₁ a) * A ιf₁ b + h.bar (A ιe₂ a) * A ιf₂ b =
      μ * hypGram 2 1 K a b := by
    intro a b
    have g := congrFun (congrFun hsim a) b
    change ((A.map h.bar)ᵀ * hypGram 2 1 K * A) a b = _ at g
    rw [Matrix.mul_apply, sum_hypIndex_two, Matrix.smul_apply, smul_eq_mul] at g
    simpa only [mul_hypGram_apply, Matrix.transpose_apply, Matrix.map_apply, hypPartner_inl,
      hypPartner_inr_inl, hypPartner_inr_inr] using g
  have J22 : hypGram 2 1 K ιe₂ ιf₂ = 1 := by simp [hypGram_apply]
  have J11 : hypGram 2 1 K ιe₁ ιf₁ = 1 := by simp [hypGram_apply]
  have J21 : hypGram 2 1 K ιe₂ ιf₁ = 0 := by simp [hypGram_apply]
  have Jz1 : hypGram 2 1 K ιz ιf₁ = 0 := by simp [hypGram_apply]
  have J51 : hypGram 2 1 K ιf₂ ιf₁ = 0 := by simp [hypGram_apply]
  have Jff : hypGram 2 1 K ιf₁ ιf₁ = 0 := by simp [hypGram_apply]
  have c1 := hcol ιe₂ (by decide)
  have c2 := hcol ιz (by decide)
  have c3 := hcol ιf₁ (by decide)
  have c4 := hcol ιf₂ (by decide)
  have w1 := hrow ιe₂ (by decide)
  have w2 := hrow ιz (by decide)
  have w3 := hrow ιf₂ (by decide)
  have s22 := hs ιe₂ ιf₂
  have s11 := hs ιe₁ ιf₁
  have s21 := hs ιe₂ ιf₁
  have sz1 := hs ιz ιf₁
  have s51 := hs ιf₂ ιf₁
  have sff := hs ιf₁ ιf₁
  rw [J22, mul_one] at s22
  rw [J11, mul_one] at s11
  rw [J21, mul_zero] at s21
  rw [Jz1, mul_zero] at sz1
  rw [J51, mul_zero] at s51
  rw [Jff, mul_zero] at sff
  simp only [← k11, ← k22, ← k33, ← k12, ← k13, ← k21, ← k23, ← k31, ← k32, c1, c2, c3, c4, w1,
    w2, w3, map_zero, zero_mul, mul_zero, zero_add, add_zero] at s22 s11 s21 sz1 s51 sff
  have hff : A ιf₁ ιf₁ = l := mul_left_cancel₀ hbl0 (s11.trans s22.symm)
  rw [hff] at s21 sz1 s51 sff
  have hX : h.bar l * A ιf₂ ιf₁ = h.bar (A ιe₁ ιe₂) * l := by
    linear_combination s21 - h2 (h.bar (A ιe₁ ιe₂) * l)
  have hY : h.bar l * A ιz ιf₁ = h.bar (A ιe₁ ιz) * l := by
    linear_combination sz1 - h2 (h.bar (A ιe₁ ιz) * l)
  have hZ : h.bar l * A ιe₂ ιf₁ = h.bar (A ιe₁ ιf₂) * l := by
    linear_combination s51 - h2 (h.bar (A ιe₁ ιf₂) * l)
  have hbar : ∀ {u v : K}, h.bar l * u = h.bar v * l → l * h.bar u = v * h.bar l := by
    intro u v e
    have := congrArg h.bar e
    simpa only [map_mul, h.bar_bar, mul_comm] using this
  have hll : l * h.bar l ≠ 0 := mul_ne_zero hl0 hbl0
  have hprod : ∀ {u v u' v' : K}, h.bar l * u = h.bar v * l → h.bar l * u' = h.bar v' * l →
      h.bar u * u' = v * h.bar v' := by
    intro u v u' v' e e'
    have e1 := hbar e
    refine mul_left_cancel₀ hll ?_
    linear_combination h.bar l * u' * e1 + v * h.bar l * e'
  have p12 := hprod hX hZ
  have p33 := hprod hY hY
  have p21 := hprod hZ hX
  have htr : A ιe₁ ιf₁ * h.bar l + h.bar (A ιe₁ ιf₁) * l =
      A ιe₁ ιz * h.bar (A ιe₁ ιz) + (A ιe₁ ιe₂ * h.bar (A ιe₁ ιf₂) +
        A ιe₁ ιf₂ * h.bar (A ιe₁ ιe₂)) := by
    linear_combination sff - p12 - p33 - p21 - h2 (A ιe₁ ιz * h.bar (A ιe₁ ιz) +
      (A ιe₁ ιe₂ * h.bar (A ιe₁ ιf₂) + A ιe₁ ιf₂ * h.bar (A ιe₁ ιe₂)))
  obtain ⟨g, hg, g1, g2, g3⟩ :=
    exists_A₂sub_coord h (A ιe₁ ιe₂ / l) (A ιe₁ ιz / l) (A ιe₁ ιf₂ / l)
  have hgU := A₂sub_le_U hg
  obtain ⟨-, -, -, -, -, g6⟩ := U_rel hgU
  rw [g1, g2, g3] at g6
  set d : K := A ιe₁ ιf₁ / l + mat g ιe₁ ιf₁ with hd
  have hdb : h.bar d = d := by
    refine bar_eq_of_add_eq_zero h ?_
    have e1 : A ιe₁ ιf₁ / l + h.bar (A ιe₁ ιf₁ / l) =
        A ιe₁ ιz / l * h.bar (A ιe₁ ιz / l) + (A ιe₁ ιe₂ / l * h.bar (A ιe₁ ιf₂ / l) +
          A ιe₁ ιf₂ / l * h.bar (A ιe₁ ιe₂ / l)) := by
      have key : A ιe₁ ιf₁ / l + h.bar (A ιe₁ ιf₁ / l) -
          (A ιe₁ ιz / l * h.bar (A ιe₁ ιz / l) + (A ιe₁ ιe₂ / l * h.bar (A ιe₁ ιf₂ / l) +
            A ιe₁ ιf₂ / l * h.bar (A ιe₁ ιe₂ / l))) =
          ((A ιe₁ ιf₁ * h.bar l + h.bar (A ιe₁ ιf₁) * l) -
            (A ιe₁ ιz * h.bar (A ιe₁ ιz) + (A ιe₁ ιe₂ * h.bar (A ιe₁ ιf₂) +
              A ιe₁ ιf₂ * h.bar (A ιe₁ ιe₂)))) / (l * h.bar l) := by
        simp only [map_div₀]
        field_simp
      rw [htr, sub_self, zero_div] at key
      exact sub_eq_zero.1 key
    rw [hd, map_add]
    linear_combination e1 + g6 + h2 (A ιe₁ ιz / l * h.bar (A ιe₁ ιz / l) +
      (A ιe₁ ιe₂ / l * h.bar (A ιe₁ ιf₂ / l) + A ιe₁ ιf₂ / l * h.bar (A ιe₁ ιe₂ / l)))
  set u := g * zRoot h ⟨d, h.mem_fixedField.2 hdb⟩ with hu
  have huA : u ∈ A₂sub h := mul_mem hg (Z₂Psub_le_A₂sub (ZPsub_le_Z₂Psub (zRoot_mem _)))
  have hmu1 : ∀ a b, b ≠ ιf₁ → mat u a b = mat g a b := by
    intro a b hb
    rw [hu, mat_mul, mat_eq_of_mem_ZPsub (zRoot_mem _), mat_zRoot,
      mul_one_add_single_apply_of_ne _ _ _ hb]
  have hmu2 : ∀ a, mat u a ιf₁ = mat g a ιf₁ + mat g a ιe₁ * d := by
    intro a
    rw [hu, mat_mul, mat_eq_of_mem_ZPsub (zRoot_mem _), mat_zRoot, mul_one_add_single_apply_f₁]
  obtain ⟨e11, ⟨d22, l32, l42, l52⟩, ⟨u23, d33, l43, l53⟩, ⟨u25, u35, l45, d55⟩, l41, d44⟩ :=
    A₂sub_entries hg
  obtain ⟨⟨-, -, -, -, -⟩, ⟨l21, l31, l51, -, -, -, -, -, -, -⟩⟩ := U_entries hgU
  obtain ⟨a1, a2, a3⟩ := A₂_rel hg
  rw [g1, map_div₀] at a1
  rw [g2, map_div₀] at a2
  rw [g3, map_div₀] at a3
  have hAu : A = l • mat u := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul]
    rcases a with i | m | i <;> rcases b with j | k | j
    · fin_cases i <;> fin_cases j
      · show A ιe₁ ιe₁ = l * mat u ιe₁ ιe₁
        rw [hmu1 ιe₁ ιe₁ (by decide), e11, mul_one]
      · show A ιe₁ ιe₂ = l * mat u ιe₁ ιe₂
        rw [hmu1 ιe₁ ιe₂ (by decide), g1]
        field_simp
      · show A ιe₂ ιe₁ = l * mat u ιe₂ ιe₁
        rw [hmu1 ιe₂ ιe₁ (by decide), l21, mul_zero, c1]
      · show A ιe₂ ιe₂ = l * mat u ιe₂ ιe₂
        rw [hmu1 ιe₂ ιe₂ (by decide), d22, mul_one, k11]
    · fin_cases i <;> fin_cases k
      · show A ιe₁ ιz = l * mat u ιe₁ ιz
        rw [hmu1 ιe₁ ιz (by decide), g2]
        field_simp
      · show A ιe₂ ιz = l * mat u ιe₂ ιz
        rw [hmu1 ιe₂ ιz (by decide), u23, mul_zero, k12]
    · fin_cases i <;> fin_cases j
      · show A ιe₁ ιf₁ = l * mat u ιe₁ ιf₁
        rw [hmu2 ιe₁, e11, one_mul, hd]
        field_simp
        linear_combination (-l) * h2 (mat g ιe₁ ιf₁)
      · show A ιe₁ ιf₂ = l * mat u ιe₁ ιf₂
        rw [hmu1 ιe₁ ιf₂ (by decide), g3]
        field_simp
      · show A ιe₂ ιf₁ = l * mat u ιe₂ ιf₁
        rw [hmu2 ιe₂, l21, zero_mul, add_zero, a3]
        field_simp
        linear_combination hZ
      · show A ιe₂ ιf₂ = l * mat u ιe₂ ιf₂
        rw [hmu1 ιe₂ ιf₂ (by decide), u25, mul_zero, k13]
    · fin_cases m
      fin_cases j
      · show A ιz ιe₁ = l * mat u ιz ιe₁
        rw [hmu1 ιz ιe₁ (by decide), l31, mul_zero, c2]
      · show A ιz ιe₂ = l * mat u ιz ιe₂
        rw [hmu1 ιz ιe₂ (by decide), l32, mul_zero, k21]
    · fin_cases m
      fin_cases k
      show A ιz ιz = l * mat u ιz ιz
      rw [hmu1 ιz ιz (by decide), d33, mul_one, k22]
    · fin_cases m
      fin_cases j
      · show A ιz ιf₁ = l * mat u ιz ιf₁
        rw [hmu2 ιz, l31, zero_mul, add_zero, a2]
        field_simp
        linear_combination hY
      · show A ιz ιf₂ = l * mat u ιz ιf₂
        rw [hmu1 ιz ιf₂ (by decide), u35, mul_zero, k23]
    · fin_cases i <;> fin_cases j
      · show A ιf₁ ιe₁ = l * mat u ιf₁ ιe₁
        rw [hmu1 ιf₁ ιe₁ (by decide), l41, mul_zero, c3]
      · show A ιf₁ ιe₂ = l * mat u ιf₁ ιe₂
        rw [hmu1 ιf₁ ιe₂ (by decide), l42, mul_zero, w1]
      · show A ιf₂ ιe₁ = l * mat u ιf₂ ιe₁
        rw [hmu1 ιf₂ ιe₁ (by decide), l51, mul_zero, c4]
      · show A ιf₂ ιe₂ = l * mat u ιf₂ ιe₂
        rw [hmu1 ιf₂ ιe₂ (by decide), l52, mul_zero, k31]
    · fin_cases i <;> fin_cases k
      · show A ιf₁ ιz = l * mat u ιf₁ ιz
        rw [hmu1 ιf₁ ιz (by decide), l43, mul_zero, w2]
      · show A ιf₂ ιz = l * mat u ιf₂ ιz
        rw [hmu1 ιf₂ ιz (by decide), l53, mul_zero, k32]
    · fin_cases i <;> fin_cases j
      · show A ιf₁ ιf₁ = l * mat u ιf₁ ιf₁
        rw [hmu2 ιf₁, l41, zero_mul, add_zero, d44, mul_one, hff]
      · show A ιf₁ ιf₂ = l * mat u ιf₁ ιf₂
        rw [hmu1 ιf₁ ιf₂ (by decide), l45, mul_zero, w3]
      · show A ιf₂ ιf₁ = l * mat u ιf₂ ιf₁
        rw [hmu2 ιf₂, l51, zero_mul, add_zero, a1]
        field_simp
        linear_combination hX
      · show A ιf₂ ιf₂ = l * mat u ιf₂ ιf₂
        rw [hmu1 ιf₂ ιf₂ (by decide), d55, mul_one, k33]
  have hσ' : x.1.right = 1 := hσ
  have hy : Phi h ((inlG u)⁻¹ * x) = 1 := by
    refine Phi_eq_one_iff.2 ⟨?_, Units.mk0 l hl0, ?_⟩
    · simp [inlG, hσ']
    · have e : ((inlG u)⁻¹ * x).1.left = (u : GL (HypIndex 2 1) K)⁻¹ * x.1.left := by
        simp [inlG]
      rw [e]
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0]
      change (((u : GL (HypIndex 2 1) K)⁻¹ : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) * A = _
      rw [hAu, Matrix.mul_smul]
      change _ • (((u : GL (HypIndex 2 1) K)⁻¹ : GL (HypIndex 2 1) K) *
        (u : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
      rw [Units.inv_mul, Matrix.smul_one_eq_diagonal]
      rfl
  refine ⟨u, huA, ?_⟩
  calc Phi h x = Phi h (inlG u * ((inlG u)⁻¹ * x)) := by rw [mul_inv_cancel_left]
    _ = innM h u := by rw [map_mul, hy, mul_one, Phi_inlG]

end Aut

end CFSG.LocalAnalysis.EvenBN.U5

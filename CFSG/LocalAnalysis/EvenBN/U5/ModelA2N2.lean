module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B4Model
public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowA2

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section Action

theorem A₂_inv_mul_mem_ZPsub {x y : hypSU h 2 1} (hx : x ∈ A₂sub h) (hy : y ∈ A₂sub h)
    (h1 : mat x ιe₁ ιe₂ = mat y ιe₁ ιe₂) (h2 : mat x ιe₁ ιz = mat y ιe₁ ιz)
    (h3 : mat x ιe₁ ιf₂ = mat y ιe₁ ιf₂) : x⁻¹ * y ∈ ZPsub h := by
  have := h.charP
  obtain ⟨m1, m2, m3⟩ := A₂_inv_mul hx hy
  exact mem_ZPsub_of_A₂ (mul_mem (inv_mem hx) hy) (by rw [m1, h1, CharTwo.add_self_eq_zero])
    (by rw [m2, h2, CharTwo.add_self_eq_zero]) (by rw [m3, h3, CharTwo.add_self_eq_zero])

theorem A₂_conj_sSU {x : hypSU h 2 1} (hx : x ∈ A₂sub h) :
    sSU h * x * (sSU h)⁻¹ ∈ A₂sub h ∧ mat (sSU h * x * (sSU h)⁻¹) ιe₁ ιe₂ = mat x ιe₁ ιf₂ ∧
      mat (sSU h * x * (sSU h)⁻¹) ιe₁ ιz = mat x ιe₁ ιz ∧
      mat (sSU h * x * (sSU h)⁻¹) ιe₁ ιf₂ = mat x ιe₁ ιe₂ := by
  refine ⟨conj_perm_mem_patSub σs_σs σs_partner mat_sSU isPattern_sA₂ isPattern_sA₂
    (by decide) hx, ?_, ?_, ?_⟩ <;> rw [conj_sSU_apply] <;> rfl

theorem A₂_conj_rootI₂ {g x : hypSU h 2 1} (hg : g ∈ patSub h sI₂ isPattern_sI₂)
    (hx : x ∈ A₂sub h) :
    g⁻¹ * x * g ∈ A₂sub h ∧ mat (g⁻¹ * x * g) ιe₁ ιe₂ = mat x ιe₁ ιe₂ ∧
      mat (g⁻¹ * x * g) ιe₁ ιz = mat x ιe₁ ιz + mat x ιe₁ ιe₂ * mat g ιe₂ ιz ∧
      mat (g⁻¹ * x * g) ιe₁ ιf₂ = mat x ιe₁ ιf₂ + mat x ιe₁ ιe₂ * mat g ιe₂ ιf₂ +
        mat x ιe₁ ιz * h.bar (mat g ιe₂ ιz) := by
  have hgU := patSub_le_U _ _ hg
  have hgi := inv_mem hg
  have hgiU := patSub_le_U _ _ hgi
  have hxU := A₂sub_le_U hx
  have hgx := mul_mem hgiU hxU
  obtain ⟨-, x1, x2, x3⟩ := mem_A₂sub.1 hx
  obtain ⟨-, g1, -, g3, -, g5, -, -⟩ := mem_patSub_sI₂.1 hg
  obtain ⟨-, i1, -, i3, -, i5, -, -⟩ := mem_patSub_sI₂.1 hgi
  have r := (U_rel hgU).2.1
  have e1 := mul_e₂z hgiU hgU
  have e2 := mul_zf₂ hgiU hgU
  have e3 := mul_e₂f₂ hgiU hgU
  rw [inv_mul_cancel, mat_one, one_apply_ne (by decide)] at e1 e2 e3
  refine ⟨mem_A₂sub.2 ⟨mul_mem hgx hgU, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [mul_e₂z hgx hgU, mul_e₂z hgiU hxU, x1, add_zero, e1]
  · rw [mul_zf₂ hgx hgU, mul_zf₂ hgiU hxU, x2, add_zero, e2]
  · rw [mul_e₂f₂ hgx hgU, mul_e₂f₂ hgiU hxU, mul_e₂z hgiU hxU, x1, x2, x3, add_zero, add_zero,
      mul_zero, add_zero, e3]
  · rw [mul_e₁e₂ hgx hgU, mul_e₁e₂ hgiU hxU, i1, g1, zero_add, add_zero]
  · rw [mul_e₁z hgx hgU, mul_e₁z hgiU hxU, mul_e₁e₂ hgiU hxU, i1, i3, g3]
    ring
  · rw [mul_e₁f₂ hgx hgU, mul_e₁f₂ hgiU hxU, mul_e₁e₂ hgiU hxU, mul_e₁z hgiU hxU, i1, i3, i5,
      g5, x3, r]
    ring

theorem exists_torus_N₂sub (h : UnitaryFieldData 2 f K) {a : K} (ha : a ≠ 0) :
    ∃ t ∈ N₂sub h, t ∈ Isub h ∧ ∀ x ∈ A₂sub h, t * x * t⁻¹ ∈ A₂sub h ∧
      mat (t * x * t⁻¹) ιe₁ ιe₂ = mat x ιe₁ ιe₂ * a⁻¹ ∧
      mat (t * x * t⁻¹) ιe₁ ιz = mat x ιe₁ ιz * (h.bar a / a)⁻¹ ∧
      mat (t * x * t⁻¹) ιe₁ ιf₂ = mat x ιe₁ ιf₂ * h.bar a := by
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus h one_ne_zero ha
  rw [map_one, one_mul, one_mul] at e3
  rw [map_one, inv_one] at e4
  refine ⟨t, mem_N₂sub_of_torus ht e1 e4, ht, fun x hx =>
    ⟨torus_conj_mem_patSub isPattern_sA₂ ht hx, ?_, ?_, ?_⟩⟩ <;>
    rw [torus_conj_apply ht, e1, one_mul]
  · rw [e2]
  · rw [e3]
  · rw [e5, inv_inv]

theorem N₂sub_sup_Isub_le_normalizer_A₂sub :
    N₂sub h ⊔ Isub h ≤ normalizer (A₂sub h : Set (hypSU h 2 1)) := by
  have := finite_hypSU (hK := h)
  refine sup_le (fun n hn => mem_normalizer_of_conj_le fun g hg => ?_)
    (fun t ht => mem_normalizer_of_conj_le fun g hg => torus_conj_mem_patSub isPattern_sA₂ ht hg)
  rw [mem_A₂sub_iff, mat_mul, mat_mul]
  refine isFlagUni_mul_mul ιe₁_ne_ιf₁ (by rw [← mat_mul, mul_inv_cancel, mat_one])
    (by rw [← mat_mul, inv_mul_cancel, mat_one]) (fun c hc => ?_) (fun k hk => ?_)
    (mem_A₂sub_iff.1 hg)
  · rw [(mem_N₂sub.1 hn).1 c, one_apply_ne hc]
  · rw [(N₂sub_rows hn k).2, one_apply_ne (Ne.symm hk)]

end Action

section NormalForm

theorem exists_N₂sub_conj_normal {x : hypSU h 2 1} (hx : x ∈ A₂sub h) (hxZ : x ∉ ZPsub h) :
    ∃ n ∈ N₂sub h, n * x * n⁻¹ ∈ A₂sub h ∧ mat (n * x * n⁻¹) ιe₁ ιe₂ = 1 ∧
      mat (n * x * n⁻¹) ιe₁ ιz = 0 := by
  have := h.charP
  obtain ⟨n₁, hn₁, hy, hy0⟩ : ∃ n₁ ∈ N₂sub h, n₁ * x * n₁⁻¹ ∈ A₂sub h ∧
      mat (n₁ * x * n₁⁻¹) ιe₁ ιe₂ ≠ 0 := by
    by_cases hα : mat x ιe₁ ιe₂ = 0
    · by_cases hc : mat x ιe₁ ιf₂ = 0
      · have hβ : mat x ιe₁ ιz ≠ 0 := fun hβ => hxZ (mem_ZPsub_of_A₂ hx hα hβ hc)
        obtain ⟨w, hw⟩ := exists_trace_one (hK := h)
        obtain ⟨g, hg, g1, g2⟩ := exists_rootI₂ h (u := 1) (c := w) (by rw [hw, map_one, mul_one])
        obtain ⟨hgx, k1, k2, k3⟩ := A₂_conj_rootI₂ hg hx
        obtain ⟨hs, s1, -, -⟩ := A₂_conj_sSU hgx
        have e : sSU h * g⁻¹ * x * (sSU h * g⁻¹)⁻¹ = sSU h * (g⁻¹ * x * g) * (sSU h)⁻¹ := by
          group
        refine ⟨sSU h * g⁻¹, mul_mem sSU_mem_N₂sub (inv_mem (patSub_sI₂_le_N₂sub hg)), ?_, ?_⟩
        · rw [e]
          exact hs
        · rw [e, s1, k3, hα, hc, g1, map_one]
          simpa using hβ
      · obtain ⟨hs, s1, -, -⟩ := A₂_conj_sSU hx
        exact ⟨sSU h, sSU_mem_N₂sub, hs, by rwa [s1]⟩
    · exact ⟨1, one_mem _, by simpa using hx, by simpa using hα⟩
  set y := n₁ * x * n₁⁻¹ with hydef
  set u := mat y ιe₁ ιz / mat y ιe₁ ιe₂ with hu
  obtain ⟨w, hw⟩ := trace_surj (hK := h) (a := u * h.bar u) (by rw [map_mul, h.bar_bar, mul_comm])
  obtain ⟨g, hg, g1, -⟩ := exists_rootI₂ h hw
  obtain ⟨hgy, k1, k2, -⟩ := A₂_conj_rootI₂ hg hy
  obtain ⟨t, htN, -, ht⟩ := exists_torus_N₂sub h hy0
  obtain ⟨htz, t1, t2, -⟩ := ht _ hgy
  have e : t * g⁻¹ * n₁ * x * (t * g⁻¹ * n₁)⁻¹ = t * (g⁻¹ * y * g) * t⁻¹ := by
    rw [hydef]
    group
  refine ⟨t * g⁻¹ * n₁, mul_mem (mul_mem htN (inv_mem (patSub_sI₂_le_N₂sub hg))) hn₁, ?_, ?_,
    ?_⟩ <;> rw [e]
  · exact htz
  · rw [t1, k1, mul_inv_cancel₀ hy0]
  · rw [t2, k2, g1, hu, mul_div_cancel₀ _ hy0, CharTwo.add_self_eq_zero, zero_mul]

end NormalForm

section Irreducible

theorem eq_A₂sub_of_coords {X : Subgroup (hypSU h 2 1)} (h1 : ZPsub h ≤ X) (h2 : X ≤ A₂sub h)
    (hα : ∀ a : K, ∃ y ∈ X, mat y ιe₁ ιe₂ = a ∧ mat y ιe₁ ιz = 0 ∧ mat y ιe₁ ιf₂ = 0)
    (hβ : ∀ b : K, ∃ y ∈ X, mat y ιe₁ ιe₂ = 0 ∧ mat y ιe₁ ιz = b ∧ mat y ιe₁ ιf₂ = 0)
    (hc : ∀ c : K, ∃ y ∈ X, mat y ιe₁ ιe₂ = 0 ∧ mat y ιe₁ ιz = 0 ∧ mat y ιe₁ ιf₂ = c) :
    X = A₂sub h := by
  refine le_antisymm h2 fun a ha => ?_
  obtain ⟨y₁, hy₁, a1, a2, a3⟩ := hα (mat a ιe₁ ιe₂)
  obtain ⟨y₂, hy₂, b1, b2, b3⟩ := hβ (mat a ιe₁ ιz)
  obtain ⟨y₃, hy₃, c1, c2, c3⟩ := hc (mat a ιe₁ ιf₂)
  have hy := mul_mem (mul_mem hy₁ hy₂) hy₃
  obtain ⟨m1, m2, m3, -⟩ := A₂_mul (mul_mem (h2 hy₁) (h2 hy₂)) (h2 hy₃)
  obtain ⟨n1, n2, n3, -⟩ := A₂_mul (h2 hy₁) (h2 hy₂)
  have hz := A₂_inv_mul_mem_ZPsub (h2 hy) ha (by rw [m1, n1, a1, b1, c1, add_zero, add_zero])
    (by rw [m2, n2, a2, b2, c2, zero_add, add_zero])
    (by rw [m3, n3, a3, b3, c3, zero_add, zero_add])
  rw [show a = (y₁ * y₂ * y₃) * ((y₁ * y₂ * y₃)⁻¹ * a) by group]
  exact mul_mem hy (h1 hz)

theorem A₂sub_irreducible {X : Subgroup (hypSU h 2 1)} (h1 : ZPsub h ≤ X) (h2 : X ≤ A₂sub h)
    (hn : ∀ n ∈ N₂sub h, ∀ x ∈ X, n * x * n⁻¹ ∈ X) : X = ZPsub h ∨ X = A₂sub h := by
  have := h.charP
  by_cases hX : X ≤ ZPsub h
  · exact Or.inl (le_antisymm hX h1)
  right
  obtain ⟨x, hxX, hxZ⟩ := Set.not_subset.1 hX
  obtain ⟨n, hnN, hy, y1, y2⟩ := exists_N₂sub_conj_normal (h2 hxX) hxZ
  have hyX : n * x * n⁻¹ ∈ X := hn n hnN x hxX
  set y := n * x * n⁻¹ with hydef
  have hF : ∀ w : K, h.bar w = w →
      ∃ v ∈ X, mat v ιe₁ ιe₂ = 0 ∧ mat v ιe₁ ιz = 0 ∧ mat v ιe₁ ιf₂ = w := by
    intro w hw
    obtain ⟨g, hg, g1, g2⟩ := exists_rootI₂ h (u := 0) (c := w)
      (by rw [hw, map_zero, mul_zero, CharTwo.add_self_eq_zero])
    have hgN := patSub_sI₂_le_N₂sub hg
    obtain ⟨hgy, k1, k2, k3⟩ := A₂_conj_rootI₂ hg hy
    have hgyX : g⁻¹ * y * g ∈ X := by
      simpa using hn g⁻¹ (inv_mem hgN) y hyX
    obtain ⟨m1, m2, m3⟩ := A₂_inv_mul hy hgy
    refine ⟨y⁻¹ * (g⁻¹ * y * g), mul_mem (inv_mem hyX) hgyX, ?_, ?_, ?_⟩
    · rw [m1, k1, CharTwo.add_self_eq_zero]
    · rw [m2, k2, y2, y1, g1]
      ring
    · rw [m3, k3, y1, y2, g1, g2]
      linear_combination (CharTwo.two_eq_zero (R := K)) * mat y ιe₁ ιf₂
  have hc : ∀ c : K, ∃ v ∈ X, mat v ιe₁ ιe₂ = 0 ∧ mat v ιe₁ ιz = 0 ∧ mat v ιe₁ ιf₂ = c := by
    intro c
    by_cases hc0 : c = 0
    · exact ⟨1, one_mem _, by simp [mat_one, one_apply_ne, hc0]⟩
    obtain ⟨v, hvX, v1, v2, v3⟩ := hF 1 (map_one _)
    have hbc : h.bar c ≠ 0 := (map_ne_zero h.bar).2 hc0
    obtain ⟨t, htN, -, ht⟩ := exists_torus_N₂sub h hbc
    obtain ⟨-, t1, t2, t3⟩ := ht v (h2 hvX)
    exact ⟨t * v * t⁻¹, hn t htN v hvX, by rw [t1, v1, zero_mul], by rw [t2, v2, zero_mul],
      by rw [t3, v3, one_mul, h.bar_bar]⟩
  have hα : ∀ a : K, ∃ v ∈ X, mat v ιe₁ ιe₂ = a ∧ mat v ιe₁ ιz = 0 ∧ mat v ιe₁ ιf₂ = 0 := by
    intro a
    obtain ⟨v, hvX, v1, v2, v3⟩ := hc a
    obtain ⟨-, s1, s2, s3⟩ := A₂_conj_sSU (h2 hvX)
    exact ⟨sSU h * v * (sSU h)⁻¹, hn _ sSU_mem_N₂sub v hvX, by rw [s1, v3], by rw [s2, v2],
      by rw [s3, v1]⟩
  have hβ : ∀ b : K, ∃ v ∈ X, mat v ιe₁ ιe₂ = 0 ∧ mat v ιe₁ ιz = b ∧ mat v ιe₁ ιf₂ = 0 := by
    intro b
    obtain ⟨v, hvX, v1, v2, v3⟩ := hα 1
    obtain ⟨w, hw⟩ := trace_surj (hK := h) (a := b * h.bar b)
      (by rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨g, hg, g1, g2⟩ := exists_rootI₂ h hw
    have hgN := patSub_sI₂_le_N₂sub hg
    obtain ⟨hgv, k1, k2, k3⟩ := A₂_conj_rootI₂ hg (h2 hvX)
    have hgvX : g⁻¹ * v * g ∈ X := by
      simpa using hn g⁻¹ (inv_mem hgN) v hvX
    obtain ⟨p, hpX, p1, p2, p3⟩ := hc w
    have hq := mul_mem (inv_mem hvX) hgvX
    obtain ⟨m1, m2, m3⟩ := A₂_inv_mul (h2 hvX) hgv
    obtain ⟨n1, n2, n3⟩ := A₂_inv_mul (h2 hpX) (h2 hq)
    refine ⟨p⁻¹ * (v⁻¹ * (g⁻¹ * v * g)), mul_mem (inv_mem hpX) hq, ?_, ?_, ?_⟩
    · rw [n1, m1, k1, p1, CharTwo.add_self_eq_zero, add_zero]
    · rw [n2, m2, k2, p2, v1, v2, g1]
      ring
    · rw [n3, m3, k3, p3, v1, v2, v3, g2]
      linear_combination (CharTwo.two_eq_zero (R := K)) * w
  exact eq_A₂sub_of_coords h1 h2 hα hβ hc

end Irreducible

end CFSG.LocalAnalysis.EvenBN.U5

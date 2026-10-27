module

public import CFSG.GH74.GLS.Stage4.RestPre

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank DodecA
open scoped Pointwise

variable {G : Type} [Group G] {D : Ch6Notation G}

theorem centralizes_of_conjBy_le {g : G} {Y Z P : Subgroup G} (hP : conjBy g Y ≤ P)
    (hZ : ∀ x ∈ Z, ∀ y ∈ P, x * y = y * x) :
    ∀ x ∈ Z, ∀ y ∈ Y, (g * x * g⁻¹) * y = y * (g * x * g⁻¹) := by
  intro x hx y hy
  have hy' : g⁻¹ * y * g ∈ conjBy g Y := by
    rw [mem_conjBy_iff]
    simpa [mul_assoc] using hy
  have h := hZ x hx _ (hP hy')
  have e1 : (g * x * g⁻¹) * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
  have e2 : y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
  rw [e1, e2, h]

theorem conj_mem_centralizer_of_comm {A : Subgroup G} {w c : G} (hw : ∀ y ∈ A, w * y = y * w)
    (hc : c ∈ centralizer (A : Set G)) : w * c * w⁻¹ ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro y hy
  have hw' : w⁻¹ * y = y * w⁻¹ := by
    have h2 := hw y hy
    calc w⁻¹ * y = w⁻¹ * (y * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * y) * w⁻¹ := by rw [h2]
      _ = y * w⁻¹ := by group
  calc y * (w * c * w⁻¹) = (y * w) * c * w⁻¹ := by group
    _ = (w * y) * c * w⁻¹ := by rw [← hw y hy]
    _ = w * (y * c) * w⁻¹ := by group
    _ = w * (c * y) * w⁻¹ := by rw [hc y hy]
    _ = (w * c) * (y * w⁻¹) := by group
    _ = (w * c) * (w⁻¹ * y) := by rw [hw']
    _ = (w * c * w⁻¹) * y := by group

theorem conjBy_inv_le_centralizer {A S : Subgroup G} {w : G} (hw : ∀ y ∈ A, w * y = y * w)
    (hS : S ≤ centralizer (A : Set G)) : conjBy w⁻¹ S ≤ centralizer (A : Set G) := by
  intro x hx
  rw [mem_conjBy_iff] at hx
  have h1 := hS hx
  have h2 := conj_mem_centralizer_of_comm hw h1
  have e : w * (w⁻¹ * x * w⁻¹⁻¹) * w⁻¹ = x := by group
  rw [e] at h2
  exact h2

theorem not_centralized_of_inv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u : G} {Y : Subgroup G}
    (hY : Y ≠ ⊥) (hu : ∀ x ∈ Y, u * x * u⁻¹ = x⁻¹) (hYp : ∀ x ∈ Y, x ^ p = 1)
    (hcomm : ∀ x ∈ Y, x * u = u * x) : False := by
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hY)
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have h1 := hu y hy
  have h2 : u * y * u⁻¹ = y := by
    rw [← hcomm y hy]
    group
  have h3 : y * y = 1 := by
    rw [h2] at h1
    calc y * y = y * y⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel y
  obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have h4 := hYp y hy
  have h5 : y ^ p = y := by
    rw [hm, pow_succ, pow_mul, pow_two, h3, one_pow, one_mul]
  exact hy1' (h5 ▸ h4)

theorem Ch6Basics.u_mem_conjBy_K₂ (h : Ch6Basics D) : D.u ∈ conjBy D.a D.K₂ := by
  rw [mem_conjBy_iff]
  have e : D.a * D.u * D.a⁻¹ = D.z := by
    simp only [Ch6Notation.u]
    group
  rw [e]
  exact h.z_mem_K₂

theorem Ch6Notation.A_false : D.A false = D.X₁ := by simp [Ch6Notation.A]
theorem Ch6Notation.A_true : D.A true = D.X₁' := by simp [Ch6Notation.A]
theorem Ch6Notation.B_false : D.B false = D.X₂ := by simp [Ch6Notation.B]
theorem Ch6Notation.B_true : D.B true = D.X₂' := by simp [Ch6Notation.B]

theorem Ch6Basics.A_le (h : Ch6Basics D) (b : Bool) : D.A b ≤ D.K₁ := by
  cases b
  · rw [Ch6Notation.A_false, h.K₁_eq]
    exact le_sup_left
  · rw [Ch6Notation.A_true, h.K₁_eq]
    exact le_sup_right

theorem Ch6Basics.B_le (h : Ch6Basics D) (b : Bool) : D.B b ≤ D.K₂ := by
  cases b
  · rw [Ch6Notation.B_false, h.K₂_eq]
    exact le_sup_left
  · rw [Ch6Notation.B_true, h.K₂_eq]
    exact le_sup_right

theorem Ch6Basics.hInv_A (h : Ch6Basics D) (b : Bool) : HInv D.H (D.A b) := by
  cases b
  · rw [Ch6Notation.A_false]
    exact h.H_norm_X₁
  · rw [Ch6Notation.A_true]
    exact h.H_norm_X₁'

theorem Ch6Basics.hInv_B (h : Ch6Basics D) (b : Bool) : HInv D.H (D.B b) := by
  cases b
  · rw [Ch6Notation.B_false]
    exact h.H_norm_X₂
  · rw [Ch6Notation.B_true]
    exact h.H_norm_X₂'

theorem Ch6Basics.A_ne_bot (h : Ch6Basics D) (b : Bool) : D.A b ≠ ⊥ := by
  have h5 := h.q₁_ge
  cases b
  · rw [Ch6Notation.A_false]
    exact ne_bot_of_card (by omega) h.card_X₁
  · rw [Ch6Notation.A_true]
    exact ne_bot_of_card (by omega) h.card_X₁'

theorem Ch6Basics.A_exp (h : Ch6Basics D) (b : Bool) : ∀ x ∈ D.A b, x ^ D.p = 1 := by
  cases b
  · rw [Ch6Notation.A_false]
    exact h.X₁_exp
  · rw [Ch6Notation.A_true]
    exact h.X₁'_exp

theorem Ch6PreP.A_inv (h : Ch6PreP D) (b : Bool) : ∀ x ∈ D.A b, D.u * x * D.u⁻¹ = x⁻¹ := by
  cases b
  · rw [Ch6Notation.A_false]
    exact h.u_inv_X₁
  · rw [Ch6Notation.A_true]
    exact h.u_inv_X₁'

theorem Ch6Notation.shape_le {α β γ δ : Bool} (hS : D.Shape α β γ δ) :
    conjBy D.a (D.A α) ≤ D.P ∧ conjBy D.a (D.B β) ≤ D.P ∧ conjBy (D.a ^ 2) (D.A γ) ≤ D.P ∧
      conjBy (D.a ^ 2) (D.B δ) ≤ D.P := by
  unfold Ch6Notation.Shape at hS
  have e1 : (1 : G) ∈ D.X₁ := D.X₁.one_mem
  have e2 : (1 : G) ∈ D.X₂ := D.X₂.one_mem
  have e3 : (1 : G) ∈ conjBy D.a (D.A α) := (conjBy D.a (D.A α)).one_mem
  have e4 : (1 : G) ∈ conjBy D.a (D.B β) := (conjBy D.a (D.B β)).one_mem
  have e5 : (1 : G) ∈ conjBy (D.a ^ 2) (D.A γ) := (conjBy (D.a ^ 2) (D.A γ)).one_mem
  have e6 : (1 : G) ∈ conjBy (D.a ^ 2) (D.B δ) := (conjBy (D.a ^ 2) (D.B δ)).one_mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have : x ∈ (D.P : Set G) := by
      rw [hS]
      simpa using six_mem_mul e1 e2 hx e4 e5 e6
    exact this
  · intro x hx
    have : x ∈ (D.P : Set G) := by
      rw [hS]
      simpa using six_mem_mul e1 e2 e3 hx e5 e6
    exact this
  · intro x hx
    have : x ∈ (D.P : Set G) := by
      rw [hS]
      simpa using six_mem_mul e1 e2 e3 e4 hx e6
    exact this
  · intro x hx
    have : x ∈ (D.P : Set G) := by
      rw [hS]
      simpa using six_mem_mul e1 e2 e3 e4 e5 hx
    exact this

theorem Ch6Pre.shape_ne_αγ (h : Ch6Pre D) {α β γ δ : Bool} (hS : D.Shape α β γ δ) : α ≠ γ := by
  have hb := h.basics
  have hp := h.pre
  intro hαγ
  rw [← hαγ] at hS
  obtain ⟨hP₁, -, hP₃, -⟩ := Ch6Notation.shape_le hS
  set Y := D.A α with hY
  set C : Subgroup G := centralizer (Y : Set G) with hC
  have hX₂ : HInv D.H D.X₂ := hb.H_norm_X₂
  have hX₂' : HInv D.H D.X₂' := hb.H_norm_X₂'
  have ha := hb.a_normH
  have ha3 := hb.a_cube
  have hc1 : conjBy D.a⁻¹ D.X₂ ≤ C := by
    intro z hz
    rw [mem_conjBy_iff] at hz
    have hz' : D.a⁻¹ * z * D.a ∈ D.X₂ := by simpa using hz
    rw [hC, mem_centralizer_iff]
    intro y hy
    have h1 := centralizes_of_conjBy_le hP₁ hp.X₂_central (D.a⁻¹ * z * D.a) hz' y hy
    have e : D.a * (D.a⁻¹ * z * D.a) * D.a⁻¹ = z := by group
    rw [e] at h1
    exact h1.symm
  have hc2 : conjBy (D.a ^ 2)⁻¹ D.X₂ ≤ C := by
    intro z hz
    rw [mem_conjBy_iff] at hz
    have hz' : (D.a ^ 2)⁻¹ * z * D.a ^ 2 ∈ D.X₂ := by simpa using hz
    rw [hC, mem_centralizer_iff]
    intro y hy
    have h1 := centralizes_of_conjBy_le hP₃ hp.X₂_central ((D.a ^ 2)⁻¹ * z * D.a ^ 2) hz' y hy
    have e : D.a ^ 2 * ((D.a ^ 2)⁻¹ * z * D.a ^ 2) * (D.a ^ 2)⁻¹ = z := by group
    rw [e] at h1
    exact h1.symm
  have e1 : conjBy D.a⁻¹ D.X₂ = conjBy (D.a ^ 2) D.X₂ := by
    have : D.a⁻¹ = D.a ^ 2 * (D.a ^ 3)⁻¹ := by group
    rw [this]
    exact conjBy_mul_of_mem hX₂ (pow_mem ha 2) (Subgroup.inv_mem _ ha3)
  have e2 : conjBy (D.a ^ 2)⁻¹ D.X₂ = conjBy D.a D.X₂ := by
    have : (D.a ^ 2)⁻¹ = D.a * (D.a ^ 3)⁻¹ := by group
    rw [this]
    exact conjBy_mul_of_mem hX₂ ha (Subgroup.inv_mem _ ha3)
  rw [e1] at hc1
  rw [e2] at hc2
  have hw : ∀ y ∈ Y, D.w₂ * y = y * D.w₂ := fun y hy =>
    (hb.K_comm y (hb.A_le α hy) D.w₂ hb.w₂_mem).symm
  have hc3 : conjBy (D.a ^ 2) D.X₂' ≤ C := by
    have := conjBy_inv_le_centralizer hw hc2
    rwa [conjBy_w_conjBy_a hX₂ hb.w₂_normH ha ha3 hb.w₂_a, conjBy_w₂_X₂ hb] at this
  have hc4 : conjBy D.a D.X₂' ≤ C := by
    have := conjBy_inv_le_centralizer hw hc1
    rw [show conjBy (D.a ^ 2) D.X₂ = conjBy (D.a ^ 2) D.X₂ from rfl,
      conjBy_w_conjBy_a_pow hX₂ hb.w₂_normH ha ha3 hb.w₂_a 2, conjBy_w₂_X₂ hb,
      conjBy_pow_mod hX₂' ha ha3 (2 * 2)] at this
    simpa using this
  have hK : conjBy D.a D.K₂ ≤ C := by
    rw [hb.K₂_eq, conjBy_sup']
    exact sup_le hc2 hc4
  have hu : ∀ y ∈ Y, y * D.u = D.u * y := fun y hy =>
    (mem_centralizer_iff.1 (hK hb.u_mem_conjBy_K₂) y hy)
  exact not_centralized_of_inv hb.prime hb.p_ne_two (hb.A_ne_bot α) (hp.A_inv α) (hb.A_exp α) hu

theorem Ch6Pre.shape_eq_βδ (h : Ch6Pre D) {α β γ δ : Bool} (hS : D.Shape α β γ δ) : β = δ := by
  have hb := h.basics
  have hp := h.pre
  by_contra hβδ
  obtain ⟨-, hP₂, -, hP₄⟩ := Ch6Notation.shape_le hS
  set C : Subgroup G := centralizer (D.X₂ : Set G) with hC
  have ha := hb.a_normH
  have ha3 := hb.a_cube
  have hcB : conjBy D.a (D.B β) ≤ C := by
    intro y hy
    rw [hC, mem_centralizer_iff]
    intro x hx
    exact hp.X₂_central x hx y (hP₂ hy)
  have hcδ : conjBy (D.a ^ 2) (D.B δ) ≤ C := by
    intro y hy
    rw [hC, mem_centralizer_iff]
    intro x hx
    exact hp.X₂_central x hx y (hP₄ hy)
  have hX₂K : D.X₂ ≤ D.K₂ := by
    rw [hb.K₂_eq]
    exact le_sup_left
  have hw : ∀ y ∈ D.X₂, D.w₁ * y = y * D.w₁ := fun y hy => hb.K_comm D.w₁ hb.w₁_mem y (hX₂K hy)
  have hwB : ∀ b : Bool, conjBy D.w₁⁻¹ (D.B b) = D.B b := by
    intro b
    refine conjBy_eq_self_of_comm (fun x hx => ?_)
    exact (Commute.inv_left (show Commute D.w₁ x from hb.K_comm D.w₁ hb.w₁_mem x (hb.B_le b hx))).eq
  have hd2 : conjBy D.a (D.B δ) ≤ C := by
    have := conjBy_inv_le_centralizer hw hcδ
    rw [conjBy_w_conjBy_a_pow (hb.hInv_B δ) hb.w₁_normH ha ha3 hb.w₁_a 2, hwB,
      conjBy_pow_mod (hb.hInv_B δ) ha ha3 (2 * 2)] at this
    simpa using this
  have hK : conjBy D.a D.K₂ ≤ C := by
    rw [hb.K₂_eq, conjBy_sup']
    cases β <;> cases δ
    · exact absurd rfl hβδ
    · simp only [Ch6Notation.B, Bool.false_eq_true, ↓reduceIte] at hcB hd2
      exact sup_le hcB hd2
    · simp only [Ch6Notation.B, Bool.false_eq_true, ↓reduceIte] at hcB hd2
      exact sup_le hd2 hcB
    · exact absurd rfl hβδ
  have hu : ∀ y ∈ D.X₂, y * D.u = D.u * y := fun y hy =>
    (mem_centralizer_iff.1 (hK hb.u_mem_conjBy_K₂) y hy)
  exact not_centralized_of_inv hb.prime hb.p_ne_two
    (ne_bot_of_card (by have := hb.q₂_ge; omega) hb.card_X₂) hp.u_inv_X₂ hb.X₂_exp hu

theorem Ch6Pre.shape_ne (h : Ch6Pre D) {α β γ δ : Bool} (hS : D.Shape α β γ δ) :
    α ≠ γ ∧ β = δ :=
  ⟨h.shape_ne_αγ hS, h.shape_eq_βδ hS⟩

end CFSG.GH74.GLS.Stage4.Rest

module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.MaxClassCubes
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_commutator_le_of_rotate {H₁ H₂ H₃ : Subgroup G} (N : Subgroup G) [N.Normal]
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have key : ∀ K : Subgroup G, K ≤ N ↔ K.map π = ⊥ := fun K => by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [key] at h1 h2 ⊢
  simp only [Subgroup.map_commutator] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem lcs_commutator_le : ∀ b a : ℕ,
    ⁅(⊤ : Subgroup G).lowerCentralSeries a, (⊤ : Subgroup G).lowerCentralSeries b⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (a + b + 1) := by
  intro b
  induction b with
  | zero =>
    intro a
    rw [Subgroup.lowerCentralSeries_zero, Subgroup.lowerCentralSeries_succ]
  | succ b ih =>
    intro a
    have hN : ((⊤ : Subgroup G).lowerCentralSeries (a + (b + 1) + 1)).Normal :=
      inferInstance
    rw [Subgroup.commutator_comm, Subgroup.lowerCentralSeries_succ (n := b)]
    apply commutator_commutator_le_of_rotate (H₁ := (⊤ : Subgroup G).lowerCentralSeries b)
      (H₂ := ⊤) (H₃ := (⊤ : Subgroup G).lowerCentralSeries a)
    · have e : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G).lowerCentralSeries a⁆ =
          (⊤ : Subgroup G).lowerCentralSeries (a + 1) := by
        rw [Subgroup.commutator_comm, ← Subgroup.lowerCentralSeries_succ]
      rw [e]
      exact (ih (a + 1)).trans (Subgroup.lowerCentralSeries_antitone _ (by omega))
    · refine (Subgroup.commutator_mono (ih a) le_rfl).trans ?_
      rw [← Subgroup.lowerCentralSeries_succ]
      exact Subgroup.lowerCentralSeries_antitone _ (by omega)

theorem commutator_mem_lcs_succ {k : ℕ} {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries k)
    (g : G) : ⁅a, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
  rw [Subgroup.lowerCentralSeries_succ]
  exact Subgroup.commutator_mem_commutator ha (Subgroup.mem_top g)

theorem commutator_mem_lcs_succ' {k : ℕ} {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries k)
    (g : G) : ⁅g, a⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ (commutator_mem_lcs_succ ha g)

@[expose] def lcsFil (M : Subgroup G) (j : ℕ) : Subgroup G :=
  if j ≤ 1 then M else (⊤ : Subgroup G).lowerCentralSeries (j - 1)

theorem lcsFil_of_le {M : Subgroup G} {j : ℕ} (hj : j ≤ 1) : lcsFil M j = M := by simp [lcsFil, hj]

theorem lcsFil_of_gt {M : Subgroup G} {j : ℕ} (hj : 2 ≤ j) :
    lcsFil M j = (⊤ : Subgroup G).lowerCentralSeries (j - 1) := by simp [lcsFil, show ¬ j ≤ 1 by omega]

theorem lcsFil_normal (M : Subgroup G) [M.Normal] (j : ℕ) : (lcsFil M j).Normal := by
  by_cases h : j ≤ 1
  · rw [lcsFil_of_le h]; infer_instance
  · rw [lcsFil_of_gt (by omega)]; infer_instance

theorem lcsFil_anti (M : Subgroup G) (hM : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ M)
    {j l : ℕ} (hjl : j ≤ l) : lcsFil M l ≤ lcsFil M j := by
  by_cases hl : l ≤ 1
  · rw [lcsFil_of_le hl, lcsFil_of_le (by omega)]
  · rw [lcsFil_of_gt (by omega)]
    by_cases hj : j ≤ 1
    · rw [lcsFil_of_le hj]
      exact (Subgroup.lowerCentralSeries_antitone _ (by omega : 1 ≤ l - 1)).trans hM
    · rw [lcsFil_of_gt (by omega)]
      exact Subgroup.lowerCentralSeries_antitone _ (by omega)

theorem lcsFil_comm (M : Subgroup G) {j l : ℕ} (hj : 1 ≤ j) (hl : 1 ≤ l) {a b : G}
    (ha : a ∈ lcsFil M j) (hb : b ∈ lcsFil M l) : ⁅a, b⁆ ∈ lcsFil M (j + l) := by
  by_cases hj1 : j = 1
  · subst hj1
    rw [lcsFil_of_le le_rfl] at ha
    by_cases hl1 : l = 1
    · subst hl1
      rw [lcsFil_of_gt (by omega)]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    · rw [lcsFil_of_gt (by omega : 2 ≤ l)] at hb
      rw [lcsFil_of_gt (by omega : 2 ≤ 1 + l), show 1 + l - 1 = (l - 1) + 1 by omega]
      exact commutator_mem_lcs_succ' hb a
  · rw [lcsFil_of_gt (by omega : 2 ≤ j)] at ha
    by_cases hl1 : l = 1
    · subst hl1
      rw [lcsFil_of_gt (by omega : 2 ≤ j + 1), show j + 1 - 1 = (j - 1) + 1 by omega]
      exact commutator_mem_lcs_succ ha b
    · rw [lcsFil_of_gt (by omega : 2 ≤ l)] at hb
      rw [lcsFil_of_gt (by omega : 2 ≤ j + l)]
      have := lcs_commutator_le (G := G) (l - 1) (j - 1)
      rw [show j - 1 + (l - 1) + 1 = j + l - 1 by omega] at this
      exact this (Subgroup.commutator_mem_commutator ha hb)

theorem lcsFil_cx_mem (M : Subgroup G) (x : G) {j : ℕ} (hj : 1 ≤ j) {w : G}
    (hw : w ∈ lcsFil M j) : cx x w ∈ lcsFil M (j + 1) := by
  have hwi : w⁻¹ ∈ lcsFil M j := (lcsFil M j).inv_mem hw
  have hcw : cx x w = ⁅w⁻¹, x⁆ := by simp [cx, commutatorElement_def, mul_assoc]
  rw [hcw]
  by_cases hj1 : j = 1
  · subst hj1
    rw [lcsFil_of_gt (by omega)]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rw [lcsFil_of_gt (by omega : 2 ≤ j)] at hwi
    rw [lcsFil_of_gt (by omega : 2 ≤ j + 1), show j + 1 - 1 = (j - 1) + 1 by omega]
    exact commutator_mem_lcs_succ hwi x

theorem CubeSetup.of_lcs (M : Subgroup G) [M.Normal] (hM : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ M)
    {n : ℕ} (hn : 2 ≤ n) (hbot : (⊤ : Subgroup G).lowerCentralSeries (n - 1) = ⊥) {x : G}
    (hx : x ^ 3 = 1)
    (hsurj : ∀ j, 1 ≤ j → j + 2 ≤ n → ∀ z ∈ lcsFil M (j + 1),
      ∃ y ∈ lcsFil M j, ∃ w ∈ lcsFil M (j + 2), z = cx x y * w)
    (hinj : ∀ j, 1 ≤ j → j + 2 ≤ n → ∀ y ∈ lcsFil M j, y ∉ lcsFil M (j + 1) →
      cx x y ∉ lcsFil M (j + 2)) :
    CubeSetup x (lcsFil M) n where
  normal := lcsFil_normal M
  anti _ _ h := lcsFil_anti M hM h
  comm j l hj hl a ha b hb := lcsFil_comm M hj hl ha hb
  bot := by
    rw [lcsFil_of_gt (by omega)]; exact hbot
  hx := hx
  hc j hj w hw := lcsFil_cx_mem M x hj hw
  hsurj := hsurj
  hinj := hinj

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

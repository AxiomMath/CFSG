module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageNextStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}

section Linear

variable (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem perm_v_szA₁ (n : normalizer (U : Set G)) {b : G} (hb : b ∈ szA₁ (szT₁ L T)) :
    H.perm n (v b) = v ((n : G) * b * (n : G)⁻¹) + H.perm n 0 := by
  obtain ⟨w, hw, rfl⟩ := H.exists_pow_eq_of_mem_szA₁ hb
  rw [H.perm_apply n hw, H.perm_zero n, conj_pow]

theorem perm_v_szA₁_of_mem_centralizer (n : normalizer (U : Set G))
    (hn : (n : G) ∈ centralizer ({t} : Set G)) {b : G} (hb : b ∈ szA₁ (szT₁ L T)) :
    H.perm n (v b) = v ((n : G) * b * (n : G)⁻¹) := by
  rw [H.perm_v_szA₁ n hb, H.perm_zero_of_mem_centralizer n hn, add_zero]

theorem perm_eq_add_of_conj_szA₁ (n : normalizer (U : Set G))
    (hn : ∀ b ∈ szA₁ (szT₁ L T), (n : G) * b * (n : G)⁻¹ = b) (s : K) :
    H.perm n s = H.perm n 0 + s := by
  obtain ⟨b, hb, rfl⟩ := H.coords.surj s
  rw [H.perm_v_szA₁ n hb, hn b hb, add_comm]

theorem conj_szA₁_of_perm_eq_add (n : normalizer (U : Set G))
    (htr : ∀ s, H.perm n s = H.perm n 0 + s) :
    ∀ b ∈ szA₁ (szT₁ L T), (n : G) * b * (n : G)⁻¹ = b := by
  refine H.conj_szA₁_of_X_conj n.2 fun w hw => ?_
  have e1 := H.perm_apply n hw
  rw [htr, H.perm_zero, add_comm] at e1
  exact (add_right_cancel e1).symm

end Linear

structure RegData (H : U3C1Next G L f t T d V U U₁ k K v μ) (E : Subgroup (Equiv.Perm K)) :
    Prop where
  le : E ≤ H.perm.range
  normal : (E.subgroupOf H.perm.range).Normal
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  sq : ∀ x ∈ E, x ^ 2 = 1
  card : Nat.card E = 2 ^ f
  reg : ∀ β γ : K, ∃! e : E, (e : Equiv.Perm K) β = γ
  trans : ∀ e ∈ E, ∀ c, e c = e 0 + c

structure NextUData (H : U3C1Next G L f t T d V U U₁ k K v μ) (U' : Subgroup G) : Prop where
  le : U' ≤ normalizer (U : Set G)
  normal : normalizer (U : Set G) ≤ normalizer (U' : Set G)
  U_le : U ≤ U'
  trans : ∀ x (hx : x ∈ U') (s : K), H.perm ⟨x, le hx⟩ s = H.perm ⟨x, le hx⟩ 0 + s
  mem_U : ∀ x (hx : x ∈ U'), H.perm ⟨x, le hx⟩ 0 = 0 → x ∈ U
  surj : ∀ s : K, ∃ x, ∃ hx : x ∈ U', H.perm ⟨x, le hx⟩ 0 = s
  conj_T₁ : ∀ x ∈ U', ∀ y ∈ szT₁ L T, y⁻¹ * (x * y * x⁻¹) ∈ szA₁ (szT₁ L T)

end U3C1Next

end CFSG.SeitzReduction.RankOne

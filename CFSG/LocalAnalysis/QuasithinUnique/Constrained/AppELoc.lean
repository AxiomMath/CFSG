module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Core

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

structure Loc (B L U Q W : Subgroup G) (q : ℕ) : Prop where
  rk : C5.Rank1 B Q U W q
  q2 : 2 ≤ q
  hZ : (U ⊓ centralizer (L : Set G)).relIndex U = q ^ 2
  hgen : ∀ y ∈ normalizer (B : Set G), ¬ conjSubgroup U y ≤ Q → ¬ conjSubgroup U y⁻¹ ≤ Q →
    ∃ k ∈ L, L ≤ conjSubgroup U y ⊔ conjSubgroup (conjSubgroup U y) k
  hLQ : L ≤ normalizer (Q : Set G)
  hUL : U ≤ L
  hcommZ : ∀ y ∈ B, y ∉ Q → ∀ u ∈ U, ⁅u, y⁆ ∈ U ⊓ centralizer (L : Set G) → ⁅u, y⁆ = 1

namespace Rank1

variable {B Q U W : Subgroup G} {q : ℕ}

theorem rank1_conj (h : C5.Rank1 B Q U W q) {g : G} (hg : g ∈ normalizer (B : Set G)) :
    C5.Rank1 B (conjSubgroup Q g) (conjSubgroup U g) (conjSubgroup W g) q := by
  have hB : ∀ y : G, y ∈ B ↔ g * y * g⁻¹ ∈ B := fun y => Subgroup.mem_normalizer_iff.1 hg y
  refine
    { U_le_Q := conjSubgroup_mono h.U_le_Q g
      Q_le_B := ?_
      B_le_normQ := h.B_le_normQ_conj hg
      B_le_normU := h.B_le_normU_conj hg
      Q_eq := h.conj_Q_eq hg
      W_le_U := conjSubgroup_mono h.W_le_U g
      idx_Q := ?_
      idx_W := ?_
      q_ne_zero := h.q_ne_zero
      cent_y := ?_
      comm_UB := ?_
      U_comm := h.conj_comm g }
  · have := conjSubgroup_mono h.Q_le_B g
    rwa [conjSubgroup_eq_self hg] at this
  · have := relIndex_conjSubgroup Q B g
    rwa [conjSubgroup_eq_self hg, h.idx_Q] at this
  · have := relIndex_conjSubgroup W U g
    rwa [h.idx_W] at this
  · intro y hy hyQ u hu
    rw [mem_conjSubgroup_iff] at hu
    have hy' : g * y * g⁻¹ ∈ B := (hB y).1 hy
    have hyQ' : g * y * g⁻¹ ∉ Q := by
      intro hq
      apply hyQ
      rw [mem_conjSubgroup_iff]
      exact hq
    have key := h.cent_y _ hy' hyQ' _ hu
    have hconj : (g * u * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * u * g⁻¹) ↔ u * y = y * u := by
      have e : (g * u * g⁻¹) * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by group
      have e' : (g * y * g⁻¹) * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
      rw [e, e']
      constructor
      · intro hc
        exact mul_left_cancel (mul_right_cancel hc)
      · intro hc
        rw [hc]
    rw [mem_conjSubgroup_iff, key, hconj]
  · have := conjSubgroup_commutator U B g
    rw [conjSubgroup_eq_self hg, h.comm_UB] at this
    exact this.symm

end Rank1

theorem conj_conj_comm (V : Subgroup G) (g k' : G) :
    conjSubgroup (conjSubgroup V g) (g⁻¹ * k' * g) = conjSubgroup (conjSubgroup V k') g := by
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
    show g * (g⁻¹ * k' * g) = k' * g by group]

namespace Loc

variable {B L U Q W : Subgroup G} {q : ℕ}

theorem conj (h : Loc B L U Q W q) {g : G} (hg : g ∈ normalizer (B : Set G)) :
    Loc B (conjSubgroup L g) (conjSubgroup U g) (conjSubgroup Q g) (conjSubgroup W g) q := by
  have hB : ∀ y : G, y ∈ B ↔ g * y * g⁻¹ ∈ B := fun y => Subgroup.mem_normalizer_iff.1 hg y
  refine
    { rk := Rank1.rank1_conj h.rk hg
      q2 := h.q2
      hZ := ?_
      hgen := ?_
      hLQ := ?_
      hUL := conjSubgroup_mono h.hUL g
      hcommZ := ?_ }
  · rw [← conjSubgroup_centralizer, ← conjSubgroup_inf, relIndex_conjSubgroup]
    exact h.hZ
  · intro y hy hy1 hy2
    have hy' : g * y * g⁻¹ ∈ normalizer (B : Set G) :=
      mul_mem (mul_mem hg hy) (inv_mem hg)
    have hy'inv : (g * y * g⁻¹)⁻¹ = g * y⁻¹ * g⁻¹ := by group
    have e1 : conjSubgroup (conjSubgroup U g) y = conjSubgroup (conjSubgroup U (g * y * g⁻¹)) g := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    have e2 : conjSubgroup (conjSubgroup U g) y⁻¹ =
        conjSubgroup (conjSubgroup U (g * y * g⁻¹)⁻¹) g := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, hy'inv]
      congr 1
      group
    rw [e1] at hy1
    rw [e2] at hy2
    have h1 : ¬ conjSubgroup U (g * y * g⁻¹) ≤ Q := fun hle => hy1 (conjSubgroup_mono hle g)
    have h2 : ¬ conjSubgroup U (g * y * g⁻¹)⁻¹ ≤ Q := fun hle => hy2 (conjSubgroup_mono hle g)
    obtain ⟨k', hk'L, hk'⟩ := h.hgen _ hy' h1 h2
    refine ⟨g⁻¹ * k' * g, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have : g * (g⁻¹ * k' * g) * g⁻¹ = k' := by group
      rw [this]
      exact hk'L
    · rw [e1, conj_conj_comm, ← C5.conjSubgroup_sup]
      exact conjSubgroup_mono hk' g
  · have := conjSubgroup_mono h.hLQ g
    rwa [conjSubgroup_normalizer] at this
  · intro y hy hyQ u hu hcom
    rw [mem_conjSubgroup_iff] at hu
    have hy' : g * y * g⁻¹ ∈ B := (hB y).1 hy
    have hyQ' : g * y * g⁻¹ ∉ Q := by
      intro hq
      apply hyQ
      rw [mem_conjSubgroup_iff]
      exact hq
    have hc : ⁅g * u * g⁻¹, g * y * g⁻¹⁆ ∈ U ⊓ centralizer (L : Set G) := by
      have e : ⁅g * u * g⁻¹, g * y * g⁻¹⁆ = g * ⁅u, y⁆ * g⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      have : ⁅u, y⁆ ∈ conjSubgroup (U ⊓ centralizer (L : Set G)) g := by
        rw [C5.conjSubgroup_inf, conjSubgroup_centralizer]
        exact hcom
      rw [mem_conjSubgroup_iff] at this
      exact this
    have h1 := h.hcommZ _ hy' hyQ' _ hu hc
    have e : ⁅g * u * g⁻¹, g * y * g⁻¹⁆ = g * ⁅u, y⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e] at h1
    have h2 : ⁅u, y⁆ = g⁻¹ * 1 * g := by
      rw [← h1]; group
    rw [h2]; group

end Loc

end CFSG.QuasithinUnique.AppE

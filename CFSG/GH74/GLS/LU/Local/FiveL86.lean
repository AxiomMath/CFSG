module

public import CFSG.GH74.GLS.LU.Local.FiveL86c
public import CFSG.GH74.GLS.LU.Local.FiveLeaves

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L86

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg.P_NN (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) : w₁ * v ∈ NN z u :=
  mul_mem c.w₁_NN c.b84.v_N

theorem Cfg.t_comm_UU (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    ∀ x ∈ UU z u, t * x = x * t := by
  intro x hx
  have hle : UU z u ≤ centralizer ({t} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr c.hs.zt_comm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr c.hs.ut
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem Cfg.conj_cent_UU (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) {n : G} (hn : n ∈ NN z u) :
    n⁻¹ * t * n ∈ centralizer ((UU z u : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hy : n * x * n⁻¹ ∈ UU z u := (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  have h1 := c.t_comm_UU _ hy
  calc x * (n⁻¹ * t * n) = n⁻¹ * ((n * x * n⁻¹) * t) * n := by group
    _ = n⁻¹ * (t * (n * x * n⁻¹)) * n := by rw [h1.symm]
    _ = (n⁻¹ * t * n) * x := by group

theorem Cfg.X5_tv (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    cjL (t * v) (X5 v w₁ X₁) = X5 v w₁ X₁ := by
  have hPN := c.P_NN
  have hA : X5 v w₁ X₁ = cjL (w₁ * v) X₁ := X5_eq v w₁ X₁
  have hHA : HInv H (X5 v w₁ X₁) := c.hinv_X5
  generalize X5 v w₁ X₁ = A at hA hHA ⊢
  generalize hP : w₁ * v = P at hA hPN
  have hPinv : P⁻¹ ∈ NN z u := inv_mem hPN
  have hPz : P * z * P⁻¹ = u := by rw [← hP]; exact c.g_z
  have hL : cjL t (cjL P K₁) = cjL P K₁ := (c.b66.t_normL P hPz).1
  generalize hDdef : cjL P⁻¹ (cjL t A) = D
  have hDK : D ≤ K₁ := by
    have h1 : cjL t A ≤ cjL P K₁ := by
      rw [hA]
      have h0 : cjL P X₁ ≤ cjL P K₁ := cjL_mono P c.b82.X₁_syl.1
      have h2 := cjL_mono t h0
      rwa [hL] at h2
    have h2 := cjL_mono P⁻¹ h1
    rw [hDdef, cjL_cjL, inv_mul_cancel, cjL_one] at h2
    exact h2
  have hDcard : Nat.card ↥D = 5 := by
    rw [← hDdef, card_cjL, card_cjL, hA, card_cjL]; exact c.card_X1
  have hDH : HInv H D := by
    have h1 : HInv H (cjL t A) := hHA.conj c.b66.t_normH
    rw [← hDdef]
    exact h1.conj (c.cjL_H hPinv)
  have hDeq : cjL t A = cjL P D := by
    rw [← hDdef, cjL_cjL, mul_inv_cancel, cjL_one]
  have hnot : D ≠ X₁ := by
    intro hD1
    have hmN : cjL (P⁻¹ * t * P) X₁ = X₁ := by
      have : cjL (P⁻¹ * t * P) X₁ = D := by
        rw [← hDdef, hA]
        have e : P⁻¹ * t * P = P⁻¹ * (t * P) := by group
        rw [e, ← cjL_cjL, ← cjL_cjL]
      rw [this, hD1]
    have hmC : P⁻¹ * t * P ∈ centralizer ((UU z u : Subgroup G) : Set G) := c.conj_cent_UU hPN
    have htC : t ∈ centralizer ((UU z u : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun x hx => (c.t_comm_UU x hx).symm)
    have hm'C : t * (P⁻¹ * t * P) * t⁻¹ ∈ centralizer ((UU z u : Subgroup G) : Set G) :=
      mul_mem (mul_mem htC hmC) (inv_mem htC)
    have hm'N : t * (P⁻¹ * t * P) * t⁻¹ ∈ normalizer ((XB t X₁ : Subgroup G) : Set G) := by
      apply mem_normalizer_of_cjL_eq
      show cjL (t * (P⁻¹ * t * P) * t⁻¹) (cjL t X₁) = cjL t X₁
      calc cjL (t * (P⁻¹ * t * P) * t⁻¹) (cjL t X₁)
          = cjL (t * (P⁻¹ * t * P) * t⁻¹ * t) X₁ := cjL_cjL _ _ _
        _ = cjL (t * (P⁻¹ * t * P)) X₁ := by congr 1; group
        _ = cjL t (cjL (P⁻¹ * t * P) X₁) := (cjL_cjL _ _ _).symm
        _ = cjL t X₁ := by rw [hmN]
    have hm'H := c.CU_inf_N_X2_le_H hm'C hm'N
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right c.t_sq
    have hmH : P⁻¹ * t * P ∈ H := by
      have h1 : t⁻¹ * (t * (P⁻¹ * t * P) * t⁻¹) * t⁻¹⁻¹ ∈ cjL t⁻¹ H := mem_cjL_self hm'H
      have h2 : cjL t⁻¹ H = H := by rw [htinv]; exact c.b66.t_normH
      rw [h2] at h1
      have : t⁻¹ * (t * (P⁻¹ * t * P) * t⁻¹) * t⁻¹⁻¹ = P⁻¹ * t * P := by group
      rwa [this] at h1
    have htH : t ∈ H := by
      have h1 : P * (P⁻¹ * t * P) * P⁻¹ ∈ cjL P H := mem_cjL_self hmH
      rw [c.cjL_H hPN] at h1
      have : P * (P⁻¹ * t * P) * P⁻¹ = t := by group
      rwa [this] at h1
    exact c.t_notin_H htH
  have hD2 : D = cjL w₁ X₁ := (c.invSyl_K1 hDK hDcard hDH).resolve_left hnot
  have hvA : cjL v A = cjL t A := by
    rw [hDeq, hD2, hA, cjL_cjL, cjL_cjL, ← hP]
    have e : v * (w₁ * v) = v * w₁ * v := by group
    rw [e]
    exact c.cjL_braid c.hinv_X1
  rw [← cjL_cjL, hvA, cjL_cjL, c.t_sq, cjL_one]

end L86

theorem leaf86 : Leaf86 := by
  intro G _ _ p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84 b85
  have c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v := ⟨⟨⟨⟨ctx, b66, b82⟩, b83⟩, b84⟩, b85⟩
  exact ⟨c.X6_v, c.X5_tv, c.X5_ne⟩

end CFSG.GH74.GLS.LU.Local.Five

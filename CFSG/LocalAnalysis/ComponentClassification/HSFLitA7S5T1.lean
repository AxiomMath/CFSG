module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5Transl

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

@[expose] def gBCols : Fin 4 → V4 := ![(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1), (1, 0, 0, 1)]

theorem gBCols_fix : ∀ i j l : Fin 2, lin gBCols (i, 0, j, l) ≠ (i, 0, j, l) ∨ (j = 0 ∧ l = 0) := by
  decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

omit H in
theorem conj_mem_normalizer_of_map {P P' : Subgroup X} {g n : X}
    (hg : P.map (MulAut.conj g).toMonoidHom = P') (hn : n ∈ normalizer (P' : Set X)) :
    g⁻¹ * n * g ∈ normalizer (P : Set X) := by
  refine mem_normalizer_of_map_eq ?_
  have e : g⁻¹ * n * g = g⁻¹ * (n * g) := by group
  rw [e, map_conj_mul, map_conj_mul, hg, map_eq_of_mem_normalizer hn, map_conj_inv hg]

theorem conj_g_k {g : X} (hgE : (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E S.y) :
    g * S.k * g⁻¹ = S.z * S.k := by
  have hkE : g * S.k * g⁻¹ ∈ S.inst₂.E := by
    show _ ∈ S.E S.y
    rw [← hgE]
    exact ⟨S.k, S.inst₁.k_mem_E, rfl⟩
  have hfix : ∀ n ∈ normalizer (S.inst₂.E : Set X), n * (g * S.k * g⁻¹) * n⁻¹ = g * S.k * g⁻¹ := by
    intro n hn
    have h1 : g⁻¹ * n * g ∈ normalizer (S.inst₁.E : Set X) :=
      conj_mem_normalizer_of_map hgE hn
    have h2 := H.k_fixed S.inst₁ h1
    have h3 : S.inst₁.ki = S.k := rfl
    rw [h3] at h2
    calc n * (g * S.k * g⁻¹) * n⁻¹ = g * ((g⁻¹ * n * g) * S.k * (g⁻¹ * n * g)⁻¹) * g⁻¹ := by
          group
      _ = g * S.k * g⁻¹ := by rw [h2]
  rcases H.eq_of_fixed S.inst₂ hkE hfix with h | h
  · exfalso
    apply S.k_ne_one
    calc S.k = g⁻¹ * (g * S.k * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem conj_g_t {g : X} (hg : g ∈ T₁) (hgT : g ∉ S.T₂of T₁) :
    g * S.t * g⁻¹ = S.t * S.k ∨ g * S.t * g⁻¹ = S.t * S.z * S.k := by
  obtain ⟨w₀, hw₀, hw₀T⟩ := H.exists_w₀
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hb := S.conj_mem_B (H.le_normalizer hg) htB
  have hnot : ¬ (g * S.t * g⁻¹ = S.t ∨ g * S.t * g⁻¹ = w₀ * S.t * w₀⁻¹) := fun h =>
    hgT ((H.mem_T₂_iff hw₀ hw₀T hg).mpr h)
  rw [H.conj_w₀_t hw₀ hw₀T] at hnot
  rcases (H.fus _ hb).mp ⟨g, rfl⟩ with h | h | h | h
  · exact absurd (Or.inl h) hnot
  · exact absurd (Or.inr h) hnot
  · exact Or.inl h
  · exact Or.inr h

theorem exists_g : ∃ g ∈ T₁, g ∉ S.T₂of T₁ ∧
    (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E S.y ∧
    g * S.t * g⁻¹ = S.t * S.k ∧ g * S.k * g⁻¹ = S.z * S.k := by
  obtain ⟨g₀, hg₀, hg₀T, hg₀E⟩ := H.exists_g₀
  obtain ⟨w, hwT₂, -, hw⟩ := H.exists_tz S.inst₁
  have hg₀z : g₀ * S.z * g₀⁻¹ = S.z := S.conj_z_eq (H.le_normalizer hg₀)
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hzk : S.z * S.k = S.k * S.z := S.z_comm_of_mem_T S.k_mem
  rcases H.conj_g_t hg₀ hg₀T with h | h
  · exact ⟨g₀, hg₀, hg₀T, hg₀E, h, H.conj_g_k hg₀E⟩
  · have hwt : w * S.t * w⁻¹ = S.t * S.z := by
      rw [hw.conj_t]; simp [transCols, Inst.wV, hzt]
    have hgw : g₀ * w ∉ S.T₂of T₁ := fun h' => hg₀T (by
      have := mul_mem h' (inv_mem hwT₂)
      rwa [mul_inv_cancel_right] at this)
    have hgwE : (S.E (S.x * S.y)).map (MulAut.conj (g₀ * w)).toMonoidHom = S.E S.y := by
      rw [map_conj_mul, map_eq_of_mem_normalizer (mem_inf.mp hwT₂).2, hg₀E]
    refine ⟨g₀ * w, mul_mem hg₀ (T₂of_le hwT₂), hgw, hgwE, ?_, H.conj_g_k hgwE⟩
    calc g₀ * w * S.t * (g₀ * w)⁻¹ = g₀ * (w * S.t * w⁻¹) * g₀⁻¹ := by group
      _ = (g₀ * S.t * g₀⁻¹) * (g₀ * S.z * g₀⁻¹) := by rw [hwt]; group
      _ = S.t * S.k := by
          rw [h, hg₀z]
          calc S.t * S.z * S.k * S.z = S.t * S.z * (S.k * S.z) := by group
            _ = S.t * S.z * (S.z * S.k) := by rw [hzk]
            _ = S.t * (S.z * S.z) * S.k := by group
            _ = S.t * S.k := by rw [← pow_two, S.z_sq, mul_one]

theorem sq_not_mem_T {g : X} (hg : g ∈ T₁) (hgt : g * S.t * g⁻¹ = S.t * S.k)
    (hgk : g * S.k * g⁻¹ = S.z * S.k) : g ^ 2 ∉ S.data.T := by
  intro h
  have hz : g * S.z * g⁻¹ = S.z := S.conj_z_eq (H.le_normalizer hg)
  have hzk : S.z * S.k = S.k * S.z := S.z_comm_of_mem_T S.k_mem
  have h2 : g ^ 2 * S.t * (g ^ 2)⁻¹ = S.t * S.z := by
    calc g ^ 2 * S.t * (g ^ 2)⁻¹ = g * (g * S.t * g⁻¹) * g⁻¹ := by rw [pow_two]; group
      _ = g * (S.t * S.k) * g⁻¹ := by rw [hgt]
      _ = (g * S.t * g⁻¹) * (g * S.k * g⁻¹) := by group
      _ = S.t * S.k * (S.z * S.k) := by rw [hgt, hgk]
      _ = S.t * (S.k * S.z) * S.k := by group
      _ = S.t * (S.z * S.k) * S.k := by rw [hzk]
      _ = S.t * S.z * (S.k * S.k) := by group
      _ = S.t * S.z := by rw [← pow_two, S.k_sq, mul_one]
  rw [S.data.commute_t h, mul_inv_cancel_right] at h2
  apply S.z_ne_one
  calc S.z = S.t⁻¹ * (S.t * S.z) := by group
    _ = 1 := by rw [← h2]; group

theorem sq_mem_and_eq {g : X} (hg : g ∈ T₁) (hgT : g ∉ S.T₂of T₁) :
    g ^ 2 ∈ S.T₂of T₁ ∧ T₁ = S.T₂of T₁ ⊔ zpowers g := by
  have hN : g ∈ normalizer (S.T₂of T₁ : Set X) :=
    mem_normalizer_of_conj_mem fun h hh => H.conj_mem_T₂of hg hh
  have hsq : g ^ 2 ∈ S.T₂of T₁ := by
    rcases H.mem_or_of_mem hg hgT (pow_mem hg 2) with h | h
    · exact h
    · exfalso
      apply hgT
      rwa [pow_two, inv_mul_cancel_left] at h
  refine ⟨hsq, (Subgroup.eq_of_le_of_card_ge (sup_le T₂of_le (zpowers_le.mpr hg)) ?_).symm⟩
  rw [card_sup_zpowers hN hsq hgT, H.card_T₁_eq]

theorem center_T₁ {g : X} (hg : g ∈ T₁) (hgt : g * S.t * g⁻¹ = S.t * S.k)
    (hgk : g * S.k * g⁻¹ = S.z * S.k) : CenterEq T₁ (zpowers S.z) := by
  intro a ha
  have hzZ : ∀ b ∈ T₁, S.z * b = b * S.z := fun b hb => by
    have := S.conj_z_eq (H.le_normalizer hb)
    calc S.z * b = b * (b⁻¹ * S.z * b) := by group
      _ = b * S.z := by
          congr 1
          calc b⁻¹ * S.z * b = b⁻¹ * (b * S.z * b⁻¹) * b := by rw [this]
            _ = S.z := by group
  constructor
  · intro hc
    have haC : a ∈ T₁ ⊓ centralizer ({S.t} : Set X) := by
      refine mem_inf.mpr ⟨ha, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact hc S.t (H.le S.data.t_mem_T)
    rw [H.inf_centralizer] at haC
    have haB : a ∈ S.B := (S.mem_B_iff haC).mp fun h hh => hc h (H.le hh)
    have hBE : S.B ≤ S.inst₁.E := by
      show S.B ≤ S.E _
      rw [S.E_eq_B_sup]
      exact le_sup_left
    obtain ⟨v, rfl⟩ := S.inst₁.eq_wV (hBE haB)
    have hv1 : v.2.1 = 0 := (S.inst₁.wV_mem_B_iff v).mp haB
    obtain ⟨i, b, j, l⟩ := v
    simp only at hv1
    subst hv1
    have hgz : g * S.z * g⁻¹ = S.z := S.conj_z_eq (H.le_normalizer hg)
    have hga : g * S.inst₁.wV (i, 0, j, l) * g⁻¹ = S.inst₁.wV (lin gBCols (i, 0, j, l)) := by
      rw [S.inst₁.wV_lin]
      have hc' : ∀ e : X, g * e * g⁻¹ = MulAut.conj g e := fun e => rfl
      simp only [Inst.wV, inst₁, hc', map_mul, map_pow]
      simp only [← hc', hgz, hgt, hgk]
      simp [gBCols, mul_assoc]
    have hfix : g * S.inst₁.wV (i, 0, j, l) * g⁻¹ = S.inst₁.wV (i, 0, j, l) := by
      rw [← hc _ hg]; group
    rw [hga] at hfix
    obtain ⟨rfl, rfl⟩ := (gBCols_fix i j l).resolve_left (not_not.mpr (S.inst₁.wV_injective hfix))
    simp only [Inst.wV, inst₁, Fin.val_zero, pow_zero, mul_one]
    exact pow_mem (mem_zpowers _) _
  · intro haz b hb
    obtain ⟨n, rfl⟩ := haz
    exact ((Commute.zpow_left (hzZ b hb) n)).eq

end Sec5Hyp

end A7Base

end CFSG.ComponentClassification.HSFLit

module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NW

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

@[expose] def idCols : Fin 4 → V4 := bas

@[expose] def comp (c₁ c₂ : Fin 4 → V4) : Fin 4 → V4 := fun i => lin c₁ (c₂ i)

@[expose] def pw (c : Fin 4 → V4) (e : Fin 2) : Fin 4 → V4 := if e = 0 then idCols else c

@[expose] def vC : Fin 4 → V4 := ![(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1), (0, 0, 0, 1)]

@[expose] def wC (ε : Fin 2) : Fin 4 → V4 :=
  ![(1, 0, 0, 0), (0, 1, 0, ε), (1, 0, 1, 0), (0, 0, 0, 1)]

@[expose] def w'C (ε : Fin 2) : Fin 4 → V4 :=
  ![(1, 0, 0, ε), (0, 1, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)]

@[expose] def gC (ε a b c : Fin 2) : Fin 4 → V4 :=
  comp (pw vC c) (comp (pw (wC ε) a) (pw (w'C ε) b))

theorem exists_gC : ∀ ε p q r : Fin 2, ∃ a b c : Fin 2,
    lin (gC ε a b c) (bas 2) = (p, q, 1, r) := by
  decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

namespace Inst

variable (I : S.Inst)

theorem μ_pw {n : normalizer (I.E : Set X)} {c : Fin 4 → V4} (hc : ∀ i, I.μ n (bas i) = c i)
    (e : Fin 2) (i : Fin 4) : I.μ (n ^ (e : ℕ)) (bas i) = pw c e i := by
  rcases Fin.exists_fin_two.mp ⟨e, rfl⟩ with rfl | rfl
  · simp [pw, idCols, I.μ_one]
  · simp [pw, hc]

theorem μ_comp {n m : normalizer (I.E : Set X)} {c₁ c₂ : Fin 4 → V4}
    (h₁ : ∀ i, I.μ n (bas i) = c₁ i) (h₂ : ∀ i, I.μ m (bas i) = c₂ i) (i : Fin 4) :
    I.μ (n * m) (bas i) = comp c₁ c₂ i := by
  rw [I.μ_mul_bas, h₂]
  simp only [comp]
  congr 1
  exact funext h₁

theorem exists_vww (H : S.Sec6Hyp T₁) : ∃ ε : Fin 2, (ε = 0 ↔ I.CaseI) ∧
    ∃ v, ∃ hv : v ∈ T₁, ∃ w, ∃ hw : w ∈ T₁, ∃ w', ∃ hw' : w' ∈ normalizer (I.E : Set X),
      (∀ i, I.μ ⟨v, I.T₁_le H hv⟩ (bas i) = vC i) ∧
      (∀ i, I.μ ⟨w, I.T₁_le H hw⟩ (bas i) = wC ε i) ∧ (∀ i, I.μ ⟨w', hw'⟩ (bas i) = w'C ε i) := by
  obtain ⟨v, hv, hvt, hvz, hvy, hvk⟩ := I.exists_v H
  obtain ⟨w, hw, hwt, hwz, hwk, hcase⟩ := I.exists_w H
  obtain ⟨d, hd, hdz, hdy⟩ := I.exists_d
  obtain ⟨hdyi, hdzi, hdzy, hdt, hdti, hdki, hdk⟩ := I.d_rels hd hdz hdy
  have hwN := I.T₁_le H hw
  have htz : S.t * S.z = I.wV (1, 0, 1, 0) := by simp [wV, S.z_comm_of_mem_T S.data.t_mem_T]
  obtain ⟨ε, hε, hwy⟩ : ∃ ε : Fin 2, (ε = 0 ↔ I.CaseI) ∧ w * I.yi * w⁻¹ = I.wV (0, 1, 0, ε) := by
    rcases hcase with ⟨hI, h⟩ | ⟨hI, h⟩
    · exact ⟨0, iff_of_true rfl hI, by rw [h]; simp [wV]⟩
    · exact ⟨1, iff_of_false (by decide) hI, by rw [h]; simp [wV]⟩
  refine ⟨ε, hε, v, hv, w, hw, d * w * d⁻¹, mul_mem (mul_mem hd.1 hwN) (inv_mem hd.1), ?_, ?_, ?_⟩
  · refine I.μ_bas_of ?_ ?_ ?_ ?_
    · show v * S.z * v⁻¹ = _
      rw [hvz]; simp [vC, wV]
    · show v * I.yi * v⁻¹ = _
      rw [hvy]; simp [vC, wV]
    · show v * S.t * v⁻¹ = _
      rw [hvt]; simp [vC, wV]
    · show v * I.ki * v⁻¹ = _
      rw [hvk]; simp [vC, wV]
  · refine I.μ_bas_of ?_ ?_ ?_ ?_
    · show w * S.z * w⁻¹ = _
      rw [hwz]; simp [wC, wV]
    · show w * I.yi * w⁻¹ = _
      rw [hwy]; rfl
    · show w * S.t * w⁻¹ = _
      rw [hwt, htz]; rfl
    · show w * I.ki * w⁻¹ = _
      rw [hwk]; simp [wC, wV]
  · have hwyk : w * I.yi * w⁻¹ = I.yi * I.ki ^ (ε : ℕ) := by rw [hwy]; simp [wV]
    refine I.μ_bas_of ?_ ?_ ?_ ?_
    · show d * w * d⁻¹ * S.z * (d * w * d⁻¹)⁻¹ = _
      calc d * w * d⁻¹ * S.z * (d * w * d⁻¹)⁻¹ = d * (w * (d⁻¹ * S.z * d) * w⁻¹) * d⁻¹ := by
            group
        _ = d * (w * S.z * w⁻¹ * (w * I.yi * w⁻¹)) * d⁻¹ := by rw [hdzi]; group
        _ = (d * S.z * d⁻¹) * (d * I.yi * d⁻¹) * (d * I.ki * d⁻¹) ^ (ε : ℕ) := by
            rw [hwz, hwyk, conj_pow]
            group
        _ = I.yi * (S.z * I.yi) * I.ki ^ (ε : ℕ) := by rw [hdz, hdy, hdk]
        _ = S.z * I.ki ^ (ε : ℕ) := by
            rw [← mul_assoc, ← S.z_comm_of_mem_T I.yi_mem.1, mul_assoc S.z, ← pow_two, I.yi_sq,
              mul_one]
        _ = I.wV (w'C ε 0) := by simp [w'C, wV]
    · show d * w * d⁻¹ * I.yi * (d * w * d⁻¹)⁻¹ = _
      calc d * w * d⁻¹ * I.yi * (d * w * d⁻¹)⁻¹ = d * (w * (d⁻¹ * I.yi * d) * w⁻¹) * d⁻¹ := by
            group
        _ = I.wV (w'C ε 1) := by rw [hdyi, hwz, hdz]; simp [w'C, wV]
    · show d * w * d⁻¹ * S.t * (d * w * d⁻¹)⁻¹ = _
      calc d * w * d⁻¹ * S.t * (d * w * d⁻¹)⁻¹ = d * (w * (d⁻¹ * S.t * d) * w⁻¹) * d⁻¹ := by
            group
        _ = (d * S.t * d⁻¹) * (d * S.z * d⁻¹) := by rw [hdti, hwt]; group
        _ = I.wV (w'C ε 2) := by
            rw [hdt, hdz]
            simp [w'C, wV, (S.data.commute_t I.yi_mem.1).symm]
    · show d * w * d⁻¹ * I.ki * (d * w * d⁻¹)⁻¹ = _
      calc d * w * d⁻¹ * I.ki * (d * w * d⁻¹)⁻¹ = d * (w * (d⁻¹ * I.ki * d) * w⁻¹) * d⁻¹ := by
            group
        _ = I.wV (w'C ε 3) := by rw [hdki, hwk, hdk]; simp [w'C, wV]

theorem classify (H : S.Sec6Hyp T₁) : ∃ ε : Fin 2, (ε = 0 ↔ I.CaseI) ∧
    ∀ n : normalizer (I.E : Set X), ∃ a b c : Fin 2, ∃ σ₁ ∈ three, ∃ σ₂ ∈ three, σ₁ ≠ σ₂ ∧
      ∀ i, I.μ n (bas i) = comp (gC ε a b c) (sigCols σ₁ σ₂) i := by
  obtain ⟨ε, hε, v, hv, w, hw, w', hw', hvc, hwc, hw'c⟩ := I.exists_vww H
  refine ⟨ε, hε, fun n => ?_⟩
  set V : normalizer (I.E : Set X) := ⟨v, I.T₁_le H hv⟩
  set W : normalizer (I.E : Set X) := ⟨w, I.T₁_le H hw⟩
  set W' : normalizer (I.E : Set X) := ⟨w', hw'⟩
  obtain ⟨p, q, r, hnt⟩ := I.conj_t_eq H.fus n.2
  obtain ⟨a, b, c, habc⟩ := exists_gC ε p q r
  set g : normalizer (I.E : Set X) := V ^ (c : ℕ) * (W ^ (a : ℕ) * W' ^ (b : ℕ)) with hg
  have hgc : ∀ i, I.μ g (bas i) = gC ε a b c i := by
    intro i
    rw [hg, I.μ_comp (I.μ_pw hvc c) (fun j => I.μ_comp (I.μ_pw hwc a) (I.μ_pw hw'c b) j)]
    rfl
  have hgt : (g : X) * S.t * (g : X)⁻¹ = (n : X) * S.t * (n : X)⁻¹ := by
    have h1 : (g : X) * S.t * (g : X)⁻¹ = I.wV (gC ε a b c 2) := by
      rw [← hgc, ← I.conj_wV, I.wV_bas_two]
    rw [h1, ← lin_bas (gC ε a b c) 2, habc, hnt,
      show ((p, q, (1 : Fin 2), r) : V4) = addV (0, 0, 1, 0) (p, q, 0, r) by simp [addV],
      I.wV_add]
    simp [wV]
  have hsC : ((g⁻¹ * n : normalizer (I.E : Set X)) : X) ∈ centralizer ({S.t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (g : X)⁻¹ * n * S.t = (g : X)⁻¹ * ((n : X) * S.t * (n : X)⁻¹) * g * ((g : X)⁻¹ * n) := by
          group
      _ = S.t * ((g : X)⁻¹ * n) := by rw [← hgt]; group
  obtain ⟨σ₁, h₁, σ₂, h₂, h12, hσ⟩ := I.cols_of_mem_NC H.fus (g⁻¹ * n) hsC
  refine ⟨a, b, c, σ₁, h₁, σ₂, h₂, h12, fun i => ?_⟩
  have : n = g * (g⁻¹ * n) := by group
  rw [this, I.μ_comp hgc hσ]

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit

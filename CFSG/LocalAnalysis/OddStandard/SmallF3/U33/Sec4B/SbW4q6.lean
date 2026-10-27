module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4qU1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4qU2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_not_comm_y
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxU t tau x₁ x₂ lam) (hgO : g ∉ ctxO t tau x₁ x₂) :
    g * x₁ ^ 2 * g⁻¹ ≠ x₁ ^ 2 := by
  intro h
  have hy : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hlo := w4q_mem_O_of_not_mem (w4q_O_le_U t tau x₁ x₂ lam) (w4q_card_U_eq hc) hg hgO
    (w4q_lam_mem_U t tau x₁ x₂ lam) (w4q_lam_not_mem_O hc)
  have h1 : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
    have h2 : (g⁻¹ * lam) * x₁ ^ 2 * (g⁻¹ * lam)⁻¹ = x₁ ^ 2 := w4q_V_central hc hlo hy
    calc lam * x₁ ^ 2 * lam⁻¹ = g * ((g⁻¹ * lam) * x₁ ^ 2 * (g⁻¹ * lam)⁻¹) * g⁻¹ := by group
      _ = g * x₁ ^ 2 * g⁻¹ := by rw [h2]
      _ = x₁ ^ 2 := h
  exact w4q_lam_y_ne hc h1

theorem w4q_F_le_U
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {v : G}
    (hv1 : ∀ x ∈ ctxU t tau x₁ x₂ lam, v * x * v⁻¹ ∈ ctxU t tau x₁ x₂ lam) :
    cj v (ctxX t tau x₁ x₂) ≤ ctxU t tau x₁ x₂ lam := by
  intro f hf
  have hx : v⁻¹ * f * v ∈ ctxX t tau x₁ x₂ := mem_cj.mp hf
  have h := hv1 _ (w4q_X_le_U hc hx)
  have e : v * (v⁻¹ * f * v) * v⁻¹ = f := by group
  rwa [e] at h

theorem w4q_F_normal (hc : Ctx4C t L S x₁ x₂ lam rho tau) {v : G}
    (hv2 : ∀ x ∈ ctxU t tau x₁ x₂ lam, v⁻¹ * x * v ∈ ctxU t tau x₁ x₂ lam) {u f : G}
    (hu : u ∈ ctxU t tau x₁ x₂ lam) (hf : f ∈ cj v (ctxX t tau x₁ x₂)) :
    u * f * u⁻¹ ∈ cj v (ctxX t tau x₁ x₂) := by
  rw [mem_cj] at hf ⊢
  have h := w4q_U_norm_X hc (hv2 u hu) hf
  have e : (v⁻¹ * u * v) * (v⁻¹ * f * v) * (v⁻¹ * u * v)⁻¹ = v⁻¹ * (u * f * u⁻¹) * v := by
    group
  rwa [e] at h

theorem w4q_F_elem
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) (v : G) :
    CFSG.Open.IsElemAbelian 2 (cj v (ctxX t tau x₁ x₂)) ∧
      Nat.card ↥(cj v (ctxX t tau x₁ x₂)) = 16 :=
  ⟨(w4q_X_facts hc).1.map _, by rw [card_cj]; exact (w4q_X_facts hc).2⟩

theorem w4q_F_le_O
    (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hH : ∀ u ∈ ctxO t tau x₁ x₂, u * u = 1 → u * t = t * u) {v : G}
    (hv1 : ∀ x ∈ ctxU t tau x₁ x₂ lam, v * x * v⁻¹ ∈ ctxU t tau x₁ x₂ lam)
    (hv2 : ∀ x ∈ ctxU t tau x₁ x₂ lam, v⁻¹ * x * v ∈ ctxU t tau x₁ x₂ lam) :
    cj v (ctxX t tau x₁ x₂) ≤ ctxO t tau x₁ x₂ := by
  by_contra hFO
  obtain ⟨hFelem, hFcard⟩ := w4q_F_elem hc v
  have hFU := w4q_F_le_U hc hv1
  have hBge : 8 ≤ Nat.card ↥(cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂) := by
    have h := w4q_card_le_two_inf hFU (w4q_O_le_U t tau x₁ x₂ lam) (w4q_card_U_eq hc)
    rw [hFcard] at h
    omega
  have hne : cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂ ≠ cj v (ctxX t tau x₁ x₂) :=
    fun h => hFO (by rw [← h]; exact inf_le_right)
  have hB8 : Nat.card ↥(cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂) = 8 := by
    have hd : Nat.card ↥(cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂) ∣ 16 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_left : cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂ ≤ cj v (ctxX t tau x₁ x₂))
      rwa [hFcard] at h
    have hle16 : Nat.card ↥(cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂) ≤ 16 :=
      Nat.le_of_dvd (by norm_num) hd
    have hne16 : Nat.card ↥(cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂) ≠ 16 := fun h =>
      hne (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hFcard, h]))
    generalize Nat.card ↥(cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂) = n at hd hle16 hne16 hBge ⊢
    interval_cases n <;> omega
  have hBelem : CFSG.Open.IsElemAbelian 2 (cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂) :=
    hFelem.mono inf_le_left
  have hBS : cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂ ≤ S := by
    intro b hb
    have hbt : b * t = t * b := hH b hb.2 (hBelem.mul_self_eq_one hb)
    rw [← w4q_S_eq hc]
    exact ⟨hFU hb.1, Subgroup.mem_centralizer_singleton_iff.mpr hbt⟩
  have hBnormS : NormalIn (cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂) S := by
    refine ⟨hBS, fun s hs b hb => ?_⟩
    have hsU : s ∈ ctxU t tau x₁ x₂ lam := hc.S_le_U hs
    exact ⟨w4q_F_normal hc hv2 hsU hb.1, w4q_U_norm_O hc hsU hb.2⟩
  have hyB : x₁ ^ 2 ∈ cj v (ctxX t tau x₁ x₂) ⊓ ctxO t tau x₁ x₂ := by
    rcases hc.l46 _ hBnormS hBelem hB8 with h | h | h | h | h <;> rw [h] <;>
      exact Subgroup.subset_closure (by simp)
  apply hFO
  intro f hf
  by_contra hfO
  apply w4q_not_comm_y hc (hFU hf) hfO
  rw [hFelem.comm hf hyB.1, mul_inv_cancel_right]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

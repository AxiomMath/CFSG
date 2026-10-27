module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBYd

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A] [Finite A]

namespace LocalDatum

variable {Δ : LocalDatum X A} {k : A} (h2 : Δ.CaseTwo k) {φ : Δ.Fusion}

namespace TwoBY

variable (YD : TwoBY φ)

omit [Finite A] in
include h2 in
theorem false_of_field_central (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) {y : X}
    (hy : y ∈ YD.Y) (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) (hyz : y ≠ Δ.dz) (hytz : y ≠ Δ.t * Δ.dz)
    {d w₀ : X} (hd : d ∈ Δ.D) (hw₀S : w₀ ∈ Δ.S) (hyeq : y = d * w₀)
    (hw₀D : ∀ d' ∈ Δ.D, w₀ * d' = d' * w₀) (hw₀k : Δ.ψe w₀ = k) (hdz : d = 1 ∨ d = Δ.dz)
    (hyD : Δ.ψe y ∉ Δ.Dbar) : False := by
  have hYD := YD.inter_D hy hy1 hyt hyz hytz hyD
  have h8 := h2.2.2.2.2.1
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right (by rw [← pow_two, h2.2.2.2.1])
  have hxz := TwoB_conj_dz h2 φ hD1
  have hxt' : φ.x⁻¹ * Δ.t * φ.x = Δ.dz := by rw [← hxz]; group
  have hxz' : φ.x⁻¹ * Δ.dz * φ.x = Δ.t := by rw [← TwoB_conj_t h2 φ hD1]; group
  have hzS := Δ.D_le Δ.dz_mem
  have hdY : d ∈ YD.Y := by
    rcases hdz with rfl | rfl
    · exact one_mem _
    · exact YD.dz_mem
  have hw₀Y : w₀ ∈ YD.Y := by
    have := mul_mem (inv_mem hdY) hy
    rwa [hyeq, inv_mul_cancel_left] at this
  have hdD : ∀ d' ∈ Δ.D, d * d' = d' * d := by
    rcases hdz with rfl | rfl
    · intro d' _; rw [one_mul, mul_one]
    · exact fun d' hd' => (Δ.dz_comm hd').symm
  have hyD' : ∀ d' ∈ Δ.D, y * d' = d' * y := fun d' hd' => by
    rw [hyeq, mul_assoc, hw₀D d' hd', ← mul_assoc, hdD d' hd', mul_assoc]
  have htD : ∀ d' ∈ Δ.D, Δ.t * d' = d' * Δ.t := fun d' hd' => (Δ.commute_t (Δ.D_le hd')).symm
  have hzD : ∀ d' ∈ Δ.D, Δ.dz * d' = d' * Δ.dz := fun d' hd' => (Δ.dz_comm hd').symm
  have hmulD : ∀ a b : X, (∀ d' ∈ Δ.D, a * d' = d' * a) → (∀ d' ∈ Δ.D, b * d' = d' * b) →
      ∀ d' ∈ Δ.D, a * b * d' = d' * (a * b) := fun a b ha hb d' hd' => by
    rw [mul_assoc, hb d' hd', ← mul_assoc, ha d' hd', mul_assoc]
  have hYW : ∀ y' ∈ YD.Y, ∀ d' ∈ Δ.D, y' * d' = d' * y' := by
    intro y' hy'
    rcases YD.cases hy hy1 hyt hyz hytz hy' with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · intro d' _; rw [one_mul, mul_one]
    · exact htD
    · exact hzD
    · exact hmulD _ _ htD hzD
    · exact hyD'
    · exact hmulD _ _ htD hyD'
    · exact hmulD _ _ hzD hyD'
    · exact hmulD _ _ (hmulD _ _ htD hzD) hyD'
  have hYW₁ : ∀ y' ∈ YD.Y, ∀ d' ∈ Δ.D,
      y' * (φ.x * d' * φ.x⁻¹) = (φ.x * d' * φ.x⁻¹) * y' := fun y' hy' d' hd' => by
    have h := hYW _ (YD.conj_inv_mem hy') d' hd'
    calc y' * (φ.x * d' * φ.x⁻¹) = φ.x * ((φ.x⁻¹ * y' * φ.x) * d') * φ.x⁻¹ := by group
      _ = φ.x * (d' * (φ.x⁻¹ * y' * φ.x)) * φ.x⁻¹ := by rw [h]
      _ = (φ.x * d' * φ.x⁻¹) * y' := by group
  set b₁ := φ.x * Δ.db * φ.x⁻¹
  have hb₁S : b₁ ∈ Δ.S := φ.conj_mem _ (Δ.D_le Δ.db_mem)
  have hb₁D : ∀ d' ∈ Δ.D, b₁ * d' = d' * b₁ := fun d' hd' =>
    (TwoB_commute φ hD1 hd' Δ.db_mem).symm
  have hb₁2 : b₁ ^ 2 = 1 := by simp only [b₁]; rw [conj_pow, Δ.db_sq]; group
  have hdb_ne : φ.x⁻¹ * b₁ * φ.x = Δ.db := by simp only [b₁]; group
  have hb₁k : Δ.ψe b₁ * k ∈ Δ.Dbar := by
    rcases h2.2.2.2.2.2 _ (Δ.ψe_mem_R hb₁S) (Δ.commute_Dbar hb₁S hb₁D) with h | h
    · exfalso
      obtain ⟨q₁, hq₁, hb | hb⟩ := Δ.mem_Qz_of_centralizes h8 hb₁S hb₁D h
      · have hq₁1 : q₁ ≠ 1 := fun h' => Δ.db_ne_one (by
          rw [← hdb_ne, hb, h']; group)
        have := Δ.eq_t_of_mem_Q hq₁ (hb ▸ hb₁2) hq₁1
        apply Δ.db_ne_dz
        rw [← hdb_ne, hb, this, hxt']
      · have hq₂ : q₁ ^ 2 = 1 := by
          rw [hb, (show Commute q₁ Δ.dz from Δ.commute_of_mem_Q_D hq₁ Δ.dz_mem).mul_pow,
            Δ.dz_sq, mul_one] at hb₁2
          exact hb₁2
        by_cases hq₁1 : q₁ = 1
        · rw [hq₁1, one_mul] at hb
          have := hD1 _ Δ.dz_mem (by rw [← hb, hdb_ne]; exact Δ.db_mem)
          exact Δ.dz_ne_one this
        · rw [Δ.eq_t_of_mem_Q hq₁ hq₂ hq₁1] at hb
          apply Δ.t_not_mem_D
          have h' : Δ.db = Δ.dz * Δ.t := by
            rw [← hdb_ne, hb]
            calc φ.x⁻¹ * (Δ.t * Δ.dz) * φ.x = (φ.x⁻¹ * Δ.t * φ.x) * (φ.x⁻¹ * Δ.dz * φ.x) := by
                  group
              _ = Δ.dz * Δ.t := by rw [hxt', hxz']
          have := mul_mem (inv_mem Δ.dz_mem) (h' ▸ Δ.db_mem)
          rwa [inv_mul_cancel_left] at this
    · exact h
  have hbw : Δ.ψe (b₁ * w₀⁻¹) ∈ Δ.Dbar := by
    rw [Δ.ψe_mul hb₁S (inv_mem hw₀S), Δ.ψe_inv hw₀S, hw₀k]
    have := mul_mem hb₁k (one_mem Δ.Dbar)
    rwa [mul_one, ← hkinv] at this
  have hbwD : ∀ d' ∈ Δ.D, b₁ * w₀⁻¹ * d' = d' * (b₁ * w₀⁻¹) := fun d' hd' => by
    have h' : w₀⁻¹ * d' = d' * w₀⁻¹ := by
      calc w₀⁻¹ * d' = w₀⁻¹ * (d' * w₀) * w₀⁻¹ := by group
        _ = w₀⁻¹ * (w₀ * d') * w₀⁻¹ := by rw [hw₀D d' hd']
        _ = d' * w₀⁻¹ := by group
    rw [mul_assoc, h', ← mul_assoc, hb₁D d' hd', mul_assoc]
  obtain ⟨q₁, hq₁, hc⟩ := Δ.mem_Qz_of_centralizes h8 (mul_mem hb₁S (inv_mem hw₀S)) hbwD hbw
  have hb₁eq : b₁ = (b₁ * w₀⁻¹) * w₀ := by group
  have hw₀2 : w₀ ^ 2 = 1 := YD.elem.sq_eq_one w₀ hw₀Y
  have hcomm := hYW₁ w₀ hw₀Y Δ.db Δ.db_mem
  have hcY : b₁ * w₀⁻¹ ∈ YD.Y := by
    have hcw : (b₁ * w₀⁻¹) * w₀ = w₀ * (b₁ * w₀⁻¹) := by
      have : w₀ * b₁ = b₁ * w₀ := hcomm
      calc b₁ * w₀⁻¹ * w₀ = b₁ := by group
        _ = w₀⁻¹ * (w₀ * b₁) := by group
        _ = w₀⁻¹ * (b₁ * w₀) := by rw [this]
        _ = w₀ * (b₁ * w₀⁻¹) := by
            rw [inv_eq_of_mul_eq_one_right (by rw [← pow_two, hw₀2] : w₀ * w₀ = 1)]
    have hc2 : (b₁ * w₀⁻¹) ^ 2 = 1 := by
      have := hb₁2
      rw [hb₁eq, (show Commute (b₁ * w₀⁻¹) w₀ from hcw).mul_pow, hw₀2, mul_one] at this
      exact this
    rcases hc with h | h
    · rw [h] at hc2 ⊢
      by_cases hq1 : q₁ = 1
      · rw [hq1]; exact one_mem _
      · rw [Δ.eq_t_of_mem_Q hq₁ hc2 hq1]; exact YD.t_mem
    · rw [h] at hc2 ⊢
      have hq2 : q₁ ^ 2 = 1 := by
        rw [(show Commute q₁ Δ.dz from Δ.commute_of_mem_Q_D hq₁ Δ.dz_mem).mul_pow, Δ.dz_sq,
          mul_one] at hc2
        exact hc2
      by_cases hq1 : q₁ = 1
      · rw [hq1, one_mul]; exact YD.dz_mem
      · rw [Δ.eq_t_of_mem_Q hq₁ hq2 hq1]; exact mul_mem YD.t_mem YD.dz_mem
  have hb₁Y : b₁ ∈ YD.Y := by rw [hb₁eq]; exact mul_mem hcY hw₀Y
  have hdbY : Δ.db ∈ YD.Y := by rw [← hdb_ne]; exact YD.conj_inv_mem hb₁Y
  rcases hYD _ hdbY Δ.db_mem with h | h
  · exact Δ.db_ne_one h
  · exact Δ.db_ne_dz h

end TwoBY

end LocalDatum

end CFSG.ComponentClassification.HSDihedral

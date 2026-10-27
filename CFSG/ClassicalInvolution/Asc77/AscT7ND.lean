module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenSubStab
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonTwelve
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7N

section Reps

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem R_le_centralizer_of_r_comm (c : Thompson.Ctx p f Ω W) (σ : Rep Ω W) {u : G} (huW : u ∈ W)
    (h : σ.r * u = u * σ.r) : σ.R ≤ Subgroup.centralizer ({u} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hxW : x ∈ W
  · exact c.comm_W x hxW u huW
  · have hy : σ.r⁻¹ * x ∈ W := D_inv_mul_mem c.hp c.hq c.hΩ c.hW σ.hR σ.hr hx σ.hrW hxW
    have hxy : x = σ.r * (σ.r⁻¹ * x) := by group
    have hyu : (σ.r⁻¹ * x) * u = u * (σ.r⁻¹ * x) := c.comm_W _ hy u huW
    calc x * u = σ.r * ((σ.r⁻¹ * x) * u) := by rw [hxy]; group
      _ = σ.r * (u * (σ.r⁻¹ * x)) := by rw [hyu]
      _ = (σ.r * u) * (σ.r⁻¹ * x) := by rw [mul_assoc]
      _ = (u * σ.r) * (σ.r⁻¹ * x) := by rw [h]
      _ = u * (σ.r * (σ.r⁻¹ * x)) := by rw [mul_assoc]
      _ = u * x := by group

end Reps

section Adapted

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_adapted_involution (c : Thompson.Ctx p f Ω W) (ρ₁ ρ₂ ρ_L : Rep Ω W) {z z_L : G}
    (hz₁ : IsUniqueInvolution ρ₁.K z) (hz₂ : IsUniqueInvolution ρ₂.K z)
    (hzL : IsUniqueInvolution ρ_L.K z_L) (h12 : ρ₁.K ≠ ρ₂.K) (hL1 : ρ_L.K ≠ ρ₁.K)
    (hL2 : ρ_L.K ≠ ρ₂.K) (hnb1 : ρ_L.K ∉ omegaNbr Ω ρ₁.K) :
    ∃ u : G, u ∈ W ∧ u ∈ ρ₁.K ⊔ ρ₂.K ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧
      ρ_L.R ≤ Subgroup.centralizer ({u} : Set G) ∧
      ∀ σ : Rep Ω W, σ.K ∈ omegaNbr Ω ρ₁.K → σ.K ∈ omegaNbr Ω ρ₂.K →
        σ.R ≤ Subgroup.centralizer ({u} : Set G) := by
  classical
  have hp := c.hp
  have hq := c.hq
  have hΩ := c.hΩ
  have hW := c.hW
  have hab := c.comm_W
  obtain ⟨w, hwR, hw4⟩ := exists_orderOf_four hp hq hΩ hW ρ₁.hR
  obtain ⟨v, hvR, hv4⟩ := exists_orderOf_four hp hq hΩ hW ρ₂.hR
  have hwK : w ∈ ρ₁.K ⊓ W := ⟨ρ₁.hRK.1 hwR.1, hwR.2⟩
  have hvK : v ∈ ρ₂.K ⊓ W := ⟨ρ₂.hRK.1 hvR.1, hvR.2⟩
  have hw2 : w * w = z := sq_eq_involution_of_orderOf_four hz₁ hwK.1 hw4
  have hv2 : v * v = z := sq_eq_involution_of_orderOf_four hz₂ hvK.1 hv4
  have hzW : z ∈ W := hw2 ▸ W.mul_mem hwK.2 hwK.2
  have hzz : z * z = 1 := hz₁.sq
  have hwv : w * v = v * w := hab w hwK.2 v hvK.2
  have hu₀sq' : (w * v) * (w * v) = 1 := by
    calc (w * v) * (w * v) = w * (v * w) * v := by group
      _ = w * (w * v) * v := by rw [hwv]
      _ = (w * w) * (v * v) := by group
      _ = 1 := by rw [hw2, hv2, hzz]
  have hu₀W' : w * v ∈ W := W.mul_mem hwK.2 hvK.2
  set u₀ := w * v with hu₀
  have hu₀W : u₀ ∈ W := hu₀W'
  have hu₀sq : u₀ * u₀ = 1 := hu₀sq'
  have hno4 : ∀ y : G, y ∈ ρ₁.K → y ∈ ρ₂.K → orderOf y ≠ 4 := by
    intro y hy1 hy2 hy4
    have hdvd : 4 ∣ Nat.card ↥(ρ₁.K ⊓ ρ₂.K) := by
      have := Subgroup.orderOf_dvd_natCard (ρ₁.K ⊓ ρ₂.K) (⟨hy1, hy2⟩ : y ∈ ρ₁.K ⊓ ρ₂.K)
      rwa [hy4] at this
    have hval := (hΩ.omega4 ρ₁.K ρ₁.hK ρ₂.K ρ₂.hK h12).1
    have h4le : 2 ≤ padicValNat 2 (Nat.card ↥(ρ₁.K ⊓ ρ₂.K)) := by
      have : 2 ^ 2 ∣ Nat.card ↥(ρ₁.K ⊓ ρ₂.K) := by simpa using hdvd
      exact (padicValNat_dvd_iff_le Nat.card_pos.ne').mp this
    omega
  have hu₀1 : u₀ ≠ 1 := by
    intro h1
    have hvw : v = w⁻¹ := by
      have : w * v = 1 := h1
      exact eq_inv_of_mul_eq_one_right this
    exact hno4 v (hvw ▸ ρ₁.K.inv_mem hwK.1) hvK.1 hv4
  have hu₀z : u₀ ≠ z := by
    intro h1
    have hvw : v = w⁻¹ * z := by
      have : w * v = z := h1
      calc v = w⁻¹ * (w * v) := by group
        _ = w⁻¹ * z := by rw [this]
    have hzK1 : z ∈ ρ₁.K := hz₁.mem
    exact hno4 v (hvw ▸ ρ₁.K.mul_mem (ρ₁.K.inv_mem hwK.1) hzK1) hvK.1 hv4
  have hcw : ρ_L.r * w * ρ_L.r⁻¹ * w⁻¹ ∈ ρ_L.K ⊓ W := c.comm_mem ρ_L ρ₁ hL1 hwK
  have hcv : ρ_L.r * v * ρ_L.r⁻¹ * v⁻¹ ∈ ρ_L.K ⊓ W := c.comm_mem ρ_L ρ₂ hL2 hvK
  set e₁ := ρ_L.r * w * ρ_L.r⁻¹ * w⁻¹ with he₁
  set e₂ := ρ_L.r * v * ρ_L.r⁻¹ * v⁻¹ with he₂
  have hr₁ : ρ_L.r * w * ρ_L.r⁻¹ = e₁ * w := by rw [he₁]; group
  have hr₂ : ρ_L.r * v * ρ_L.r⁻¹ = e₂ * v := by rw [he₂]; group
  set e := e₁ * e₂ with he
  have heL : e ∈ ρ_L.K := ρ_L.K.mul_mem hcw.1 hcv.1
  have heW : e ∈ W := W.mul_mem hcw.2 hcv.2
  have hru₀ : ρ_L.r * u₀ * ρ_L.r⁻¹ = e * u₀ := by
    have h1 : ρ_L.r * u₀ * ρ_L.r⁻¹ = (ρ_L.r * w * ρ_L.r⁻¹) * (ρ_L.r * v * ρ_L.r⁻¹) := by
      rw [hu₀]; group
    rw [h1, hr₁, hr₂]
    have h2 : e₂ * w = w * e₂ := hab e₂ hcv.2 w hwK.2
    calc e₁ * w * (e₂ * v) = e₁ * (w * e₂) * v := by group
      _ = e₁ * (e₂ * w) * v := by rw [h2]
      _ = (e₁ * e₂) * (w * v) := by group
  have hesq : e * e = 1 := by
    have hconj : (ρ_L.r * u₀ * ρ_L.r⁻¹) * (ρ_L.r * u₀ * ρ_L.r⁻¹) = 1 := by
      calc (ρ_L.r * u₀ * ρ_L.r⁻¹) * (ρ_L.r * u₀ * ρ_L.r⁻¹) = ρ_L.r * (u₀ * u₀) * ρ_L.r⁻¹ := by
            group
        _ = 1 := by rw [hu₀sq]; group
    rw [hru₀] at hconj
    have heu : e * u₀ = u₀ * e := hab e heW u₀ hu₀W
    calc e * e = (e * e) * (u₀ * u₀) := by rw [hu₀sq, mul_one]
      _ = (e * u₀) * (e * u₀) := by
          calc (e * e) * (u₀ * u₀) = e * (e * u₀) * u₀ := by group
            _ = e * (u₀ * e) * u₀ := by rw [heu]
            _ = (e * u₀) * (e * u₀) := by group
      _ = 1 := hconj
  have hrz : ρ_L.r * z * ρ_L.r⁻¹ = z_L * z :=
    c.conj_involution ρ_L ρ₁ hL1 (fun hnb => hnb1 (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ
      ρ_L.hK ρ₁.hK hnb)) hzL hz₁
  have hzLW : z_L ∈ W :=
    (uniqueInvolution_mem_W hp hq hΩ hW ρ_L.hK ρ_L.hR ρ_L.hRK hzL).2
  have hzc : ∀ x ∈ W, x * z = z * x := fun x hx => hab x hx z hzW
  obtain ⟨u, hucases, hcomm⟩ : ∃ u : G, (u = u₀ ∨ u = u₀ * z) ∧ ρ_L.r * u = u * ρ_L.r := by
    rcases hzL.unique e heL hesq with he1 | hez
    · refine ⟨u₀, Or.inl rfl, ?_⟩
      have : ρ_L.r * u₀ * ρ_L.r⁻¹ = u₀ := by rw [hru₀, he1, one_mul]
      exact mul_inv_eq_iff_eq_mul.mp this
    · refine ⟨u₀ * z, Or.inr rfl, ?_⟩
      have h1 : ρ_L.r * (u₀ * z) * ρ_L.r⁻¹ = (ρ_L.r * u₀ * ρ_L.r⁻¹) * (ρ_L.r * z * ρ_L.r⁻¹) := by
        group
      have h2 : ρ_L.r * (u₀ * z) * ρ_L.r⁻¹ = u₀ * z := by
        rw [h1, hru₀, hrz, hez]
        have hzu : z_L * u₀ = u₀ * z_L := hab z_L hzLW u₀ hu₀W
        have hzz' : z_L * z = z * z_L := hab z_L hzLW z hzW
        calc z_L * u₀ * (z_L * z) = (z_L * u₀) * z_L * z := by group
          _ = (u₀ * z_L) * z_L * z := by rw [hzu]
          _ = u₀ * (z_L * z_L) * z := by group
          _ = u₀ * z := by rw [hzL.sq, mul_one]
      exact mul_inv_eq_iff_eq_mul.mp h2
  have huW : u ∈ W := by
    rcases hucases with rfl | rfl
    · exact hu₀W
    · exact W.mul_mem hu₀W hzW
  have hu_sq : u * u = 1 := by
    rcases hucases with rfl | rfl
    · exact hu₀sq
    · have hc : z * u₀ = u₀ * z := hzc u₀ hu₀W |>.symm
      calc u₀ * z * (u₀ * z) = u₀ * (z * u₀) * z := by group
        _ = u₀ * (u₀ * z) * z := by rw [hc]
        _ = (u₀ * u₀) * (z * z) := by group
        _ = 1 := by rw [hu₀sq, hzz, one_mul]
  have hu_ne1 : u ≠ 1 := by
    rcases hucases with rfl | rfl
    · exact hu₀1
    · intro h1
      have : u₀ = z⁻¹ := eq_inv_of_mul_eq_one_left h1
      exact hu₀z (this.trans (inv_eq_of_mul_eq_one_left hzz))
  have hu_nez : u ≠ z := by
    rcases hucases with rfl | rfl
    · exact hu₀z
    · intro h1
      have : u₀ = 1 := by
        have h2 : u₀ * z = 1 * z := by rw [h1, one_mul]
        exact mul_right_cancel h2
      exact hu₀1 this
  have hu_mem : u ∈ ρ₁.K ⊔ ρ₂.K := by
    have h0 : u₀ ∈ ρ₁.K ⊔ ρ₂.K :=
      (ρ₁.K ⊔ ρ₂.K).mul_mem (Subgroup.mem_sup_left hwK.1) (Subgroup.mem_sup_right hvK.1)
    have hz' : z ∈ ρ₁.K ⊔ ρ₂.K := Subgroup.mem_sup_left hz₁.mem
    rcases hucases with rfl | rfl
    · exact h0
    · exact (ρ₁.K ⊔ ρ₂.K).mul_mem h0 hz'
  refine ⟨u, huW, hu_mem, hu_sq, hu_ne1, hu_nez,
    R_le_centralizer_of_r_comm c ρ_L huW hcomm, fun σ hσ1 hσ2 => ?_⟩
  have hnb1' : ρ₁.K ∈ omegaNbr Ω σ.K := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ ρ₁.hK σ.hK hσ1
  have hnb2' : ρ₂.K ∈ omegaNbr Ω σ.K := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ ρ₂.hK σ.hK hσ2
  have hzK : z ∈ ρ₁.K ⊓ W := ⟨hz₁.mem, hzW⟩
  have hσw : σ.r * w = w * σ.r := c.centralizes σ ρ₁ hnb1' hwK
  have hσv : σ.r * v = v * σ.r := c.centralizes σ ρ₂ hnb2' hvK
  have hσz : σ.r * z = z * σ.r := c.centralizes σ ρ₁ hnb1' hzK
  have hσu₀ : σ.r * u₀ = u₀ * σ.r := by
    calc σ.r * (w * v) = (σ.r * w) * v := (mul_assoc σ.r w v).symm
      _ = (w * σ.r) * v := by rw [hσw]
      _ = w * (σ.r * v) := mul_assoc w σ.r v
      _ = w * (v * σ.r) := by rw [hσv]
      _ = (w * v) * σ.r := (mul_assoc w v σ.r).symm
  refine R_le_centralizer_of_r_comm c σ huW ?_
  rcases hucases with rfl | rfl
  · exact hσu₀
  · calc σ.r * (u₀ * z) = (σ.r * u₀) * z := (mul_assoc σ.r u₀ z).symm
      _ = (u₀ * σ.r) * z := by rw [hσu₀]
      _ = u₀ * (σ.r * z) := mul_assoc u₀ σ.r z
      _ = u₀ * (z * σ.r) := by rw [hσz]
      _ = (u₀ * z) * σ.r := (mul_assoc u₀ z σ.r).symm

end Adapted

end T7N

end CFSG.ClassicalInvolution.Asc77

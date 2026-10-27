module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Dih
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.QuatMod
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.IV2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

theorem dih_index2_invol : Dih_index2_invol := by
  intro G _ D M n _ hidx hD _
  obtain ⟨-, k, -, hk2, ⟨e⟩⟩ := hD
  refine Dih.exists_invol_not_mem hk2 e (fun hle => ?_)
  have := Subgroup.relIndex_eq_one.2 hle
  omega

theorem Pz_eq_sup_std (hII : II4_4_4_center) {G : Type} [Group G] [Finite G] {z : G}
    {S K₁ K₂ : Subgroup G} (h : Std4 G z S K₁ K₂) : Pz S z = Pof S K₁ ⊔ Pof S K₂ := by
  have hM := m4_of_std hII h
  have e1 : M.Pm S K₁ K₂ ⊓ K₁ = Pof S K₁ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  have e2 : M.Pm S K₁ K₂ ⊓ K₂ = Pof S K₂ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_right : K₂ ≤ K₁ ⊔ K₂)]
  rw [Pz_eq h, hM.P_eq, e1, e2]

theorem ig_10_32_P (hII : II4_4_4_center) : IG_10_32_P := by
  intro G _ _ z S K₁ K₂ hstd x hxS hxo hxint v hv hv2
  have hM := m4_of_std hII hstd
  have hzS : z ∈ S := hM.z_mem_S
  have hzP₁ : z ∈ Pof S K₁ := ⟨hzS, hM.z_mem_comp (Or.inl rfl)⟩
  have hPeq := Pz_eq_sup_std hII hstd
  have hcom : ∀ a ∈ Pof S K₁, ∀ b ∈ Pof S K₂, a * b = b * a := fun _ ha _ hb =>
    hM.comm_of_S ha.2 hb.2 ha.1 hb.1
  have hinf : Pof S K₁ ⊓ Pof S K₂ = zpowers z := by
    apply le_antisymm
    · rintro y ⟨⟨hyS, hyK₁⟩, ⟨-, hyK₂⟩⟩
      have hy : y ∈ S ⊓ M.ZsM (pPrimeCoreOf 2) K₁ := ⟨hyS, hyK₁, hM.cs₁ hyK₂⟩
      rw [(hM.S_inf_Zs_comp (Or.inl rfl)).2] at hy
      exact hy
    · exact zpowers_le.2 ⟨hzP₁, ⟨hzS, hM.z_mem_comp (Or.inr rfl)⟩⟩
  have hz2 : z * z = 1 := hM.z_sq
  have hx2 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hxo
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hv2' : v * v = 1 := mul_self_eq_one_of_orderOf_eq_two hv2
  have hzc : ∀ s ∈ S, s * z = z * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (hM.S_syl.1 hs)
  obtain ⟨hc1, hc2⟩ := (interchanges_iff x).1 hxint
  have hx₁ : ∀ p ∈ Pof S K₁, x * p * x⁻¹ ∈ Pof S K₂ := fun p hp =>
    ⟨S.mul_mem (S.mul_mem hxS hp.1) (S.inv_mem hxS), by
      have : p ∈ M.cj K₂ x := by rw [hc2]; exact hp.2
      exact M.mem_cj.1 this⟩
  have hx₂ : ∀ p ∈ Pof S K₂, x * p * x⁻¹ ∈ Pof S K₁ := fun p hp =>
    ⟨S.mul_mem (S.mul_mem hxS hp.1) (S.inv_mem hxS), by
      have : p ∈ M.cj K₁ x := by rw [hc1]; exact hp.2
      exact M.mem_cj.1 this⟩
  obtain ⟨p₁, hp₁, p₂, hp₂, hvp⟩ :=
    A.mem_sup_of_commute hcom (hPeq ▸ hv : v * x⁻¹ ∈ Pof S K₁ ⊔ Pof S K₂)
  have hv' : v = p₁ * p₂ * x := by
    have : v = v * x⁻¹ * x := by group
    rw [this, hvp]
  obtain ⟨a, ha⟩ : ∃ a, a = x * p₂ * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = x * p₁ * x⁻¹ := ⟨_, rfl⟩
  have haP : a ∈ Pof S K₁ := ha ▸ hx₂ p₂ hp₂
  have hbP : b ∈ Pof S K₂ := hb ▸ hx₁ p₁ hp₁
  have h1 : p₁ * p₂ * b * a = 1 := by
    have e : v * v = p₁ * p₂ * b * a * (x * x) := by
      rw [hv', ha, hb]
      group
    rw [hx2, mul_one] at e
    rw [← e]
    exact hv2'
  have h2 : (p₁ * a) * (p₂ * b) = 1 := by
    calc (p₁ * a) * (p₂ * b) = p₁ * (a * p₂) * b := by group
      _ = p₁ * (p₂ * a) * b := by rw [hcom a haP p₂ hp₂]
      _ = p₁ * p₂ * (a * b) := by group
      _ = p₁ * p₂ * (b * a) := by rw [hcom a haP b hbP]
      _ = p₁ * p₂ * b * a := by group
      _ = 1 := h1
  have hε₁ : p₁ * a ∈ Pof S K₁ := (Pof S K₁).mul_mem hp₁ haP
  have hε₂ : p₁ * a ∈ Pof S K₂ := by
    rw [eq_inv_of_mul_eq_one_left h2]
    exact (Pof S K₂).inv_mem ((Pof S K₂).mul_mem hp₂ hbP)
  have hεz : p₁ * a ∈ zpowers z := hinf.le ⟨hε₁, hε₂⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hεz
  have hp₂' : p₂ = x⁻¹ * (p₁⁻¹ * (p₁ * a)) * x := by
    rw [ha]
    group
  have hvε : v = p₁ * x * p₁⁻¹ * (p₁ * a) := by
    calc v = p₁ * p₂ * x := hv'
      _ = p₁ * (x⁻¹ * (p₁⁻¹ * (p₁ * a)) * x) * x := by rw [← hp₂']
      _ = p₁ * x⁻¹ * p₁⁻¹ * (p₁ * a) * (x * x) := by group
      _ = p₁ * x * p₁⁻¹ * (p₁ * a) := by rw [hx2, mul_one, hxinv]
  have hPmem : p₁ ∈ Pz S z := hPeq ▸ mem_sup_left hp₁
  refine ⟨p₁, hPmem, ?_⟩
  rcases B.zpow_of_sq_eq_one hz2 k with h3 | h3
  · left
    have : p₁ * a = 1 := hk.symm.trans h3
    rw [hvε, this, mul_one]
  · right
    have h4 : p₁ * a = z := hk.symm.trans h3
    have hzp : p₁⁻¹ * z = z * p₁⁻¹ := by
      have := hzc p₁ hp₁.1
      calc p₁⁻¹ * z = p₁⁻¹ * (z * p₁) * p₁⁻¹ := by group
        _ = p₁⁻¹ * (p₁ * z) * p₁⁻¹ := by rw [this]
        _ = z * p₁⁻¹ := by group
    rw [hvε, h4]
    calc p₁ * (x * z) * p₁⁻¹ = p₁ * x * (z * p₁⁻¹) := by group
      _ = p₁ * x * (p₁⁻¹ * z) := by rw [hzp]
      _ = p₁ * x * p₁⁻¹ * z := by group


theorem quat_mod_center : Quat_mod_center := by
  intro G _ P z n hP hz hz2
  obtain ⟨hn, ⟨e⟩⟩ := hP
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  obtain ⟨hnorm, ⟨e'⟩⟩ := QM.quot_equiv e hz hz2
  refine ⟨hnorm, 2 ^ (n - 2), ?_, ?_, ⟨e'⟩⟩
  · rw [← pow_succ']
    congr 1
    omega
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)


theorem iv2_2_5 : IV2_2_5 := by
  intro G _ _ T P₁ P₂ Q₁ Q₂ U z _ hT hTQ hn₁ hn₂ hq₁ hq₂ hz hz₁ hz₂ hp₁ hp₂ h21 h12 hc₁ hc₂ hU hPU
  obtain ⟨-, ⟨e₁⟩⟩ := hq₁
  obtain ⟨-, ⟨e₂⟩⟩ := hq₂
  obtain ⟨-, ⟨f₁⟩⟩ := hp₁
  obtain ⟨-, ⟨f₂⟩⟩ := hp₂
  have hU2 : ∀ a ∈ U, a * a = 1 := by
    intro a ha
    have := hU.1
    have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) a ha
    simpa [pow_two] using h2
  exact IV2.iv2_core hT hTQ hn₁ hn₂ (e₁ : ↥Q₁ ≃* QuaternionGroup 4) (e₂ : ↥Q₂ ≃* QuaternionGroup 4)
    hz hz₁ hz₂ (f₁ : ↥P₁ ≃* QuaternionGroup 2) (f₂ : ↥P₂ ≃* QuaternionGroup 2) h21 h12 hc₁ hc₂ hU2
    hU.2 hPU

end CFSG.GH74.GLS.Stage1.Thm3.Sec7

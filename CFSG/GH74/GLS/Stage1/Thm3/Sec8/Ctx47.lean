module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx46
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx43
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic13

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G}

theorem exists_t_P (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1))
    (hY : YData S K₁ W₂ U h Y) (eY : ↥Y ≃* Bg.TwoGroups.SylSL3_4) :
    ∃ t ∈ Nh S h, t ∉ Wsub S U ∧ t * t = 1 ∧ t * u * t⁻¹ = u * z ∧ t * h * t⁻¹ = h⁻¹ ∧
      t ∈ Pz S z := by
  obtain ⟨t₀, ht₀P, ht₀sq, ht₀u⟩ := hs.exists_t₀ hII hq hk
  have ht₀S : t₀ ∈ S := ht₀P.1
  obtain ⟨y, hy, t, ht, hyt⟩ := hY.decomp t₀ ht₀S
  have htW : t ∉ Wsub S U := by
    intro htW
    apply hs.t₀_not_mem_W hII ht₀S ht₀u
    rw [hyt]
    exact mul_mem (hY.le_W hy) htW
  have ht2 : t * t = 1 := by
    have h1 : t * t = (y * (t * y * t⁻¹))⁻¹ := by
      calc t * t = (y * (t * y * t⁻¹))⁻¹ * ((y * t) * (y * t)) := by group
        _ = (y * (t * y * t⁻¹))⁻¹ := by rw [← hyt, ht₀sq, mul_one]
    have h2 : t * t ∈ Y := by
      rw [h1]
      exact inv_mem (mul_mem hy (hY.norm_D t ht y hy))
    have h3 : t * t ∈ Y ⊓ Nh S h := Subgroup.mem_inf.2 ⟨h2, mul_mem ht ht⟩
    rw [hY.Y_inf_Nh hII hs, Subgroup.mem_bot] at h3
    exact h3
  have hth : t * h * t⁻¹ = h⁻¹ := hs.Nh_not_W_inv hII ht htW
  have htu : t * u * t⁻¹ = u * z := hs.conj_u_of_not_mem_W hII ht.1 htW
  refine ⟨t, ht, htW, ht2, htu, hth, ?_⟩
  have hUA : U ≤ Aof S K₁ W₂ h := hs.U_le_A hII hq hrec (le_refl _) hk
  have hUY : U ≤ Y := hUA.trans hY.A_le
  obtain ⟨hcomm, hcentral⟩ := Basic.comm_central_of_equiv eY hUY hs.U_four.2
    (fun y hy w hw => hs.U_norm y (hY.Y_le_S hy) w hw)
  have hQ := hs.Q_mem_U hII hq hrec hk hY hcomm hcentral hy
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hty : t * y * t⁻¹ = y⁻¹ := by
    have h1 : y * t * (y * t) = 1 := by rw [← hyt]; exact ht₀sq
    calc t * y * t⁻¹ = t * y * t := by rw [ht']
      _ = y⁻¹ * (y * t * (y * t)) := by group
      _ = y⁻¹ := by rw [h1, mul_one]
  have hth' : t * h⁻¹ * t⁻¹ = h := by
    rw [show t * h⁻¹ * t⁻¹ = (t * h * t⁻¹)⁻¹ by group, hth, inv_inv]
  have hty₁ : t * (h⁻¹ * y * h) * t⁻¹ = h * y⁻¹ * h⁻¹ := by
    calc t * (h⁻¹ * y * h) * t⁻¹ = (t * h⁻¹ * t⁻¹) * (t * y * t⁻¹) * (t * h * t⁻¹) := by group
      _ = h * y⁻¹ * h⁻¹ := by rw [hth', hty, hth]
  have hy₁ : h⁻¹ * y * h ∈ Y := hY.conj_h y hy
  have hconj : (h⁻¹ * y * h) * t₀ * (h⁻¹ * y * h)⁻¹ = (((h⁻¹ * y * h) * y) * (h * y * h⁻¹)) * t := by
    calc (h⁻¹ * y * h) * t₀ * (h⁻¹ * y * h)⁻¹ = (h⁻¹ * y * h) * (y * t) * (h⁻¹ * y * h)⁻¹ := by
          rw [hyt]
      _ = ((h⁻¹ * y * h) * y * (t * (h⁻¹ * y * h) * t⁻¹)⁻¹) * t := by group
      _ = (((h⁻¹ * y * h) * y) * (h * y * h⁻¹)) * t := by rw [hty₁]; group
  have hP1 := hs.S_normalizes_Pz hII (hY.Y_le_S hy₁) t₀ ht₀P
  rw [hconj] at hP1
  have hQP : ((h⁻¹ * y * h) * y) * (h * y * h⁻¹) ∈ Pz S z := hs.U_le_Pz hII hq hQ
  have : t = (((h⁻¹ * y * h) * y) * (h * y * h⁻¹))⁻¹ *
      ((((h⁻¹ * y * h) * y) * (h * y * h⁻¹)) * t) := by group
  rw [this]
  exact mul_mem (inv_mem hQP) hP1

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8

module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic18
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx50

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y E₁ E₂ : Subgroup G} {t w : G}

theorem w_comm_U (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (cfg : Cfg88 z S K₁ W₂ U u h Y t w) :
    ∀ c ∈ U, w * c = c * w := fun c hc => by
  have := hs.W_cent_U cfg.hwW hc
  calc w * c = (w * c * w⁻¹) * w := by group
    _ = c * w := by rw [this]

theorem conj_E₁_w (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) (cfg : Cfg88 z S K₁ W₂ U u h Y t w)
    (hE : EData Y U E₁ E₂) (hcentral : ∀ y ∈ Y, ∀ c ∈ U, y * c = c * y)
    (hCw : Y ⊓ centralizer ({w} : Set G) = U) : conjugate E₁ w = E₂ := by
  have hY := cfg.hY
  have hwS : w ∈ S := Nh_le_S cfg.hwD
  have hSN : S ≤ normalizer (Y : Set G) := hY.S_le_normalizer
  have hwYinv : ∀ y ∈ Y, w⁻¹ * y * w ∈ Y := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.1 (hSN (inv_mem hwS)) y).1 hy
    simpa using this
  have hE₁sq := E₁_sq hE
  have hE'sq : ∀ x ∈ conjugate E₁ w, x * x = 1 := conj_sq w hE₁sq
  have hE'Y : conjugate E₁ w ≤ Y := by
    intro x hx
    have h1 : w * x * w⁻¹ ∈ E₁ := mem_conjugate_iff.1 hx
    have h2 := hwYinv _ (hE.le₁ h1)
    have e : w⁻¹ * (w * x * w⁻¹) * w = x := by group
    rwa [e] at h2
  have hE'card : Nat.card ↥(conjugate E₁ w) = 16 := by rw [conjugate_card]; exact hE.card₁
  rcases Basic.elem_eq_or_of_le hE'Y hE'sq (invol_of_EData hE) hE.card₁ hE.card₂ hE'card with h1 | h1
  · exfalso
    have hwE : ∀ e ∈ E₁, w * e * w⁻¹ ∈ E₁ := fun e he => by
      have : e ∈ conjugate E₁ w := by rw [h1]; exact he
      exact mem_conjugate_iff.1 this
    have hUE₁ : U ≤ E₁ := hE.inter ▸ inf_le_left
    have hwU := hs.w_comm_U cfg
    obtain ⟨e, he, hez⟩ := Basic.exists_mul_conj_eq (E := E₁) (K := U) (d := w) (k := z)
      hE.elem₁.1 hE₁sq hwE cfg.hw2
      (fun e he => ⟨fun hc => by
        rw [← hCw]
        exact Subgroup.mem_inf.2 ⟨hE.le₁ he, Subgroup.mem_centralizer_singleton_iff.2 hc.symm⟩,
        fun hc => hwU e hc⟩)
      hUE₁ hE.card₁ hs.U_four.2 hs.z_mem
    have hee : e * e = 1 := hE₁sq e he
    have hwe : w * e * w⁻¹ = e * z := by
      calc w * e * w⁻¹ = e⁻¹ * (e * (w * e * w⁻¹)) := by group
        _ = e⁻¹ * z := by rw [hez]
        _ = e * z := by rw [inv_eq_of_mul_eq_one_right hee]
    obtain ⟨x, hVx, -, -, -, hz⟩ := hs.xdata hII hq hk
    have hxV : x ∈ Vof S K₁ W₂ := hVx ▸ Subgroup.mem_zpowers x
    have hxA : x ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left hxV
    have hxY : x ∈ Y := hY.A_le hxA
    have hzz := hs.z_sq
    have hz1 : z ≠ 1 := hs.z_ne
    have hxinv : x⁻¹ = x * z := inv_eq_of_mul_eq_one_right (by
      calc x * (x * z) = (x * x) * z := by group
        _ = z * z := by rw [← hz]
        _ = 1 := hzz)
    have hwx : w * x * w⁻¹ = x * z := by rw [cfg.hinvA x hxA, hxinv]
    have hezc : e * z = z * e := hcentral e (hE.le₁ he) z hs.z_mem
    have hxe : w * (x * e) * w⁻¹ = x * e := by
      calc w * (x * e) * w⁻¹ = (w * x * w⁻¹) * (w * e * w⁻¹) := by group
        _ = (x * z) * (e * z) := by rw [hwx, hwe]
        _ = x * (z * e) * z := by group
        _ = x * (e * z) * z := by rw [hezc]
        _ = x * e * (z * z) := by group
        _ = x * e := by rw [hzz, mul_one]
    have hxeU : x * e ∈ U := by
      rw [← hCw]
      refine Subgroup.mem_inf.2 ⟨mul_mem hxY (hE.le₁ he), Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc x * e * w = (w * (x * e) * w⁻¹) * w := by rw [hxe]
        _ = w * (x * e) := by group
    have hxE : x ∈ E₁ := by
      have : x = (x * e) * e⁻¹ := by group
      rw [this]
      exact mul_mem (hUE₁ hxeU) (inv_mem he)
    have := hE₁sq x hxE
    rw [← hz] at this
    exact hz1 this
  · exact h1

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8

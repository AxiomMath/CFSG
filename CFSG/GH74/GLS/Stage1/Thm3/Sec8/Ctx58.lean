module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx57
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic15
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic16

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y E₁ E₂ : Subgroup G} {t w : G}

theorem exists_x₀ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) (hE : EData Y U E₁ E₂) (hUY : U ≤ Y)
    (hcentral : ∀ y ∈ Y, ∀ c ∈ U, y * c = c * y)
    (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ U) (hsq : ∀ a ∈ Y, a * a ∈ U)
    (hswap : ∀ y, (t * w) * y * (t * w)⁻¹ ∈ E₁ ↔ y ∈ E₂)
    (hCw : Y ⊓ centralizer ({w} : Set G) = U) :
    32 ≤ Nat.card ↥(S ⊓ centralizer ({t * w} : Set G)) ∧
      ∃ x₀ ∈ S, x₀ * (t * w) = (t * w) * x₀ ∧ x₀ ^ 4 = z := by
  have hY := cfg.hY
  have hd2 := tw_sq cfg
  have hdD := d_mem_Nh cfg
  have hdY : ∀ y ∈ Y, (t * w) * y * (t * w)⁻¹ ∈ Y := hY.norm_D _ hdD
  have hdz := d_z hII hs cfg
  have hdu := d_u hs cfg
  have hQ8 := Basic.card_cent_ge_eight hUY (fun c hc y hy => (hcentral y hy c hc).symm) hcomm hsq
    hY.card hs.U_four.2 hdY hd2 hs.U_elems hs.z_mem hs.u_mem hs.z_ne hdz hdu
  have hwd : w * (t * w) = (t * w) * w := Nh_comm cfg w cfg.hwD _ hdD
  have hzQ : z ∈ Y ⊓ centralizer ({t * w} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hUY hs.z_mem, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc z * (t * w) = ((t * w) * z * (t * w)⁻¹) * (t * w) := by rw [hdz]
      _ = (t * w) * z := by group
  have huniq : ∀ x ∈ Y ⊓ centralizer ({t * w} : Set G), x * x = 1 → x = 1 ∨ x = z := by
    intro x hx hx2
    have hxd : x * (t * w) = (t * w) * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    have hxdd : (t * w) * x * (t * w)⁻¹ = x := by rw [← hxd]; group
    have hxU : x ∈ U := by
      rcases invol_of_EData hE x hx.1 hx2 with h1 | h1
      · have h2 : x ∈ E₂ := (hswap x).1 (by rw [hxdd]; exact h1)
        rw [← hE.inter]
        exact Subgroup.mem_inf.2 ⟨h1, h2⟩
      · have h2 : x ∈ E₁ := by
          have := (hswap x).2 h1
          rwa [hxdd] at this
        rw [← hE.inter]
        exact Subgroup.mem_inf.2 ⟨h2, h1⟩
    exact cent_U_d hII hs cfg x hxU hxd
  have hexp : ∀ x ∈ Y ⊓ centralizer ({t * w} : Set G), x ^ 4 = 1 := by
    intro x hx
    have h2 := hs.four_sq _ (hsq x hx.1)
    have e : x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    exact h2
  have hwN : ∀ x ∈ Y ⊓ centralizer ({t * w} : Set G),
      w * x * w⁻¹ ∈ Y ⊓ centralizer ({t * w} : Set G) := by
    intro x hx
    have hwS : w ∈ S := Nh_le_S cfg.hwD
    have hSN : S ≤ normalizer (Y : Set G) := hY.S_le_normalizer
    have hwY : w * x * w⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hSN hwS) x).1 hx.1
    refine Subgroup.mem_inf.2 ⟨hwY, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hxd : x * (t * w) = (t * w) * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    have hwd' : w⁻¹ * (t * w) = (t * w) * w⁻¹ := Nh_comm cfg w⁻¹ (inv_mem cfg.hwD) _ hdD
    calc w * x * w⁻¹ * (t * w) = w * x * (w⁻¹ * (t * w)) := by group
      _ = w * x * ((t * w) * w⁻¹) := by rw [hwd']
      _ = w * (x * (t * w)) * w⁻¹ := by group
      _ = w * ((t * w) * x) * w⁻¹ := by rw [hxd]
      _ = (w * (t * w)) * x * w⁻¹ := by group
      _ = ((t * w) * w) * x * w⁻¹ := by rw [hwd]
      _ = (t * w) * (w * x * w⁻¹) := by group
  have hfix : ∀ x ∈ Y ⊓ centralizer ({t * w} : Set G), w * x = x * w → x = 1 ∨ x = z := by
    intro x hx hwx
    have hxC : x ∈ Y ⊓ centralizer ({w} : Set G) :=
      Subgroup.mem_inf.2 ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.2 hwx.symm⟩
    rw [hCw] at hxC
    exact cent_U_d hII hs cfg x hxC (Subgroup.mem_centralizer_singleton_iff.1 hx.2)
  obtain ⟨q, hqQ, hq4⟩ := Basic.exists_pow_four_eq hQ8 hzQ hs.z_sq hs.z_ne huniq hexp hwN cfg.hw2 hfix
  refine ⟨?_, q * w, mul_mem (hY.Y_le_S hqQ.1) (Nh_le_S cfg.hwD), ?_, hq4⟩
  · have h4 := four_mul_card_cent_le hII hs cfg (c := t * w) (fun a ha => Nh_comm cfg a ha _ hdD)
    omega
  · have hqd : q * (t * w) = (t * w) * q := Subgroup.mem_centralizer_singleton_iff.1 hqQ.2
    calc q * w * (t * w) = q * (w * (t * w)) := by group
      _ = q * ((t * w) * w) := by rw [hwd]
      _ = (q * (t * w)) * w := by group
      _ = ((t * w) * q) * w := by rw [hqd]
      _ = (t * w) * (q * w) := by group

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8

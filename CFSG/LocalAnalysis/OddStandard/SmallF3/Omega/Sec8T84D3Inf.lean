module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D3Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D3Comm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E X1 X2 E1 E2 : Subgroup G}

theorem sec8t84d3_Y_inf_E (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2) :
    Sec8T84Y X1 ⊓ E ≤ E1 := by
  let O : Subgroup G := oddCoreIn (normalizer (E : Set G))
  obtain ⟨g, hgX2, hg5, hgC⟩ := hd.ex5_2
  have hconjO : ∀ x ∈ X1, ∀ o ∈ O, x * o * x⁻¹ ∈ O := fun x hx o ho =>
    conj_mem_oddCoreIn (Subgroup.le_normalizer (h.hX.le1 hx)) ho
  let S : Subgroup G :=
    { carrier := {x | x ∈ X1 ∧ ∃ e ∈ E1, ∃ o ∈ O, x * g * x⁻¹ * g⁻¹ = e * o}
      one_mem' := ⟨X1.one_mem, 1, E1.one_mem, 1, O.one_mem, by group⟩
      mul_mem' := by
        rintro x y ⟨hx1, ex, hex, ox, hox, hxeq⟩ ⟨hy1, ey, hey, oy, hoy, hyeq⟩
        have hOy : x * oy * x⁻¹ ∈ O := hconjO x hx1 oy hoy
        refine ⟨X1.mul_mem hx1 hy1, (x * ey * x⁻¹) * ex,
          E1.mul_mem (hd.inv1 x hx1 ey hey) hex,
          (x * oy * x⁻¹) * ox, O.mul_mem hOy hox, ?_⟩
        have hxy : (x * y) * g * (x * y)⁻¹ * g⁻¹
            = (x * (y * g * y⁻¹ * g⁻¹) * x⁻¹) * (x * g * x⁻¹ * g⁻¹) := by group
        rw [hxy, hyeq, hxeq]
        have hcomm : (x * oy * x⁻¹) * ex = ex * (x * oy * x⁻¹) :=
          (sec8t84d3_O_comm h hOy (hd.le1 hex)).symm
        calc (x * (ey * oy) * x⁻¹) * (ex * ox)
            = (x * ey * x⁻¹) * (x * oy * x⁻¹) * (ex * ox) := by group
          _ = (x * ey * x⁻¹) * ((x * oy * x⁻¹) * ex) * ox := by group
          _ = (x * ey * x⁻¹) * (ex * (x * oy * x⁻¹)) * ox := by rw [hcomm]
          _ = ((x * ey * x⁻¹) * ex) * ((x * oy * x⁻¹) * ox) := by group
      inv_mem' := by
        rintro x ⟨hx1, ex, hex, ox, hox, hxeq⟩
        have hOx : x⁻¹ * ox⁻¹ * x ∈ O := by
          simpa using hconjO x⁻¹ (X1.inv_mem hx1) ox⁻¹ (O.inv_mem hox)
        have hEx : x⁻¹ * ex⁻¹ * x ∈ E1 := by
          simpa using hd.inv1 x⁻¹ (X1.inv_mem hx1) ex⁻¹ (E1.inv_mem hex)
        refine ⟨X1.inv_mem hx1, x⁻¹ * ex⁻¹ * x, hEx, x⁻¹ * ox⁻¹ * x, hOx, ?_⟩
        have hxinv : x⁻¹ * g * (x⁻¹)⁻¹ * g⁻¹
            = x⁻¹ * (x * g * x⁻¹ * g⁻¹)⁻¹ * x := by group
        rw [hxinv, hxeq]
        calc x⁻¹ * (ex * ox)⁻¹ * x
            = (x⁻¹ * ox⁻¹ * x) * (x⁻¹ * ex⁻¹ * x) := by rw [mul_inv_rev]; group
          _ = (x⁻¹ * ex⁻¹ * x) * (x⁻¹ * ox⁻¹ * x) :=
                (sec8t84d3_O_comm h hOx (hd.le1 hEx)).symm }
  have hY_le_S : Sec8T84Y X1 ≤ S := by
    change Subgroup.closure {x | x ∈ X1 ∧ Odd (orderOf x)} ≤ S
    rw [Subgroup.closure_le]
    intro x hx
    exact ⟨hx.1, sec8t84d3_comm_E1 h hd hx.1 hx.2 hgX2⟩
  intro y hy
  obtain ⟨hyY, hyE⟩ := hy
  obtain ⟨_, e, he1, o, ho, heo⟩ := hY_le_S hyY
  obtain ⟨e1, he1', e2, he2, hy12⟩ := sec8t84d3_E_decomp h hd hyE
  set f : G := g * e2 * g⁻¹ with hf_def
  have hf2 : f ∈ E2 := hd.inv2 g hgX2 e2 he2
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((h.elem.1.1.is_comm).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hgy : g * y * g⁻¹ = e1 * f := by
    rw [hy12, hf_def]
    calc g * (e1 * e2) * g⁻¹ = (g * e1 * g⁻¹) * (g * e2 * g⁻¹) := by group
      _ = e1 * (g * e2 * g⁻¹) := by rw [hd.triv2 g hgX2 e1 he1']
  have hyg : y * g * y⁻¹ * g⁻¹ = e2 * f⁻¹ := by
    calc y * g * y⁻¹ * g⁻¹ = y * (g * y * g⁻¹)⁻¹ := by group
      _ = (e1 * e2) * (e1 * f)⁻¹ := by rw [hgy, hy12]
      _ = e2 * f⁻¹ := by
            have h1 : (e1 * e2) * (e1 * f)⁻¹ = e1 * (e2 * f⁻¹) * e1⁻¹ := by
              rw [mul_inv_rev]; group
            rw [h1, hEcomm e1 (hd.le1 he1') (e2 * f⁻¹)
              (E.mul_mem (hd.le2 he2) (E.inv_mem (hd.le2 hf2)))]
            group
  have hsum : e2 * f⁻¹ = e * o := by rw [← hyg, heo]
  have hoE : o ∈ E := by
    have ho_eq : o = e⁻¹ * (e2 * f⁻¹) := by
      calc o = e⁻¹ * (e * o) := by group
        _ = e⁻¹ * (e2 * f⁻¹) := by rw [← hsum]
    rw [ho_eq]
    exact E.mul_mem (E.inv_mem (hd.le1 he1)) (E.mul_mem (hd.le2 he2) (E.inv_mem (hd.le2 hf2)))
  have ho1 : o = 1 := by
    have hbot : o ∈ (⊥ : Subgroup G) := by
      rw [← sec8t84d3_E_inf_O h]
      exact ⟨hoE, ho⟩
    exact Subgroup.mem_bot.mp hbot
  have he2f : e2 * f⁻¹ = e := by rw [hsum, ho1, mul_one]
  have he2f1 : e2 * f⁻¹ = 1 := by
    have hbot : e2 * f⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hd.inf]
      exact ⟨by rw [he2f]; exact he1, E2.mul_mem he2 (E2.inv_mem hf2)⟩
    exact Subgroup.mem_bot.mp hbot
  have hfe2 : e2 = f := eq_of_mul_inv_eq_one he2f1
  have hfix : g * e2 * g⁻¹ = e2 := by rw [← hf_def]; exact hfe2.symm
  have he2one : e2 = 1 := hd.fpf2 g hgX2 hg5 hgC e2 he2 hfix
  rw [hy12, he2one, mul_one]
  exact he1'

end CFSG.OddStandard.SmallF3.Omega

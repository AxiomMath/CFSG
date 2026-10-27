module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AFusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AInvPT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AFour
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AOuter

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem lemma4_2_of_simple (hG : IsSimpleGroup G) (h4 : 4 ∣ Nat.card G)
    (h : Ctx t L S x₁ x₂ lam rho tau) : 2 ∣ S.index := by
  by_contra hS
  have key : ∀ (p g₁ u e g : G), p ∈ twoCore t → u = p * tau → u * u = 1 →
      g₁ * u * g₁⁻¹ = t → e ∈ L → e * e = 1 → e ≠ 1 → u * e = e * u →
      g * u * g⁻¹ = t → g * e * g⁻¹ ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam → False := by
    intro p g₁ u e g hp hu hu2 hg₁ heL he2 hene hue hgu hge
    have h0 : Ctx0 t L S x₁ x₂ lam rho := h.toCtx0
    obtain ⟨c, hcL, hce⟩ := h.invol_L e heL he2 hene
    set f : G := g * e * g⁻¹ with hf
    have hfK : f ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam := by rw [hf]; exact hge
    have hf2 : f * f = 1 := by
      rw [hf]
      calc (g * e * g⁻¹) * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
        _ = 1 := by rw [he2]; group
    have hgc : (g * c) * (x₁ * x₂) ^ 2 * (g * c)⁻¹ = f := by
      rw [hf]
      calc (g * c) * (x₁ * x₂) ^ 2 * (g * c)⁻¹ =
            g * (c * (x₁ * x₂) ^ 2 * c⁻¹) * g⁻¹ := by group
        _ = g * e * g⁻¹ := by rw [hce]
    obtain ⟨c', hc'L, hc'z⟩ := exists_conj_of_involution_conj_z h0
      (not_conj_t_z h hS) (not_conj_z_tz h hS) hfK hf2 hgc
    have hu_mem : u ∈ invCent t := by
      rw [hu]
      exact Subgroup.mul_mem (invCent t) (twoCore_le_invCent t hp) (h.le_invCent h.tau_mem)
    have hu_notK : u ∉ twoCore t ⊔ L := by
      intro huK
      have hpK : p ∈ twoCore t ⊔ L := Subgroup.mem_sup_left hp
      have hpinv : p⁻¹ ∈ twoCore t ⊔ L := Subgroup.inv_mem _ hpK
      have htauK : tau ∈ twoCore t ⊔ L := by
        have hm := Subgroup.mul_mem _ hpinv huK
        rw [hu, show p⁻¹ * (p * tau) = tau by group] at hm
        exact hm
      exact h.tau_not_mem htauK
    have hwe_mem : u * e ∈ invCent t :=
      Subgroup.mul_mem (invCent t) hu_mem (L_le_invCent h.hyp heL)
    have hwe2 : (u * e) * (u * e) = 1 := by
      calc (u * e) * (u * e) = u * (e * u) * e := by group
        _ = u * (u * e) * e := by rw [hue]
        _ = (u * u) * (e * e) := by group
        _ = 1 := by rw [hu2, he2, one_mul]
    have hweu : (u * e) * u⁻¹ ∈ L := by
      have heq : (u * e) * u⁻¹ = e := by rw [hue, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]; exact heL
    obtain ⟨l, hlL, hle⟩ := outer_coset_conj h.hyp hu_mem hu2 hu_notK hwe_mem hwe2 hweu
    have ht_c' : t * c' = c' * t := (mem_invCent_iff.mp (L_le_invCent h.hyp hc'L)).symm
    have hway1 : g * (u * e) * g⁻¹ = c' * (t * (x₁ * x₂) ^ 2) * c'⁻¹ := by
      have hge' : g * e * g⁻¹ = c' * (x₁ * x₂) ^ 2 * c'⁻¹ := hf.symm.trans hc'z.symm
      calc g * (u * e) * g⁻¹ = (g * u * g⁻¹) * (g * e * g⁻¹) := by group
        _ = t * (c' * (x₁ * x₂) ^ 2 * c'⁻¹) := by rw [hgu, hge']
        _ = c' * (t * (x₁ * x₂) ^ 2) * c'⁻¹ := by
              calc t * (c' * (x₁ * x₂) ^ 2 * c'⁻¹) =
                    (t * c') * (x₁ * x₂) ^ 2 * c'⁻¹ := by group
                _ = (c' * t) * (x₁ * x₂) ^ 2 * c'⁻¹ := by rw [ht_c']
                _ = c' * (t * (x₁ * x₂) ^ 2) * c'⁻¹ := by group
    have hway2 : g * (u * e) * g⁻¹ = (g * l * g₁⁻¹) * t * (g * l * g₁⁻¹)⁻¹ := by
      rw [hle, ← hg₁]
      group
    have hEq : c' * (t * (x₁ * x₂) ^ 2) * c'⁻¹ =
        (g * l * g₁⁻¹) * t * (g * l * g₁⁻¹)⁻¹ := hway1.symm.trans hway2
    have hconj : (c'⁻¹ * (g * l * g₁⁻¹)) * t * (c'⁻¹ * (g * l * g₁⁻¹))⁻¹ =
        t * (x₁ * x₂) ^ 2 := by
      have h2 : (c'⁻¹ * (g * l * g₁⁻¹)) * t * (c'⁻¹ * (g * l * g₁⁻¹))⁻¹ =
          c'⁻¹ * ((g * l * g₁⁻¹) * t * (g * l * g₁⁻¹)⁻¹) * c' := by group
      rw [h2, ← hEq]
      group
    exact not_conj_t_tz h hS _ hconj
  obtain ⟨p, hp, g₁, hpτ, hg₁⟩ := exists_outer_involution_conj_t hG h4 h hS
  set u : G := p * tau with hu
  have hu2 : u * u = 1 := by rw [hu]; exact hpτ
  have hg₁' : g₁ * u * g₁⁻¹ = t := by rw [hu]; exact hg₁
  have hyL : x₁ ^ 2 ∈ L := (y_z_mem_L h.toCtx0).1
  have hzL : (x₁ * x₂) ^ 2 ∈ L := (y_z_mem_L h.toCtx0).2
  have hpy : p * x₁ ^ 2 = x₁ ^ 2 * p := twoCore_commute h.hyp p hp _ hyL
  have hpz : p * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * p := twoCore_commute h.hyp p hp _ hzL
  have hty : tau * x₁ ^ 2 = x₁ ^ 2 * tau := tau_commute_y h
  have htz : tau * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * tau := tau_commute_z h
  have hue_y : u * x₁ ^ 2 = x₁ ^ 2 * u := by
    rw [hu]
    calc (p * tau) * x₁ ^ 2 = p * (tau * x₁ ^ 2) := by group
      _ = p * (x₁ ^ 2 * tau) := by rw [hty]
      _ = (p * x₁ ^ 2) * tau := by group
      _ = (x₁ ^ 2 * p) * tau := by rw [hpy]
      _ = x₁ ^ 2 * (p * tau) := by group
  have hue_z : u * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * u := by
    rw [hu]
    calc (p * tau) * (x₁ * x₂) ^ 2 = p * (tau * (x₁ * x₂) ^ 2) := by group
      _ = p * ((x₁ * x₂) ^ 2 * tau) := by rw [htz]
      _ = (p * (x₁ * x₂) ^ 2) * tau := by group
      _ = ((x₁ * x₂) ^ 2 * p) * tau := by rw [hpz]
      _ = (x₁ * x₂) ^ 2 * (p * tau) := by group
  have hue_yz : u * (x₁ ^ 2 * (x₁ * x₂) ^ 2) = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * u := by
    calc u * (x₁ ^ 2 * (x₁ * x₂) ^ 2) = (u * x₁ ^ 2) * (x₁ * x₂) ^ 2 := by group
      _ = (x₁ ^ 2 * u) * (x₁ * x₂) ^ 2 := by rw [hue_y]
      _ = x₁ ^ 2 * (u * (x₁ * x₂) ^ 2) := by group
      _ = x₁ ^ 2 * ((x₁ * x₂) ^ 2 * u) := by rw [hue_z]
      _ = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * u := by group
  obtain ⟨g, hgu, hcase⟩ := exists_conj_four_mem_PT h hue_y hue_z hg₁'
  rcases hcase with hy | hz | hyz
  · exact key p g₁ u (x₁ ^ 2) g hp hu hu2 hg₁' hyL (y_mul_self_ne_one h.wreath).1
      (y_mul_self_ne_one h.wreath).2 hue_y hgu hy
  · exact key p g₁ u ((x₁ * x₂) ^ 2) g hp hu hu2 hg₁' hzL (z_mul_self_ne_one h.toCtx0).1
      (z_mul_self_ne_one h.toCtx0).2 hue_z hgu hz
  · exact key p g₁ u (x₁ ^ 2 * (x₁ * x₂) ^ 2) g hp hu hu2 hg₁'
      (Subgroup.mul_mem L hyL hzL) (yz_mul_self_ne_one h.wreath).1
      (yz_mul_self_ne_one h.wreath).2 hue_yz hgu hyz

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AOdd

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem normalizer_fixes_z (h : Ctx0 t L S x₁ x₂ lam rho) {n : G}
    (hn : n ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G)) :
    n * (x₁ * x₂) ^ 2 * n⁻¹ = (x₁ * x₂) ^ 2 := by
  let z : G := (x₁ * x₂) ^ 2
  have hzL : z ∈ L := (y_z_mem_L h).2
  have hzsq : z * z = 1 := (z_mul_self_ne_one h).1
  have hzne : z ≠ 1 := (z_mul_self_ne_one h).2
  have hg : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 := Subtype.ext (by simpa using hzsq)
  have hg1 : (⟨z, hzL⟩ : ↥L) ≠ 1 :=
    fun hh => hzne (by simpa using Subtype.ext_iff.mp hh)
  obtain ⟨a, b, haz, hbz, haodd, hbodd, hab⟩ :=
    exists_odd_pair_of_psu33 h.hyp.lieModel (g := (⟨z, hzL⟩ : ↥L)) hg hg1
  have ha_t : Commute (a : G) t := (mem_invCent_iff).1 (L_le_invCent h.hyp a.2)
  have hb_t : Commute (b : G) t := (mem_invCent_iff).1 (L_le_invCent h.hyp b.2)
  have hazG : Commute (a : G) z := by
    have h := congrArg Subtype.val haz
    show (a : G) * z = z * (a : G)
    simpa [z] using h
  have hbzG : Commute (b : G) z := by
    have h := congrArg Subtype.val hbz
    show (b : G) * z = z * (b : G)
    simpa [z] using h
  have habG : ((a : G) * (b : G)) ^ 2 = z := by
    have h := congrArg Subtype.val hab; simpa [z] using h
  let E : Subgroup G := closure {t, z}
  have hnE : ∀ e : G, e ∈ E ↔ n * e * n⁻¹ ∈ E :=
    (Subgroup.mem_set_normalizer_iff).1 hn
  have htE : t ∈ E := Subgroup.subset_closure (by simp)
  have hzE : z ∈ E := Subgroup.subset_closure (by simp)
  have hninv_t : n⁻¹ * t * n ∈ E :=
    (hnE (n⁻¹ * t * n)).2 (by rw [show n * (n⁻¹ * t * n) * n⁻¹ = t by group]; exact htE)
  have ha_comm_E : ∀ e ∈ E, Commute (a : G) e := by
    intro e he
    rcases mem_closure_t_z h he with rfl | rfl | rfl | rfl
    · exact Commute.one_right _
    · exact ha_t
    · exact hazG
    · exact ha_t.mul_right hazG
  have hb_comm_E : ∀ e ∈ E, Commute (b : G) e := by
    intro e he
    rcases mem_closure_t_z h he with rfl | rfl | rfl | rfl
    · exact Commute.one_right _
    · exact hb_t
    · exact hbzG
    · exact hb_t.mul_right hbzG
  have ha'_t : Commute (n * (a : G) * n⁻¹) t := by
    have hh := (ha_comm_E (n⁻¹ * t * n) hninv_t).conj n
    rw [show n * (n⁻¹ * t * n) * n⁻¹ = t by group] at hh
    exact hh
  have hb'_t : Commute (n * (b : G) * n⁻¹) t := by
    have hh := (hb_comm_E (n⁻¹ * t * n) hninv_t).conj n
    rw [show n * (n⁻¹ * t * n) * n⁻¹ = t by group] at hh
    exact hh
  have ha'_inv : n * (a : G) * n⁻¹ ∈ invCent t := (mem_invCent_iff).2 ha'_t.eq
  have hb'_inv : n * (b : G) * n⁻¹ ∈ invCent t := (mem_invCent_iff).2 hb'_t.eq
  have ha'_order : orderOf (n * (a : G) * n⁻¹) = orderOf (a : G) := by
    rw [← MulAut.conj_apply n (a : G)]
    exact MulEquiv.orderOf_eq (MulAut.conj n) (a : G)
  have hb'_order : orderOf (n * (b : G) * n⁻¹) = orderOf (b : G) := by
    rw [← MulAut.conj_apply n (b : G)]
    exact MulEquiv.orderOf_eq (MulAut.conj n) (b : G)
  have ha'_odd : ¬ 2 ∣ orderOf (n * (a : G) * n⁻¹) := by
    rw [ha'_order, Subgroup.orderOf_coe a]; exact haodd
  have hb'_odd : ¬ 2 ∣ orderOf (n * (b : G) * n⁻¹) := by
    rw [hb'_order, Subgroup.orderOf_coe b]; exact hbodd
  have ha'_L : n * (a : G) * n⁻¹ ∈ L := odd_mem_L h ha'_inv ha'_odd
  have hb'_L : n * (b : G) * n⁻¹ ∈ L := odd_mem_L h hb'_inv hb'_odd
  have hab' : ((n * (a : G) * n⁻¹) * (n * (b : G) * n⁻¹)) ^ 2 = n * z * n⁻¹ := by
    have hmul : (n * (a : G) * n⁻¹) * (n * (b : G) * n⁻¹) =
        n * ((a : G) * (b : G)) * n⁻¹ := by group
    rw [hmul, conj_pow, habG]
  have hconjz_L : n * z * n⁻¹ ∈ L := by
    rw [← hab']
    exact L.pow_mem (L.mul_mem ha'_L hb'_L) 2
  have hconjz_E : n * z * n⁻¹ ∈ E := (hnE z).1 hzE
  rcases eq_one_or_z_of_mem_closure_t_z_of_mem_L h hconjz_E hconjz_L with h1 | hz
  · exfalso
    exact hzne (by
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group)
  · exact hz

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

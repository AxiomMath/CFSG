module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a4b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private noncomputable def dI2a_sigma (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ↥(q13A t tau x₁ x₂ rho) →* ↥(q13A t tau x₁ x₂ rho) where
  toFun a := ⟨lam * (a : G) * lam⁻¹, (q13a_A_inv h a a.2).2.1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' := by
    intro a b
    apply Subtype.ext
    show lam * ((a : G) * (b : G)) * lam⁻¹ =
      (lam * (a : G) * lam⁻¹) * (lam * (b : G) * lam⁻¹)
    group

private noncomputable def dI2a_phi (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ↥(q13A t tau x₁ x₂ rho) →* ↥(q13A t tau x₁ x₂ rho) :=
  MonoidHom.mk' (fun a => a * dI2a_sigma h a) (by
    intro a b
    rw [map_mul]
    have hcommAB : (b : ↥(q13A t tau x₁ x₂ rho)) * dI2a_sigma h a =
        dI2a_sigma h a * b :=
      Subtype.ext (q13a_A_comm h (b : G) b.2 (dI2a_sigma h a : G) (dI2a_sigma h a).2)
    calc (a * b) * (dI2a_sigma h a * dI2a_sigma h b)
        = a * (b * dI2a_sigma h a) * dI2a_sigma h b := by group
      _ = a * (dI2a_sigma h a * b) * dI2a_sigma h b := by rw [hcommAB]
      _ = (a * dI2a_sigma h a) * (b * dI2a_sigma h b) := by group)

private lemma dI2a_phi_coe (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (a : ↥(q13A t tau x₁ x₂ rho)) :
    ((dI2a_phi h a : ↥(q13A t tau x₁ x₂ rho)) : G) = (a : G) * (lam * (a : G) * lam⁻¹) :=
  rfl

private lemma dI2a_phi_ker (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (dI2a_phi h).ker =
      (q13A t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)).subgroupOf
        (q13A t tau x₁ x₂ rho) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hphi
    have hval : (a : G) * (lam * (a : G) * lam⁻¹) = 1 := by
      rw [← dI2a_phi_coe h a]
      exact congrArg Subtype.val hphi
    have hx_eq : lam * (a : G) * lam⁻¹ = (a : G)⁻¹ :=
      eq_inv_of_mul_eq_one_right hval
    refine ⟨a.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : (t * lam) * (a : G) * (t * lam)⁻¹ = (a : G) := by
      calc (t * lam) * (a : G) * (t * lam)⁻¹
          = t * (lam * (a : G) * lam⁻¹) * t⁻¹ := by group
        _ = t * (a : G)⁻¹ * t⁻¹ := by rw [hx_eq]
        _ = (t * (a : G) * t⁻¹)⁻¹ := by group
        _ = ((a : G)⁻¹)⁻¹ := by rw [q13a_t_inv_A h (a : G) a.2]
        _ = (a : G) := inv_inv _
    have hcomm_goal : (t * lam) * (a : G) = (a : G) * (t * lam) := by
      calc (t * lam) * (a : G) = ((t * lam) * (a : G) * (t * lam)⁻¹) * (t * lam) := by group
        _ = (a : G) * (t * lam) := by rw [hconj]
    exact hcomm_goal.symm
  · rintro ⟨_, hcent⟩
    apply Subtype.ext
    show (a : G) * (lam * (a : G) * lam⁻¹) = 1
    have hcomm : (t * lam) * (a : G) = (a : G) * (t * lam) :=
      (Subgroup.mem_centralizer_singleton_iff.mp hcent).symm
    have hconj : (t * lam) * (a : G) * (t * lam)⁻¹ = (a : G) := by
      rw [hcomm]; group
    have hx : lam * (a : G) * lam⁻¹ = (a : G)⁻¹ := by
      have h2 : (t * lam) * (a : G) * (t * lam)⁻¹ = (lam * (a : G) * lam⁻¹)⁻¹ := by
        calc (t * lam) * (a : G) * (t * lam)⁻¹
            = t * (lam * (a : G) * lam⁻¹) * t⁻¹ := by group
          _ = (lam * (a : G) * lam⁻¹)⁻¹ :=
            q13a_t_inv_A h (lam * (a : G) * lam⁻¹) (q13a_A_inv h (a : G) a.2).2.1
      rw [h2] at hconj
      have := congrArg Inv.inv hconj
      simpa using this
    rw [hx, mul_inv_cancel]

private lemma dI2a_phi_range_le (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (dI2a_phi h).range ≤
      (q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)).subgroupOf
        (q13A t tau x₁ x₂ rho) := by
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · exact Subgroup.mul_mem _ a.2 (q13a_A_inv h (a : G) a.2).2.1
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hl : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (q13a_lam_mul_self h)
    have hfix : lam * ((a : G) * (lam * (a : G) * lam⁻¹)) * lam⁻¹ =
        (a : G) * (lam * (a : G) * lam⁻¹) := by
      calc lam * ((a : G) * (lam * (a : G) * lam⁻¹)) * lam⁻¹
          = (lam * (a : G) * lam⁻¹) * (lam * (lam * (a : G) * lam⁻¹) * lam⁻¹) := by group
        _ = (lam * (a : G) * lam⁻¹) * (a : G) := by
              congr 1
              calc lam * (lam * (a : G) * lam⁻¹) * lam⁻¹
                  = (lam * lam) * (a : G) * (lam⁻¹ * lam⁻¹) := by group
                _ = 1 * (a : G) * 1 := by
                      rw [q13a_lam_mul_self h, hl, q13a_lam_mul_self h]
                _ = (a : G) := by group
        _ = (a : G) * (lam * (a : G) * lam⁻¹) :=
              q13a_A_comm h (lam * (a : G) * lam⁻¹) (q13a_A_inv h (a : G) a.2).2.1
                (a : G) a.2
    have hcomm_goal : ((a : G) * (lam * (a : G) * lam⁻¹)) * lam =
        lam * ((a : G) * (lam * (a : G) * lam⁻¹)) := by
      calc ((a : G) * (lam * (a : G) * lam⁻¹)) * lam
          = (lam * ((a : G) * (lam * (a : G) * lam⁻¹)) * lam⁻¹) * lam := by rw [hfix]
        _ = lam * ((a : G) * (lam * (a : G) * lam⁻¹)) := by group
    simpa [dI2a_phi_coe h a] using hcomm_goal

theorem q13d_card_CA_lam_ge (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    4 ≤ Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) := by
  let A := q13A t tau x₁ x₂ rho
  let C := A ⊓ centralizer ({lam} : Set G)
  let K := A ⊓ centralizer ({t * lam} : Set G)
  change 4 ≤ Nat.card ↥C
  have hker_eq : (dI2a_phi h).ker = K.subgroupOf A := dI2a_phi_ker h
  have hker : Nat.card (dI2a_phi h).ker = 4 := by
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ≤ A)).toEquiv]
    simpa [A, K] using q13a_card_CA_tlam h
  have hcardA : Nat.card ↥A = 16 := by
    rw [q13a_card_A h]; norm_num
  have hrange : Nat.card (dI2a_phi h).range = 4 := by
    have hcard := card_ker_mul_card_range (dI2a_phi h)
    rw [hker, hcardA] at hcard
    omega
  have hle : (dI2a_phi h).range ≤ C.subgroupOf A := dI2a_phi_range_le h
  calc 4 = Nat.card (dI2a_phi h).range := hrange.symm
    _ ≤ Nat.card ↥(C.subgroupOf A) := Subgroup.card_le_of_le hle
    _ = Nat.card ↥C :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ A)).toEquiv

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13d_rho_comm_gam (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Commute rho (t * om) := by
  have ht : t * rho = rho * t := (q13a_t_comm h).2.1
  have hom : om * rho = rho * om := (q13a_om_comm h).2.1
  calc rho * (t * om) = (rho * t) * om := by group
    _ = (t * rho) * om := by rw [ht]
    _ = t * (rho * om) := by group
    _ = t * (om * rho) := by rw [hom]
    _ = (t * om) * rho := by group

private theorem q13d_rho_norm_A (h : Q13Om t L S x₁ x₂ lam rho tau om) {a : G}
    (ha : a ∈ q13A t tau x₁ x₂ rho) :
    rho * a * rho⁻¹ ∈ q13A t tau x₁ x₂ rho :=
  (q13a_A_inv h a ha).1

private theorem q13d_rho_zpow_norm_A (h : Q13Om t L S x₁ x₂ lam rho tau om) (m : ℤ)
    {a : G} (ha : a ∈ q13A t tau x₁ x₂ rho) :
    rho ^ m * a * (rho ^ m)⁻¹ ∈ q13A t tau x₁ x₂ rho := by
  have hrho : rho ∈ Subgroup.normalizer
      ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => q13d_rho_norm_A h ha)
  have hle : zpowers rho ≤ Subgroup.normalizer
      ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hrho
  have hmem : rho ^ m ∈ Subgroup.normalizer
      ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    hle (Subgroup.zpow_mem_zpowers rho m)
  exact (Subgroup.mem_normalizer_iff.mp hmem a).mp ha

private noncomputable def q13d_phi (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ↥(q13A t tau x₁ x₂ rho) → ↥(q13A t tau x₁ x₂ rho) :=
  fun a => ⟨⁅(a : G), rho⁆, by
    have hmem := (q13A t tau x₁ x₂ rho).mul_mem a.2
      (q13d_rho_norm_A h ((q13A t tau x₁ x₂ rho).inv_mem a.2))
    simpa [commutatorElement_def, mul_assoc] using hmem⟩

private theorem q13d_phi_injective (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Function.Injective (q13d_phi h) := by
  intro a b hab
  have hval : ⁅(a : G), rho⁆ = ⁅(b : G), rho⁆ := congrArg Subtype.val hab
  have hval' : (a : G) * rho * (a : G)⁻¹ * rho⁻¹
      = (b : G) * rho * (b : G)⁻¹ * rho⁻¹ := by
    simpa only [commutatorElement_def] using hval
  have h1 : (a : G) * rho * (a : G)⁻¹ = (b : G) * rho * (b : G)⁻¹ := by
    calc (a : G) * rho * (a : G)⁻¹
        = (a : G) * rho * (a : G)⁻¹ * rho⁻¹ * rho := by group
      _ = (b : G) * rho * (b : G)⁻¹ * rho⁻¹ * rho := by rw [hval']
      _ = (b : G) * rho * (b : G)⁻¹ := by group
  have hconj : ((b : G)⁻¹ * (a : G)) * rho * ((b : G)⁻¹ * (a : G))⁻¹ = rho := by
    calc ((b : G)⁻¹ * (a : G)) * rho * ((b : G)⁻¹ * (a : G))⁻¹
        = (b : G)⁻¹ * ((a : G) * rho * (a : G)⁻¹) * (b : G) := by group
      _ = (b : G)⁻¹ * ((b : G) * rho * (b : G)⁻¹) * (b : G) := by rw [h1]
      _ = rho := by group
  have hcomm : ((b : G)⁻¹ * (a : G)) * rho = rho * ((b : G)⁻¹ * (a : G)) := by
    calc ((b : G)⁻¹ * (a : G)) * rho
        = ((b : G)⁻¹ * (a : G)) * rho * ((b : G)⁻¹ * (a : G))⁻¹ *
            ((b : G)⁻¹ * (a : G)) := by group
      _ = rho * ((b : G)⁻¹ * (a : G)) := by rw [hconj]
  have hmem : (b : G)⁻¹ * (a : G) ∈ q13A t tau x₁ x₂ rho :=
    (q13A t tau x₁ x₂ rho).mul_mem ((q13A t tau x₁ x₂ rho).inv_mem b.2) a.2
  have hc : (b : G)⁻¹ * (a : G) = 1 :=
    l12_cent_Q_rho h.c11 _ (Subgroup.mem_inf.mp hmem).1 hcomm
  exact Subtype.ext (inv_mul_eq_one.mp hc).symm

theorem q13d_CP_rho (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    q13P t tau x₁ x₂ rho om ⊓ centralizer ({rho} : Set G) = zpowers (t * om) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨hpP, hpc⟩ := Subgroup.mem_inf.mp hp
    obtain ⟨a, ha, k, rfl⟩ := (q13d_mem_P h hII).mp hpP
    have hcent : (a * (t * om) ^ k) * rho = rho * (a * (t * om) ^ k) :=
      Subgroup.mem_centralizer_singleton_iff.mp hpc
    have hgam : rho * (t * om) ^ k = (t * om) ^ k * rho :=
      (q13d_rho_comm_gam h).zpow_right k
    have hcomm : rho * a = a * rho := by
      have h2 : rho * a * (t * om) ^ k = a * rho * (t * om) ^ k := by
        calc rho * a * (t * om) ^ k
            = rho * (a * (t * om) ^ k) := by group
          _ = (a * (t * om) ^ k) * rho := hcent.symm
          _ = a * ((t * om) ^ k * rho) := by group
          _ = a * (rho * (t * om) ^ k) := by rw [hgam.symm]
          _ = a * rho * (t * om) ^ k := by group
      exact mul_right_cancel h2
    have ha1 : a = 1 :=
      l12_cent_Q_rho h.c11 a (Subgroup.mem_inf.mp ha).1 hcomm.symm
    rw [ha1, one_mul]
    exact Subgroup.zpow_mem_zpowers (t * om) k
  · intro p hp
    apply Subgroup.mem_inf.mpr
    refine ⟨Subgroup.zpowers_le.mpr (q13d_gam_mem_P h) hp, ?_⟩
    exact Subgroup.zpowers_le.mpr (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (q13d_rho_comm_gam h).symm) hp

theorem q13d_comm_P_rho (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ⁅q13P t tau x₁ x₂ rho om, zpowers rho⁆ = q13A t tau x₁ x₂ rho := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro p hp g hg
    obtain ⟨a, ha, k, rfl⟩ := (q13d_mem_P h hII).mp hp
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcr : ((t * om) ^ k) * rho ^ m = rho ^ m * (t * om) ^ k :=
      ((q13d_rho_comm_gam h).symm.zpow_left k).zpow_right m
    have hgoal : (a * (t * om) ^ k) * rho ^ m * (a * (t * om) ^ k)⁻¹ * (rho ^ m)⁻¹
        = a * (rho ^ m * a⁻¹ * (rho ^ m)⁻¹) := by
      calc (a * (t * om) ^ k) * rho ^ m * (a * (t * om) ^ k)⁻¹ * (rho ^ m)⁻¹
          = a * ((t * om) ^ k * rho ^ m * ((t * om) ^ k)⁻¹) * a⁻¹ * (rho ^ m)⁻¹ := by
            group
        _ = a * rho ^ m * a⁻¹ * (rho ^ m)⁻¹ := by rw [hcr]; group
        _ = a * (rho ^ m * a⁻¹ * (rho ^ m)⁻¹) := by group
    rw [commutatorElement_def, hgoal]
    exact (q13A t tau x₁ x₂ rho).mul_mem ha
      (q13d_rho_zpow_norm_A h m ((q13A t tau x₁ x₂ rho).inv_mem ha))
  · intro b hb
    have hinj := q13d_phi_injective h
    have hsurj : Function.Surjective (q13d_phi h) :=
      Finite.injective_iff_surjective.mp hinj
    obtain ⟨a, ha⟩ := hsurj ⟨b, hb⟩
    have hval : (q13d_phi h a : G) = b := congrArg Subtype.val ha
    rw [← hval]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left a.2)
      (Subgroup.mem_zpowers rho)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4Defs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4_V_comm (hc : Ctx0 t L S x₁ x₂ lam rho) {u v : G} (hu : u ∈ fourGrp x₁ x₂)
    (hv : v ∈ fourGrp x₁ x₂) : u * v = v * u := by
  have hVA : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
    rw [(hc.wreath.fourGrp_eq_omega).1]
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr (fun a ha => ha.1)
  haveI : IsMulCommutative (baseGrp x₁ x₂) := hc.wreath.baseGrp_eq.1
  exact congrArg Subtype.val (mul_comm' (⟨u, hVA hu⟩ : baseGrp x₁ x₂) ⟨v, hVA hv⟩)

theorem w4_rho_t (hc : Ctx4 t L S x₁ x₂ lam rho tau) : rho * t = t * rho :=
  S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hc.rho_mem)

theorem w4_rho_tau (hc : Ctx4 t L S x₁ x₂ lam rho tau) : rho * tau = tau * rho :=
  hc.tau_rho.symm

theorem w4_conj_t_mem (hc : W4Ctx0 t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) : g * t * g⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) := by
  rw [← hc.tM]
  exact ⟨g, hg, rfl⟩

private lemma w4_mul_inv_eq {t u v : G} (h : v = t * u) : v * u⁻¹ = t := by
  rw [h]; group

theorem w4_conj_tau_cases (hc : W4Ctxa t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) :
    g * tau * g⁻¹ ∈ tau • (fourGrp x₁ x₂ : Set G) ∨
      g * tau * g⁻¹ ∈ (t * tau) • (fourGrp x₁ x₂ : Set G) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have ht2 : t * t = 1 := S4A.t_mul_self hc4.hyp
  have htau2 : tau * tau = 1 := by simpa [pow_two] using hc4.l44.1
  have htauX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have hX : g * tau * g⁻¹ ∈ ctxX t tau x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hg tau).mp htauX
  have hVg : ∀ v ∈ fourGrp x₁ x₂, g⁻¹ * v * g ∈ fourGrp x₁ x₂ := fun v hv => by
    simpa using hc.normal_V.2 g⁻¹ (inv_mem hg) v hv
  have hVN : fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ := (p0_V_le_N_le_X t tau x₁ x₂).1
  rcases l12_X_cases hc4 hX with hN | hN
  · rcases l12_N_cases hc4 hN with hV | hV
    · exfalso
      have h1 := hVg _ hV
      rw [show g⁻¹ * (g * tau * g⁻¹) * g = tau by group] at h1
      exact l12_tau_not_mem_V hc4 h1
    · left
      refine Set.mem_smul_set.mpr ⟨tau * (g * tau * g⁻¹), hV, ?_⟩
      show tau * (tau * (g * tau * g⁻¹)) = g * tau * g⁻¹
      rw [← mul_assoc, htau2, one_mul]
  · rcases l12_N_cases hc4 hN with hV | hV
    · exfalso
      obtain ⟨w₁, hw₁, hw₁e⟩ := Set.mem_smul_set.mp (w4_conj_t_mem hc.toW4Ctx0 (inv_mem hg))
      simp only [smul_eq_mul, inv_inv] at hw₁e
      have h1 := hVg _ hV
      have htt : t * (t * (g * tau * g⁻¹)) = g * tau * g⁻¹ := by
        rw [← mul_assoc, ht2, one_mul]
      have hτ : tau = t * (w₁ * (g⁻¹ * (t * (g * tau * g⁻¹)) * g)) := by
        calc tau = g⁻¹ * (g * tau * g⁻¹) * g := by group
          _ = g⁻¹ * (t * (t * (g * tau * g⁻¹))) * g := by rw [htt]
          _ = (g⁻¹ * t * g) * (g⁻¹ * (t * (g * tau * g⁻¹)) * g) := by group
          _ = (t * w₁) * (g⁻¹ * (t * (g * tau * g⁻¹)) * g) := by rw [hw₁e]
          _ = t * (w₁ * (g⁻¹ * (t * (g * tau * g⁻¹)) * g)) := by group
      have hmem : tau * (w₁ * (g⁻¹ * (t * (g * tau * g⁻¹)) * g))⁻¹ ∈ ctxN tau x₁ x₂ :=
        mul_mem (Subgroup.subset_closure (by simp)) (inv_mem (hVN (mul_mem hw₁ h1)))
      apply l12_t_not_mem_N hc4
      rw [← w4_mul_inv_eq hτ]
      exact hmem
    · right
      refine Set.mem_smul_set.mpr ⟨tau * (t * (g * tau * g⁻¹)), hV, ?_⟩
      show t * tau * (tau * (t * (g * tau * g⁻¹))) = g * tau * g⁻¹
      calc t * tau * (tau * (t * (g * tau * g⁻¹)))
          = t * (tau * tau) * t * (g * tau * g⁻¹) := by group
        _ = g * tau * g⁻¹ := by rw [htau2, mul_one, ht2, one_mul]

theorem w4_baseGrp_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : baseGrp x₁ x₂ ≤ L := by
  rw [baseGrp]
  refine (Subgroup.closure_le (K := L)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact (S4A.generators_mem_L h).1
  · exact (S4A.generators_mem_L h).2.1

theorem w4_fpf (h : Ctx0 t L S x₁ x₂ lam rho) {f : G} (hf : f ∈ fourGrp x₁ x₂)
    (hcomm : rho * f = f * rho) : f = 1 := by
  have hfB : f ∈ baseGrp x₁ x₂ := by
    have hfeq := hf
    rw [(WreathRel.fourGrp_eq_omega h.wreath).1] at hfeq
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr (fun a ha => ha.1) hfeq
  have hfL : f ∈ L := w4_baseGrp_le_L h hfB
  have hfW : f ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right hfB
  have hfC : f ∈ Subgroup.centralizer ({rho} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hfP : f ∈ twoCore t := by
    have hmem : f ∈ ctxW t x₁ x₂ ⊓ Subgroup.centralizer ({rho} : Set G) := ⟨hfW, hfC⟩
    rwa [h.cent_rho] at hmem
  have hmem : f ∈ twoCore t ⊓ L := ⟨hfP, hfL⟩
  rwa [h.hyp.twoCore_inf, Subgroup.mem_bot] at hmem

theorem w4_rho_norm (hc : W4Ctxa t L S x₁ x₂ lam rho tau) {a : G} (ha : a ∈ fourGrp x₁ x₂) :
    a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho) = 1 := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hc0 : Ctx0 t L S x₁ x₂ lam rho := hc4.toCtx0
  have hρM : rho ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc4).2.2.2.2.1
  have hρ3 : rho ^ 3 = 1 := by rw [← hc4.ord_rho]; exact pow_orderOf_eq_one rho
  have hρ2 : rho * rho = rho⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc rho * rho * rho = rho ^ 3 := (pow_three' rho).symm
      _ = 1 := hρ3
  have h1 : rho * a * rho⁻¹ ∈ fourGrp x₁ x₂ := hc.normal_V.2 rho hρM a ha
  have h2 : rho⁻¹ * a * rho ∈ fourGrp x₁ x₂ := by
    simpa using hc.normal_V.2 rho⁻¹ (inv_mem hρM) a ha
  have hconj : rho * (a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho)) * rho⁻¹ =
      a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho) := by
    have e2 : rho * (rho * a * rho⁻¹) * rho⁻¹ = rho⁻¹ * a * rho := by
      calc rho * (rho * a * rho⁻¹) * rho⁻¹ = (rho * rho) * a * (rho * rho)⁻¹ := by group
        _ = rho⁻¹ * a * rho := by rw [hρ2]; group
    calc rho * (a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho)) * rho⁻¹
        = (rho * a * rho⁻¹) * (rho * (rho * a * rho⁻¹) * rho⁻¹) *
            (rho * (rho⁻¹ * a * rho) * rho⁻¹) := by group
      _ = (rho * a * rho⁻¹) * (rho⁻¹ * a * rho) * a := by rw [e2]; group
      _ = a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho) := by
        have hca : (rho⁻¹ * a * rho) * a = a * (rho⁻¹ * a * rho) := w4_V_comm hc0 h2 ha
        have hba : (rho * a * rho⁻¹) * a = a * (rho * a * rho⁻¹) := w4_V_comm hc0 h1 ha
        calc (rho * a * rho⁻¹) * (rho⁻¹ * a * rho) * a
            = (rho * a * rho⁻¹) * ((rho⁻¹ * a * rho) * a) := by group
          _ = (rho * a * rho⁻¹) * (a * (rho⁻¹ * a * rho)) := by rw [hca]
          _ = ((rho * a * rho⁻¹) * a) * (rho⁻¹ * a * rho) := by group
          _ = (a * (rho * a * rho⁻¹)) * (rho⁻¹ * a * rho) := by rw [hba]
  refine w4_fpf hc0 (mul_mem (mul_mem ha h1) h2) ?_
  calc rho * (a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho)) =
      (rho * (a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho)) * rho⁻¹) * rho := by group
    _ = (a * (rho * a * rho⁻¹) * (rho⁻¹ * a * rho)) * rho := by rw [hconj]

theorem w4_O_cent_V (hc : W4Ctxb t L S x₁ x₂ lam rho tau) {g : G} (hg : g ∈ ctxO t tau x₁ x₂)
    {v : G} (hv : v ∈ fourGrp x₁ x₂) : g * v * g⁻¹ = v := by
  have h : g ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [← hc.O_eq_C]; exact hg
  have hv' : v * g = g * v := Subgroup.mem_centralizer_iff.mp h.2 v hv
  calc g * v * g⁻¹ = (g * v) * g⁻¹ := rfl
    _ = (v * g) * g⁻¹ := by rw [← hv']
    _ = v := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

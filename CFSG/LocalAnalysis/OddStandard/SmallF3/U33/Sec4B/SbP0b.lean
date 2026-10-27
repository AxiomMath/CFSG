module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTOrb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem p0b_baseGrp_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : baseGrp x₁ x₂ ≤ L := by
  rw [baseGrp]
  refine (Subgroup.closure_le (K := L)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact (S4A.generators_mem_L h).1
  · exact (S4A.generators_mem_L h).2.1

private theorem p0b_baseGrp_commute (h : Ctx0 t L S x₁ x₂ lam rho) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) : a * b = b * a := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := h.wreath.baseGrp_eq.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : baseGrp x₁ x₂) ⟨b, hb⟩)

private theorem p0b_baseGrp_conj_eq_of_mem (h : Ctx0 t L S x₁ x₂ lam rho) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) : a * b * a⁻¹ = b := by
  rw [p0b_baseGrp_commute h ha hb, mul_assoc, mul_inv_cancel, mul_one]

private theorem p0b_rho_conj_mem_fourGrp (h : Ctx0 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) : rho * f * rho⁻¹ ∈ fourGrp x₁ x₂ := by
  have hρnormB : rho ∈ Subgroup.normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    have hmem : rho ∈ Subgroup.normalizer (⁅ctxW t x₁ x₂, zpowers rho⁆ : Subgroup G) :=
      Subgroup.normalizer_commutator_ge_right (H₁ := ctxW t x₁ x₂) (H₂ := zpowers rho)
        (Subgroup.mem_zpowers rho)
    rwa [h.comm_rho] at hmem
  have hfB : f ∈ baseGrp x₁ x₂ := by
    have hfeq := hf
    rw [(h.wreath.fourGrp_eq_omega).1] at hfeq
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr (fun a ha => ha.1) hfeq
  have hf2 : f ^ 2 = 1 := (h.wreath.fourGrp_eq_omega).2.1.2 f hf
  have hconjB : rho * f * rho⁻¹ ∈ baseGrp x₁ x₂ :=
    (Subgroup.mem_normalizer_iff.mp hρnormB f).mp hfB
  have hconj2 : (rho * f * rho⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hf2, mul_one, mul_inv_cancel]
  rw [(h.wreath.fourGrp_eq_omega).1]
  exact Subgroup.subset_closure ⟨hconjB, hconj2⟩

private theorem p0b_rho_mem_normalizer_fourGrp (h : Ctx0 t L S x₁ x₂ lam rho) :
    rho ∈ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hle : (fourGrp x₁ x₂).map (MulAut.conj rho).toMonoidHom ≤ fourGrp x₁ x₂ := by
    rw [Subgroup.map_le_iff_le_comap]
    intro f hf
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      using p0b_rho_conj_mem_fourGrp h hf
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj rho).injective).ge)

private theorem p0b_eq_one_of_commute_rho_of_mem_fourGrp (h : Ctx0 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) (hc : rho * f = f * rho) : f = 1 := by
  have hfB : f ∈ baseGrp x₁ x₂ := by
    have hfeq := hf
    rw [(h.wreath.fourGrp_eq_omega).1] at hfeq
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr (fun a ha => ha.1) hfeq
  have hfL : f ∈ L := p0b_baseGrp_le_L h hfB
  have hfW : f ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right hfB
  have hfC : f ∈ Subgroup.centralizer ({rho} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc.symm
  have hfP : f ∈ twoCore t := by
    have hmem : f ∈ ctxW t x₁ x₂ ⊓ Subgroup.centralizer ({rho} : Set G) := ⟨hfW, hfC⟩
    rwa [h.cent_rho] at hmem
  have hmem : f ∈ twoCore t ⊓ L := ⟨hfP, hfL⟩
  rwa [h.hyp.twoCore_inf, Subgroup.mem_bot] at hmem

private theorem p0b_mem_fourGrp_cases_rho (h : Ctx0 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) :
    f = 1 ∨ f = (x₁ * x₂) ^ 2 ∨ f = rho * (x₁ * x₂) ^ 2 * rho⁻¹ ∨
      f = rho⁻¹ * (x₁ * x₂) ^ 2 * rho := by
  have hcomm : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 := S4A.y_commute_z h.wreath
  have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := (S4A.y_mul_self_ne_one h.wreath).1
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (S4A.z_mul_self_ne_one h).1
  have hzne1 : (x₁ * x₂) ^ 2 ≠ 1 := (S4A.z_mul_self_ne_one h).2
  have hzF : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzpF : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ∈ fourGrp x₁ x₂ :=
    p0b_rho_conj_mem_fourGrp h hzF
  have hρnorm : rho ∈ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    p0b_rho_mem_normalizer_fourGrp h
  have hzppF : rho⁻¹ * (x₁ * x₂) ^ 2 * rho ∈ fourGrp x₁ x₂ := by
    have hmem :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hρnorm) ((x₁ * x₂) ^ 2)).mp hzF
    simpa using hmem
  have hzp_ne_one : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ≠ 1 := by
    intro h1
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      calc (x₁ * x₂) ^ 2
          = rho⁻¹ * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) * rho := by group
        _ = rho⁻¹ * 1 * rho := by rw [h1]
        _ = 1 := by group
    exact hzne1 hz1
  have hzpp_ne_one : rho⁻¹ * (x₁ * x₂) ^ 2 * rho ≠ 1 := by
    intro h1
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      calc (x₁ * x₂) ^ 2
          = rho * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) * rho⁻¹ := by group
        _ = rho * 1 * rho⁻¹ := by rw [h1]
        _ = 1 := by group
    exact hzne1 hz1
  have hzp_ne_z : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ≠ (x₁ * x₂) ^ 2 := by
    intro h1
    have hc : rho * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * rho := by
      have := congrArg (fun u => u * rho) h1
      simpa [mul_assoc] using this
    exact hzne1 (p0b_eq_one_of_commute_rho_of_mem_fourGrp h hzF hc)
  have hzpp_ne_z : rho⁻¹ * (x₁ * x₂) ^ 2 * rho ≠ (x₁ * x₂) ^ 2 := by
    intro h1
    have hc : rho * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * rho := by
      have := congrArg (fun u => rho * u) h1
      have h2 : (x₁ * x₂) ^ 2 * rho = rho * (x₁ * x₂) ^ 2 := by
        simpa [mul_assoc] using this
      exact h2.symm
    exact hzne1 (p0b_eq_one_of_commute_rho_of_mem_fourGrp h hzF hc)
  have hzp_ne_zpp : rho * (x₁ * x₂) ^ 2 * rho⁻¹ ≠ rho⁻¹ * (x₁ * x₂) ^ 2 * rho := by
    intro h1
    have hρ3 : rho ^ 3 = 1 := by
      rw [← h.ord_rho]
      exact pow_orderOf_eq_one rho
    have hρ2m : rho ^ 2 * rho = 1 := by
      rw [← pow_succ]
      exact hρ3
    have hρm2 : rho * rho ^ 2 = 1 := by
      rw [← pow_succ']
      exact hρ3
    have hρinv : rho⁻¹ = rho ^ 2 := inv_eq_of_mul_eq_one_right hρm2
    have hρinvsq : (rho ^ 2)⁻¹ = rho := inv_eq_of_mul_eq_one_right hρ2m
    have hρsq : rho * rho = rho⁻¹ := by rw [← pow_two, ← hρinv]
    have hρinvsq2 : rho⁻¹ * rho⁻¹ = rho := by
      rw [← mul_inv_rev, ← pow_two, hρinvsq]
    have hconj : (x₁ * x₂) ^ 2 = rho⁻¹ * rho⁻¹ * (x₁ * x₂) ^ 2 * (rho * rho) := by
      have h := congrArg (fun u => rho⁻¹ * u * rho) h1
      calc (x₁ * x₂) ^ 2 = rho⁻¹ * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) * rho := by group
        _ = rho⁻¹ * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) * rho := by rw [h]
        _ = rho⁻¹ * rho⁻¹ * (x₁ * x₂) ^ 2 * (rho * rho) := by group
    have hconj' : (x₁ * x₂) ^ 2 = rho * (x₁ * x₂) ^ 2 * rho⁻¹ := by
      rw [hρinvsq2, hρsq] at hconj
      exact hconj
    have hc : rho * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * rho := by
      have := congrArg (fun u => u * rho) hconj'
      simpa [mul_assoc] using this.symm
    exact hzne1 (p0b_eq_one_of_commute_rho_of_mem_fourGrp h hzF hc)
  have hcases := S4A.mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2) hcomm hy2 hz2 hf
  have hzp_cases :=
    S4A.mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2) hcomm hy2 hz2 hzpF
  have hzpp_cases :=
    S4A.mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2) hcomm hy2 hz2 hzppF
  have hy_cases : x₁ ^ 2 = rho * (x₁ * x₂) ^ 2 * rho⁻¹ ∨
      x₁ ^ 2 = rho⁻¹ * (x₁ * x₂) ^ 2 * rho := by
    rcases hzp_cases with h1 | h1 | h1 | h1
    · exact absurd h1 hzp_ne_one
    · exact Or.inl h1.symm
    · exact absurd h1 hzp_ne_z
    · rcases hzpp_cases with h2 | h2 | h2 | h2
      · exact absurd h2 hzpp_ne_one
      · exact Or.inr h2.symm
      · exact absurd h2 hzpp_ne_z
      · exact absurd (h1.trans h2.symm) hzp_ne_zpp
  have hyz_cases : x₁ ^ 2 * (x₁ * x₂) ^ 2 = rho * (x₁ * x₂) ^ 2 * rho⁻¹ ∨
      x₁ ^ 2 * (x₁ * x₂) ^ 2 = rho⁻¹ * (x₁ * x₂) ^ 2 * rho := by
    rcases hzp_cases with h1 | h1 | h1 | h1
    · exact absurd h1 hzp_ne_one
    · rcases hzpp_cases with h2 | h2 | h2 | h2
      · exact absurd h2 hzpp_ne_one
      · exact absurd (h1.trans h2.symm) hzp_ne_zpp
      · exact absurd h2 hzpp_ne_z
      · exact Or.inr h2.symm
    · exact absurd h1 hzp_ne_z
    · exact Or.inl h1.symm
  rcases hcases with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · rcases hy_cases with h2 | h2
    · exact Or.inr (Or.inr (Or.inl (h1.trans h2)))
    · exact Or.inr (Or.inr (Or.inr (h1.trans h2)))
  · exact Or.inr (Or.inl h1)
  · rcases hyz_cases with h2 | h2
    · exact Or.inr (Or.inr (Or.inl (h1.trans h2)))
    · exact Or.inr (Or.inr (Or.inr (h1.trans h2)))

private theorem p0b_fourGrp_le_ctxX (t tau x₁ x₂ : G) :
    fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  rw [fourGrp, ctxX]
  refine (Subgroup.closure_le _).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> exact Subgroup.subset_closure (by simp)

private theorem p0b_fourGrp_le_baseGrp (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, baseGrp]
  refine (Subgroup.closure_le _).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact pow_mem (Subgroup.subset_closure (by simp)) 2
  · exact pow_mem (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

private theorem p0b_conj_mem_closure_of_gens {S : Set G} {g : G}
    (hgen : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) :
    ∀ w ∈ Subgroup.closure S, g * w * g⁻¹ ∈ Subgroup.closure S := by
  intro w hw
  refine Subgroup.closure_induction (p := fun w _ => g * w * g⁻¹ ∈ Subgroup.closure S)
    ?_ ?_ ?_ ?_ hw
  · intro x hx; exact hgen x hx
  · simp
  · intro x y hx hy ihx ihy
    have he : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [he]; exact mul_mem ihx ihy
  · intro x hx ihx
    have he : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [he]; exact inv_mem ihx

private theorem p0b_mem_ctxM_of (h : Ctx t L S x₁ x₂ lam rho tau) {g : G}
    (hgH : g ∈ invCent t)
    (hgNA : g ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G))
    (hgτ : g * tau * g⁻¹ ∈ ctxX t tau x₁ x₂) :
    g ∈ ctxM t tau x₁ x₂ := by
  have hVX : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ := p0b_fourGrp_le_ctxX t tau x₁ x₂
  have hgen : ∀ x ∈ ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G),
      g * x * g⁻¹ ∈ ctxX t tau x₁ x₂ := by
    intro x hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]
      have hcomm : g * t = t * g := S4A.mem_invCent_iff.mp hgH
      have : g * t * g⁻¹ = t := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]; exact Subgroup.subset_closure (by simp)
    · rw [hx]; exact hgτ
    · rw [hx]
      have hx₁A : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
      have hconjA : g * x₁ * g⁻¹ ∈ baseGrp x₁ x₂ :=
        (Subgroup.mem_normalizer_iff.mp hgNA x₁).mp hx₁A
      have hsq : g * x₁ ^ 2 * g⁻¹ = (g * x₁ * g⁻¹) ^ 2 := by rw [conj_pow]
      rw [hsq]
      exact hVX (by
        rw [WreathRel.fourGrp_eq_mho h.wreath]
        exact Subgroup.subset_closure ⟨g * x₁ * g⁻¹, hconjA, rfl⟩)
    · rw [hx]
      have hx₁x₂A : x₁ * x₂ ∈ baseGrp x₁ x₂ :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      have hconjA : g * (x₁ * x₂) * g⁻¹ ∈ baseGrp x₁ x₂ :=
        (Subgroup.mem_normalizer_iff.mp hgNA (x₁ * x₂)).mp hx₁x₂A
      have hsq : g * (x₁ * x₂) ^ 2 * g⁻¹ = (g * (x₁ * x₂) * g⁻¹) ^ 2 := by rw [conj_pow]
      rw [hsq]
      exact hVX (by
        rw [WreathRel.fourGrp_eq_mho h.wreath]
        exact Subgroup.subset_closure ⟨g * (x₁ * x₂) * g⁻¹, hconjA, rfl⟩)
  show g ∈ normalizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G)
  apply S4A.mem_normalizer_of_conj_mem
  intro x hx
  rw [ctxX] at hx ⊢
  exact p0b_conj_mem_closure_of_gens hgen x hx

private theorem p0b_conj_tau_eq_sq_mul_tau {a : G} (hinv : tau * a * tau⁻¹ = a⁻¹) :
    a * tau * a⁻¹ = a ^ 2 * tau := by
  calc a * tau * a⁻¹
      = a * (tau * a⁻¹ * tau⁻¹) * tau := by group
    _ = a * (tau * a * tau⁻¹)⁻¹ * tau := by
          rw [show tau * a⁻¹ * tau⁻¹ = (tau * a * tau⁻¹)⁻¹ by group]
    _ = a * (a⁻¹)⁻¹ * tau := by rw [hinv]
    _ = a ^ 2 * tau := by rw [inv_inv, pow_two]

private theorem p0b_tau_inv_mul (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
  have h12 : x₁⁻¹ * x₂⁻¹ = x₂⁻¹ * x₁⁻¹ := by
    have h := congrArg Inv.inv h.wreath.comm
    simpa only [mul_inv_rev] using h.symm
  calc tau * (x₁ * x₂) * tau⁻¹ = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
    _ = x₁⁻¹ * x₂⁻¹ := by rw [h.tau_x₁, h.tau_x₂]
    _ = (x₁ * x₂)⁻¹ := by rw [mul_inv_rev, h12]

private theorem p0b_yz_comm_tau (h : Ctx t L S x₁ x₂ lam rho tau) :
    (x₁ ^ 2 * (x₁ * x₂) ^ 2) * tau = tau * (x₁ ^ 2 * (x₁ * x₂) ^ 2) := by
  have hy : tau * x₁ ^ 2 = x₁ ^ 2 * tau := S4A.tau_commute_y h
  have hz : tau * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * tau := S4A.tau_commute_z h
  calc (x₁ ^ 2 * (x₁ * x₂) ^ 2) * tau
      = x₁ ^ 2 * ((x₁ * x₂) ^ 2 * tau) := by group
    _ = x₁ ^ 2 * (tau * (x₁ * x₂) ^ 2) := by rw [← hz]
    _ = (x₁ ^ 2 * tau) * (x₁ * x₂) ^ 2 := by group
    _ = (tau * x₁ ^ 2) * (x₁ * x₂) ^ 2 := by rw [← hy]
    _ = tau * (x₁ ^ 2 * (x₁ * x₂) ^ 2) := by group

private theorem p0b_rho_conj_rho_conj {rho z : G} (h2 : rho * rho = rho⁻¹)
    (hi2 : rho⁻¹ * rho⁻¹ = rho) :
    rho * (rho * z * rho⁻¹) * rho⁻¹ = rho⁻¹ * z * rho := by
  calc rho * (rho * z * rho⁻¹) * rho⁻¹
      = (rho * rho) * z * (rho⁻¹ * rho⁻¹) := by group
    _ = rho⁻¹ * z * rho := by rw [h2, hi2]

private theorem p0b_rho_inv_conj_rho_inv_conj {rho z : G} (h2 : rho * rho = rho⁻¹)
    (hi2 : rho⁻¹ * rho⁻¹ = rho) :
    rho⁻¹ * (rho⁻¹ * z * rho) * rho = rho * z * rho⁻¹ := by
  calc rho⁻¹ * (rho⁻¹ * z * rho) * rho
      = (rho⁻¹ * rho⁻¹) * z * (rho * rho) := by group
    _ = rho * z * rho⁻¹ := by rw [hi2, h2]


theorem p0_gens_mem_M (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    t ∈ ctxM t tau x₁ x₂ ∧ tau ∈ ctxM t tau x₁ x₂ ∧ x₁ ∈ ctxM t tau x₁ x₂ ∧
      x₂ ∈ ctxM t tau x₁ x₂ ∧ rho ∈ ctxM t tau x₁ x₂ ∧ lam ∈ ctxM t tau x₁ x₂ := by
  have hXle : ctxX t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := Subgroup.le_normalizer
  have htM : t ∈ ctxM t tau x₁ x₂ := hXle (Subgroup.subset_closure (by simp))
  have htauM : tau ∈ ctxM t tau x₁ x₂ := hXle (Subgroup.subset_closure (by simp))
  have hx₁H : x₁ ∈ invCent t := S4A.L_le_invCent hc.hyp (S4A.generators_mem_L hc.toCtx0).1
  have hx₂H : x₂ ∈ invCent t :=
    S4A.L_le_invCent hc.hyp (S4A.generators_mem_L hc.toCtx0).2.1
  have hx₁NA : x₁ ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (H := baseGrp x₁ x₂) (Subgroup.subset_closure (by simp))
  have hx₂NA : x₂ ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (H := baseGrp x₁ x₂) (Subgroup.subset_closure (by simp))
  have hx₁τ : x₁ * tau * x₁⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have h1 : x₁ * tau * x₁⁻¹ = x₁ ^ 2 * tau := by
      calc x₁ * tau * x₁⁻¹
          = x₁ * (tau * x₁⁻¹ * tau⁻¹) * tau := by group
        _ = x₁ * (tau * x₁ * tau⁻¹)⁻¹ * tau := by
              rw [show tau * x₁⁻¹ * tau⁻¹ = (tau * x₁ * tau⁻¹)⁻¹ by group]
        _ = x₁ * (x₁⁻¹)⁻¹ * tau := by rw [hc.tau_x₁]
        _ = x₁ ^ 2 * tau := by rw [inv_inv, pow_two]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hx₂τ : x₂ * tau * x₂⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have h2 : x₂ * tau * x₂⁻¹ = x₂ ^ 2 * tau := by
      calc x₂ * tau * x₂⁻¹
          = x₂ * (tau * x₂⁻¹ * tau⁻¹) * tau := by group
        _ = x₂ * (tau * x₂ * tau⁻¹)⁻¹ * tau := by
              rw [show tau * x₂⁻¹ * tau⁻¹ = (tau * x₂ * tau⁻¹)⁻¹ by group]
        _ = x₂ * (x₂⁻¹)⁻¹ * tau := by rw [hc.tau_x₂]
        _ = x₂ ^ 2 * tau := by rw [inv_inv, pow_two]
    rw [h2, WreathRel.x₂_sq hc.wreath]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))
  have hx₁M : x₁ ∈ ctxM t tau x₁ x₂ :=
    p0b_mem_ctxM_of hc.toCtx hx₁H hx₁NA hx₁τ
  have hx₂M : x₂ ∈ ctxM t tau x₁ x₂ :=
    p0b_mem_ctxM_of hc.toCtx hx₂H hx₂NA hx₂τ
  have hrhoH : rho ∈ invCent t := S4A.L_le_invCent hc.hyp hc.rho_mem
  have hrhoNA : rho ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    have hmem : rho ∈ Subgroup.normalizer (⁅ctxW t x₁ x₂, zpowers rho⁆ : Subgroup G) :=
      Subgroup.normalizer_commutator_ge_right (H₁ := ctxW t x₁ x₂) (H₂ := zpowers rho)
        (Subgroup.mem_zpowers rho)
    rwa [hc.comm_rho] at hmem
  have hrhoτ : rho * tau * rho⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have hcomm : rho * tau = tau * rho := hc.tau_rho.symm
    have : rho * tau * rho⁻¹ = tau := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact Subgroup.subset_closure (by simp)
  have hrhoM : rho ∈ ctxM t tau x₁ x₂ := p0b_mem_ctxM_of hc.toCtx hrhoH hrhoNA hrhoτ
  have hlamH : lam ∈ invCent t :=
    S4A.L_le_invCent hc.hyp (S4A.generators_mem_L hc.toCtx0).2.2
  have hlamNA : lam ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    have hlam2 : lam * lam = 1 := by
      have := pow_orderOf_eq_one lam
      rw [hc.wreath.ord_lam] at this
      simpa [pow_two] using this
    have hconj_x₂ : lam * x₂ * lam⁻¹ = x₁ := by
      rw [← hc.wreath.conj_x₁]
      calc lam * (lam * x₁ * lam⁻¹) * lam⁻¹
          = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := by group
        _ = x₁ := by rw [hlam2, ← mul_inv_rev, hlam2, inv_one, one_mul, mul_one]
    have hA : baseGrp x₁ x₂ ≤ (baseGrp x₁ x₂).comap (MulAut.conj lam).toMonoidHom := by
      change Subgroup.closure {x₁, x₂} ≤
        (baseGrp x₁ x₂).comap (MulAut.conj lam).toMonoidHom
      rw [Subgroup.closure_le]
      intro x hx
      apply Subgroup.mem_comap.mpr
      rcases hx with hx | hx
      · rw [hx]
        rw [show (MulAut.conj lam).toMonoidHom x₁ = x₂ from by
              simpa [MulAut.conj_apply] using hc.wreath.conj_x₁]
        exact Subgroup.subset_closure (by simp)
      · rw [hx]
        rw [show (MulAut.conj lam).toMonoidHom x₂ = x₁ from by
              simpa [MulAut.conj_apply] using hconj_x₂]
        exact Subgroup.subset_closure (by simp)
    apply S4A.mem_normalizer_of_conj_mem
    intro a ha
    simpa [MulAut.conj_apply] using Subgroup.mem_comap.mp (hA ha)
  have hlamτ : lam * tau * lam⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have hcomm : lam * tau = tau * lam := hc.tau_lam.symm
    have : lam * tau * lam⁻¹ = tau := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact Subgroup.subset_closure (by simp)
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := p0b_mem_ctxM_of hc.toCtx hlamH hlamNA hlamτ
  exact ⟨htM, htauM, hx₁M, hx₂M, hrhoM, hlamM⟩

theorem p0_V_le_N_le_X (t tau x₁ x₂ : G) :
    fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ ∧ ctxN tau x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  constructor
  · rw [fourGrp, ctxN]
    refine (Subgroup.closure_le (K := closure {tau, x₁ ^ 2, (x₁ * x₂) ^ 2})).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · rw [ctxN, ctxX]
    refine (Subgroup.closure_le (K := closure {t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2})).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem p0_rho_orbit_V (hc : Ctx4 t L S x₁ x₂ lam rho tau) {v w : G} (hv : v ∈ fourGrp x₁ x₂)
    (hv1 : v ≠ 1) (hw : w ∈ fourGrp x₁ x₂) (hw1 : w ≠ 1) :
    w = v ∨ w = rho * v * rho⁻¹ ∨ w = rho⁻¹ * v * rho := by
  have hρ3 : rho ^ 3 = 1 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  have hρ2m : rho ^ 2 * rho = 1 := by rw [← pow_succ]; exact hρ3
  have hρm2 : rho * rho ^ 2 = 1 := by rw [← pow_succ']; exact hρ3
  have hρinv : rho⁻¹ = rho ^ 2 := inv_eq_of_mul_eq_one_right hρm2
  have hρinvsq : (rho ^ 2)⁻¹ = rho := inv_eq_of_mul_eq_one_right hρ2m
  have hρsq : rho * rho = rho⁻¹ := by rw [← pow_two, ← hρinv]
  have hρinvsq2 : rho⁻¹ * rho⁻¹ = rho := by rw [← mul_inv_rev, ← pow_two, hρinvsq]
  have hv' := p0b_mem_fourGrp_cases_rho hc.toCtx0 hv
  have hw' := p0b_mem_fourGrp_cases_rho hc.toCtx0 hw
  rcases hv' with h1 | h1 | h1 | h1
  · exact absurd h1 hv1
  · rcases hw' with h2 | h2 | h2 | h2
    · exact absurd h2 hw1
    · left; rw [h1, h2]
    · right; left; rw [h1, h2]
    · right; right; rw [h1, h2]
  · rcases hw' with h2 | h2 | h2 | h2
    · exact absurd h2 hw1
    · right; right; rw [h1, h2]; group
    · left; rw [h1, h2]
    · right; left
      rw [h1, h2]
      exact (p0b_rho_conj_rho_conj hρsq hρinvsq2).symm
  · rcases hw' with h2 | h2 | h2 | h2
    · exact absurd h2 hw1
    · right; left; rw [h1, h2]; group
    · right; right
      rw [h1, h2]
      exact (p0b_rho_inv_conj_rho_inv_conj hρsq hρinvsq2).symm
    · left; rw [h1, h2]

theorem p0_t_mul_mem_tM (hc : Ctx8 t L S x₁ x₂ lam rho tau) {n : G} (hn : n ∈ ctxN tau x₁ x₂) :
    t * n ∈ conjIn (ctxM t tau x₁ x₂) t := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  rw [hc.tM]
  rcases l12_N_cases hc4 hn with hnV | htnV
  · left
    exact Set.mem_smul_set.mpr ⟨n, hnV, by rw [smul_eq_mul]⟩
  · right
    refine Set.mem_smul_set.mpr ⟨tau * n, htnV, ?_⟩
    rw [smul_eq_mul, mul_assoc t tau (tau * n), ← mul_assoc tau tau n, htau2, one_mul]

theorem p0_tM_mul_mem_N (hc : Ctx8 t L S x₁ x₂ lam rho tau) {u u' : G}
    (hu : u ∈ conjIn (ctxM t tau x₁ x₂) t) (hu' : u' ∈ conjIn (ctxM t tau x₁ x₂) t) :
    u * u' ∈ ctxN tau x₁ x₂ := by
  have hVN : fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ := (p0_V_le_N_le_X t tau x₁ x₂).1
  have hNcent : ctxN tau x₁ x₂ ≤ invCent t := by
    rw [ctxN]
    refine (Subgroup.closure_le (K := invCent t)).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hc.le_invCent hc.tau_mem
    · exact S4A.L_le_invCent hc.hyp (S4A.y_z_mem_L hc.toCtx0).1
    · exact S4A.L_le_invCent hc.hyp (S4A.y_z_mem_L hc.toCtx0).2
  have hex : ∀ {x : G}, x ∈ conjIn (ctxM t tau x₁ x₂) t → ∃ a ∈ ctxN tau x₁ x₂, x = t * a := by
    intro x hx
    have hcases : x ∈ t • (fourGrp x₁ x₂ : Set G) ∪
        (t * tau) • (fourGrp x₁ x₂ : Set G) := by rw [← hc.tM]; exact hx
    rcases hcases with hxV | hxτV
    · obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hxV
      exact ⟨v, hVN hv, by rw [smul_eq_mul]⟩
    · obtain ⟨v, hv, hvv⟩ := Set.mem_smul_set.mp hxτV
      refine ⟨tau * v, mul_mem (Subgroup.subset_closure (by simp)) (hVN hv), ?_⟩
      rw [← hvv, smul_eq_mul, mul_assoc]
  obtain ⟨a, haN, rfl⟩ := hex hu
  obtain ⟨a', ha'N, rfl⟩ := hex hu'
  have hta : t * a = a * t := (S4A.mem_invCent_iff.mp (hNcent haN)).symm
  have hta' : t * a' = a' * t := (S4A.mem_invCent_iff.mp (hNcent ha'N)).symm
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have heq : (t * a) * (t * a') = a * a' := by
    calc (t * a) * (t * a') = t * (a * t) * a' := by group
      _ = t * (t * a) * a' := by rw [← hta]
      _ = (t * t) * (a * a') := by group
      _ = a * a' := by rw [ht2, one_mul]
  rw [heq]
  exact mul_mem haN ha'N

theorem p0_normal_N (hc : Ctx8 t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxN tau x₁ x₂) (ctxM t tau x₁ x₂) := by
  refine ⟨?hle, ?hnorm⟩
  · have hNX : ctxN tau x₁ x₂ ≤ ctxX t tau x₁ x₂ := (p0_V_le_N_le_X t tau x₁ x₂).2
    exact hNX.trans Subgroup.le_normalizer
  · intro g hg k hk
    have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
    have hk' : k = t * (t * k) := by rw [← mul_assoc, ht2, one_mul]
    rw [hk']
    have h1 : g * t * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) t := ⟨g, hg, rfl⟩
    have h2 : g * (t * k) * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) t := by
      obtain ⟨m, hm, hmk⟩ := p0_t_mul_mem_tM hc hk
      exact ⟨g * m, mul_mem hg hm, by rw [← hmk]; group⟩
    have heq : g * (t * (t * k)) * g⁻¹ = (g * t * g⁻¹) * (g * (t * k) * g⁻¹) := by group
    rw [heq]
    exact p0_tM_mul_mem_N hc h1 h2

theorem p0_conj_z_mem_V (hc : Ctx8 t L S x₁ x₂ lam rho tau)
    (hM : Nat.card ↥(ctxM t tau x₁ x₂) = 3 * 2 ^ 10)
    (hN : NormalIn (ctxN tau x₁ x₂) (ctxM t tau x₁ x₂)) {m : G} (hm : m ∈ ctxM t tau x₁ x₂) :
    m * (x₁ * x₂) ^ 2 * m⁻¹ ∈ fourGrp x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hVN : fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ := (p0_V_le_N_le_X t tau x₁ x₂).1
  set z : G := (x₁ * x₂) ^ 2 with hzdef
  have hzV : z ∈ fourGrp x₁ x₂ := by rw [hzdef]; exact Subgroup.subset_closure (by simp)
  have hzne1 : z ≠ 1 := by rw [hzdef]; exact (S4A.z_mul_self_ne_one hc4.toCtx0).2
  have hzN : z ∈ ctxN tau x₁ x₂ := hVN hzV
  set u : G := m * z * m⁻¹ with hudef
  have huN : u ∈ ctxN tau x₁ x₂ := by rw [hudef]; exact hN.2 m hm z hzN
  rcases l12_N_cases hc4 huN with huV | htuV
  · exact huV
  · by_contra huV
    obtain ⟨htM, htauM, hx1M, hx2M, hrhoM, hlamM⟩ := p0_gens_mem_M hc4
    have hx12M : x₁ * x₂ ∈ ctxM t tau x₁ x₂ := mul_mem hx1M hx2M
    have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
    have hu_eq : u = tau * (tau * u) := by rw [← mul_assoc, htau2, one_mul]
    have huB : tau * u ∈ baseGrp x₁ x₂ := p0b_fourGrp_le_baseGrp x₁ x₂ htuV
    have hx1τ : x₁ * tau * x₁⁻¹ = x₁ ^ 2 * tau := p0b_conj_tau_eq_sq_mul_tau hc.tau_x₁
    have hx2τ : x₂ * tau * x₂⁻¹ = x₂ ^ 2 * tau := p0b_conj_tau_eq_sq_mul_tau hc.tau_x₂
    have hx12τ : (x₁ * x₂) * tau * (x₁ * x₂)⁻¹ = (x₁ * x₂) ^ 2 * tau :=
      p0b_conj_tau_eq_sq_mul_tau (p0b_tau_inv_mul hc.toCtx)
    have hx1u : x₁ * (tau * u) * x₁⁻¹ = tau * u :=
      p0b_baseGrp_conj_eq_of_mem hc4.toCtx0 (Subgroup.subset_closure (by simp)) huB
    have hx2u : x₂ * (tau * u) * x₂⁻¹ = tau * u :=
      p0b_baseGrp_conj_eq_of_mem hc4.toCtx0 (Subgroup.subset_closure (by simp)) huB
    have hx12u : (x₁ * x₂) * (tau * u) * (x₁ * x₂)⁻¹ = tau * u :=
      p0b_baseGrp_conj_eq_of_mem hc4.toCtx0
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))) huB
    have hx1conj : x₁ * u * x₁⁻¹ = tau * (x₁ ^ 2 * (tau * u)) := by
      calc x₁ * u * x₁⁻¹ = x₁ * (tau * (tau * u)) * x₁⁻¹ := by conv_lhs => rw [hu_eq]
        _ = (x₁ * tau * x₁⁻¹) * (x₁ * (tau * u) * x₁⁻¹) := by group
        _ = (x₁ ^ 2 * tau) * (tau * u) := by rw [hx1τ, hx1u]
        _ = tau * (x₁ ^ 2 * (tau * u)) := by rw [← S4A.tau_commute_y hc.toCtx]; group
    have hx2conj : x₂ * u * x₂⁻¹ = tau * ((x₁ ^ 2 * (x₁ * x₂) ^ 2) * (tau * u)) := by
      have hx2sq : x₂ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := WreathRel.x₂_sq hc.wreath
      calc x₂ * u * x₂⁻¹ = x₂ * (tau * (tau * u)) * x₂⁻¹ := by conv_lhs => rw [hu_eq]
        _ = (x₂ * tau * x₂⁻¹) * (x₂ * (tau * u) * x₂⁻¹) := by group
        _ = (x₂ ^ 2 * tau) * (tau * u) := by rw [hx2τ, hx2u]
        _ = tau * ((x₁ ^ 2 * (x₁ * x₂) ^ 2) * (tau * u)) := by
              rw [hx2sq, p0b_yz_comm_tau hc.toCtx]; group
    have hx12conj : (x₁ * x₂) * u * (x₁ * x₂)⁻¹ = tau * ((x₁ * x₂) ^ 2 * (tau * u)) := by
      calc (x₁ * x₂) * u * (x₁ * x₂)⁻¹
          = (x₁ * x₂) * (tau * (tau * u)) * (x₁ * x₂)⁻¹ := by conv_lhs => rw [hu_eq]
        _ = ((x₁ * x₂) * tau * (x₁ * x₂)⁻¹) * ((x₁ * x₂) * (tau * u) * (x₁ * x₂)⁻¹) := by
              group
        _ = ((x₁ * x₂) ^ 2 * tau) * (tau * u) := by rw [hx12τ, hx12u]
        _ = tau * ((x₁ * x₂) ^ 2 * (tau * u)) := by rw [← S4A.tau_commute_z hc.toCtx]; group
    have hV1 : ((fourGrp x₁ x₂ : Set G) \ {1}) ⊆ conjIn (ctxM t tau x₁ x₂) z := by
      intro v hv
      have hv1 : v ≠ 1 := hv.2
      rcases p0b_mem_fourGrp_cases_rho hc4.toCtx0 hv.1 with h1 | h1 | h1 | h1
      · exact absurd h1 hv1
      · rw [h1]
        exact ⟨1, Subgroup.one_mem (ctxM t tau x₁ x₂), by rw [hzdef]; group⟩
      · rw [h1]
        exact ⟨rho, hrhoM, by rw [hzdef]⟩
      · rw [h1]
        refine ⟨rho⁻¹, inv_mem hrhoM, ?_⟩
        rw [inv_inv, hzdef]
    have hτV : (tau • (fourGrp x₁ x₂ : Set G)) ⊆ conjIn (ctxM t tau x₁ x₂) z := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hw
      have heV : v * (tau * u)⁻¹ ∈ fourGrp x₁ x₂ := mul_mem hv (inv_mem htuV)
      have hve : v = (v * (tau * u)⁻¹) * (tau * u) := by group
      rcases S4A.mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2)
          (S4A.y_commute_z hc.wreath) (S4A.y_mul_self_ne_one hc.wreath).1
          (S4A.z_mul_self_ne_one hc4.toCtx0).1 heV with he | he | he | he
      · refine ⟨m, hm, ?_⟩
        rw [smul_eq_mul, hve, he, one_mul]
        rw [← hu_eq, hudef]
      · refine ⟨x₁ * m, mul_mem hx1M hm, ?_⟩
        rw [smul_eq_mul, hve, he]
        rw [show (x₁ * m) * z * (x₁ * m)⁻¹ = x₁ * u * x₁⁻¹ by rw [hudef]; group, hx1conj]
      · refine ⟨(x₁ * x₂) * m, mul_mem hx12M hm, ?_⟩
        rw [smul_eq_mul, hve, he]
        rw [show ((x₁ * x₂) * m) * z * ((x₁ * x₂) * m)⁻¹ =
              (x₁ * x₂) * u * (x₁ * x₂)⁻¹ by rw [hudef]; group, hx12conj]
      · refine ⟨x₂ * m, mul_mem hx2M hm, ?_⟩
        rw [smul_eq_mul, hve, he]
        rw [show (x₂ * m) * z * (x₂ * m)⁻¹ = x₂ * u * x₂⁻¹ by rw [hudef]; group, hx2conj]
    have hVcard : Nat.card ↥(fourGrp x₁ x₂) = 4 := hc.wreath.fourGrp_eq_omega.2.2
    have hVncard : (fourGrp x₁ x₂ : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]; exact hVcard
    have hV1card : ((fourGrp x₁ x₂ : Set G) \ {1}).ncard = 3 := by
      rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem (fourGrp x₁ x₂)), hVncard]
    have hτVcard : (tau • (fourGrp x₁ x₂ : Set G)).ncard = 4 := by
      rw [← Set.image_smul]
      rw [Set.ncard_image_of_injective _ (fun a b hab => by
        simpa [smul_eq_mul] using mul_left_cancel hab)]
      exact hVncard
    have hdisj : Disjoint ((fourGrp x₁ x₂ : Set G) \ {1}) (tau • (fourGrp x₁ x₂ : Set G)) := by
      rw [Set.disjoint_left]
      intro x hx hxt
      obtain ⟨v, hv, hvv⟩ := Set.mem_smul_set.mp hxt
      have htauV : tau ∈ fourGrp x₁ x₂ := by
        have h : x * v⁻¹ ∈ fourGrp x₁ x₂ := mul_mem hx.1 (inv_mem hv)
        rwa [← hvv, smul_eq_mul, mul_assoc, mul_inv_cancel, mul_one] at h
      exact l12_tau_not_mem_V hc4 htauV
    have hunion : (((fourGrp x₁ x₂ : Set G) \ {1}) ∪
        (tau • (fourGrp x₁ x₂ : Set G))).ncard = 7 := by
      rw [Set.ncard_union_eq hdisj, hV1card, hτVcard]
    have hNdiff : (ctxN tau x₁ x₂ : Set G) \ {1} =
        ((fourGrp x₁ x₂ : Set G) \ {1}) ∪ (tau • (fourGrp x₁ x₂ : Set G)) := by
      ext x
      constructor
      · intro hx
        have hx1 : x ≠ 1 := hx.2
        rcases l12_N_cases hc4 hx.1 with hxV | htxV
        · exact Or.inl ⟨hxV, hx1⟩
        · right
          refine Set.mem_smul_set.mpr ⟨tau * x, htxV, ?_⟩
          rw [smul_eq_mul, ← mul_assoc, htau2, one_mul]
      · intro hx
        rcases hx with hxV | hxτV
        · exact ⟨hVN hxV.1, hxV.2⟩
        · obtain ⟨v, hv, hvv⟩ := Set.mem_smul_set.mp hxτV
          have hxN : x ∈ ctxN tau x₁ x₂ := by
            rw [← hvv, smul_eq_mul]
            exact mul_mem (Subgroup.subset_closure (by simp)) (hVN hv)
          have hx1 : x ≠ 1 := by
            rintro h1
            have htau_eq : tau = v⁻¹ := by
              have hv1 : tau * v = 1 := by rw [← smul_eq_mul, hvv]; exact h1
              calc tau = (tau * v) * v⁻¹ := by group
                _ = 1 * v⁻¹ := by rw [hv1]
                _ = v⁻¹ := one_mul _
            have htv : tau ∈ fourGrp x₁ x₂ := by
              have := inv_mem hv
              rwa [← htau_eq] at this
            exact l12_tau_not_mem_V hc4 htv
          exact ⟨hxN, hx1⟩
    have hclass_sub : conjIn (ctxM t tau x₁ x₂) z ⊆ (ctxN tau x₁ x₂ : Set G) \ {1} := by
      intro y hy
      obtain ⟨k, hk, hky⟩ := hy
      refine ⟨?_, ?_⟩
      · rw [← hky]; exact hN.2 k hk z hzN
      · rintro h1
        have hz1 : z = 1 := by
          have hkz : k * z * k⁻¹ = 1 := hky.trans h1
          calc z = k⁻¹ * (k * z * k⁻¹) * k := by group
            _ = k⁻¹ * 1 * k := by rw [hkz]
            _ = 1 := by group
        exact hzne1 hz1
    have hclass_rev : (ctxN tau x₁ x₂ : Set G) \ {1} ⊆ conjIn (ctxM t tau x₁ x₂) z := by
      intro y hy
      rw [hNdiff] at hy
      rcases hy with hyV | hyτV
      · exact hV1 hyV
      · exact hτV hyτV
    have hclass : conjIn (ctxM t tau x₁ x₂) z =
        ((fourGrp x₁ x₂ : Set G) \ {1}) ∪ (tau • (fourGrp x₁ x₂ : Set G)) := by
      rw [← hNdiff]
      exact Set.Subset.antisymm hclass_sub hclass_rev
    have hclass_ncard : (conjIn (ctxM t tau x₁ x₂) z).ncard = 7 := by
      rw [hclass, hunion]
    have h7 : 7 ∣ Nat.card ↥(ctxM t tau x₁ x₂) := by
      rw [card_eq_ncard_conjIn_mul (G := G) (ctxM t tau x₁ x₂) z, hclass_ncard]
      exact dvd_mul_right 7 _
    rw [hM] at h7
    norm_num at h7

theorem p0_normal_V (hc : Ctx8 t L S x₁ x₂ lam rho tau)
    (hM : Nat.card ↥(ctxM t tau x₁ x₂) = 3 * 2 ^ 10)
    (hN : NormalIn (ctxN tau x₁ x₂) (ctxM t tau x₁ x₂)) :
    NormalIn (fourGrp x₁ x₂) (ctxM t tau x₁ x₂) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hVN : fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ := (p0_V_le_N_le_X t tau x₁ x₂).1
  have hNM : ctxN tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := (p0_normal_N hc).1
  refine ⟨hVN.trans hNM, ?_⟩
  intro g hg v hv
  obtain ⟨htM, htauM, hx1M, hx2M, hrhoM, hlamM⟩ := p0_gens_mem_M hc4
  rcases p0b_mem_fourGrp_cases_rho hc4.toCtx0 hv with h1 | h1 | h1 | h1
  · rw [h1]; simpa using Subgroup.one_mem (fourGrp x₁ x₂)
  · rw [h1]
    exact p0_conj_z_mem_V hc hM hN hg
  · rw [h1]
    have heq : (g * rho) * (x₁ * x₂) ^ 2 * (g * rho)⁻¹ =
        g * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) * g⁻¹ := by group
    rw [← heq]
    exact p0_conj_z_mem_V hc hM hN (mul_mem hg hrhoM)
  · rw [h1]
    have heq : (g * rho⁻¹) * (x₁ * x₂) ^ 2 * (g * rho⁻¹)⁻¹ =
        g * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) * g⁻¹ := by group
    rw [← heq]
    exact p0_conj_z_mem_V hc hM hN (mul_mem hg (inv_mem hrhoM))

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

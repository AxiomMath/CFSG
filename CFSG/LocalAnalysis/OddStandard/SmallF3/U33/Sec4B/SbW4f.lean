module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemXA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4_cent_E
    (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    ctxO t tau x₁ x₂ ⊓ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) =
      closure ({t, tau, x₁, x₂} : Set G) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have htC : t ∈ closure ({t, tau, x₁, x₂} : Set G) := Subgroup.subset_closure (by simp)
  have htauC : tau ∈ closure ({t, tau, x₁, x₂} : Set G) := Subgroup.subset_closure (by simp)
  have hx₁C : x₁ ∈ closure ({t, tau, x₁, x₂} : Set G) := Subgroup.subset_closure (by simp)
  have hx₂C : x₂ ∈ closure ({t, tau, x₁, x₂} : Set G) := Subgroup.subset_closure (by simp)
  have hCE : centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) =
      closure ({t, tau, x₁, x₂} : Set G) := by
    rw [S4A.centralizer_E_of hc4.toCtx, ctxW, hc4.l43]
    apply le_antisymm
    · refine sup_le (sup_le (Subgroup.zpowers_le.mpr htC) ?_) (Subgroup.zpowers_le.mpr htauC)
      rw [baseGrp, Subgroup.closure_le]
      intro x hx
      rcases (by simpa using hx) with h | h
      · rw [h]; exact hx₁C
      · rw [h]; exact hx₂C
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h | h
      · rw [h]
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)
      · rw [h]
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
      · rw [h]
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  obtain ⟨htO, htauO, hx₁O, hx₂O⟩ := w4_gens_mem_O hc
  have hle : closure ({t, tau, x₁, x₂} : Set G) ≤ ctxO t tau x₁ x₂ := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact htO
    · rw [h]; exact htauO
    · rw [h]; exact hx₁O
    · rw [h]; exact hx₂O
  rw [hCE]
  exact inf_eq_right.mpr hle

theorem w4_normal_centE
    (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    NormalIn (closure ({t, tau, x₁, x₂} : Set G)) (ctxM t tau x₁ x₂) := by
  rw [← w4_cent_E hc]
  refine ⟨inf_le_left.trans (p0_O_le_M t tau x₁ x₂), fun g hg c hcc => ?_⟩
  obtain ⟨hcO, hcC⟩ := Subgroup.mem_inf.mp hcc
  refine Subgroup.mem_inf.mpr ⟨(p0_normal_O t tau x₁ x₂).2 g hg c hcO, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have he' : g⁻¹ * e * g ∈ ctxE t x₁ x₂ := by
    simpa using hc.normal_E.2 g⁻¹ (inv_mem hg) e he
  have hcomm : (g⁻¹ * e * g) * c = c * (g⁻¹ * e * g) :=
    Subgroup.mem_centralizer_iff.mp hcC _ he'
  calc e * (g * c * g⁻¹) = g * ((g⁻¹ * e * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * e * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * c * g⁻¹) * e := by group

private theorem w4_lam_normalizes_Q (hc : W4Ctxa t L S x₁ x₂ lam rho tau) :
    lam ∈ Subgroup.normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc.toCtx10.toCtx4).2.2.2.2.2
  have hlam_normO : lam ∈ Subgroup.normalizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact (p0_normal_O t tau x₁ x₂).2 lam hlamM h hh
    · intro hh
      have hh' := (p0_normal_O t tau x₁ x₂).2 lam⁻¹ (inv_mem hlamM) (lam * h * lam⁻¹) hh
      simpa [mul_assoc] using hh'
  have hOmap : (ctxO t tau x₁ x₂).map (MulAut.conj lam) = ctxO t tau x₁ x₂ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hlam_normO
  have hRhomap : (Subgroup.zpowers rho).map (MulAut.conj lam) = Subgroup.zpowers rho := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj lam) rho) = Subgroup.zpowers rho
    rw [MulAut.conj_apply, hc.lam_rho, Subgroup.zpowers_inv]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [ctxQ, Subgroup.map_commutator, hOmap, hRhomap]

theorem w4_Q_le_O (hc : W4Ctxa t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := by
  have hρM : rho ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc.toCtx10.toCtx4).2.2.2.2.1
  rw [ctxQ, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₂M : g₂ ∈ ctxM t tau x₁ x₂ := (Subgroup.zpowers_le.mpr hρM) hg₂
  rw [commutatorElement_def]
  have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ ctxO t tau x₁ x₂ :=
    (p0_normal_O t tau x₁ x₂).2 g₂ hg₂M g₁⁻¹ (inv_mem hg₁)
  have h2 : g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) ∈ ctxO t tau x₁ x₂ := mul_mem hg₁ h1
  simpa [mul_assoc] using h2

theorem w4_normal_Q (hc : W4Ctxc t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxQ t tau x₁ x₂ rho) (ctxM t tau x₁ x₂) := by
  have hρM : rho ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc.toCtx10.toCtx4).2.2.2.2.1
  have hO : (ctxO t tau x₁ x₂ : Subgroup G) ≤
      Subgroup.normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left (ctxO t tau x₁ x₂) (Subgroup.zpowers rho)
  have hrho : rho ∈ Subgroup.normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right (ctxO t tau x₁ x₂) (Subgroup.zpowers rho)
      (Subgroup.mem_zpowers rho)
  have hM : (ctxM t tau x₁ x₂ : Subgroup G) ≤
      Subgroup.normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [hc.M_eq]
    refine sup_le hO ?_
    rw [Subgroup.closure_le]
    intro x hx
    rcases (by simpa using hx) with h | h
    · rw [h]; exact hrho
    · rw [h]; exact w4_lam_normalizes_Q hc.toW4Ctxa
  refine ⟨(w4_Q_le_O hc.toW4Ctxa).trans (p0_O_le_M t tau x₁ x₂), ?_⟩
  intro g hg k hk
  exact (Subgroup.mem_normalizer_iff.mp (hM hg) k).mp hk

theorem w4_base_le_Q (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    baseGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  obtain ⟨htO, -, hx₁O, hx₂O⟩ := w4_gens_mem_O hc
  rw [← hc4.comm_rho, ctxQ]
  refine Subgroup.commutator_mono ?_ le_rfl
  rw [ctxW, hc4.l43]
  refine sup_le (Subgroup.zpowers_le.mpr htO) ?_
  rw [baseGrp, Subgroup.closure_le]
  intro x hx
  rcases (by simpa using hx) with h | h
  · rw [h]; exact hx₁O
  · rw [h]; exact hx₂O

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

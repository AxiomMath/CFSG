module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0i

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem p0_Q_le_R (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho ≤ ctxR t tau x₁ x₂ := by
  simpa only [ctxQ] using p0_comm_O_le_R hc

private theorem p0_lam_normalizes_Q (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
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

theorem p0_normal_Q (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxQ t tau x₁ x₂ rho) (ctxM t tau x₁ x₂) := by
  have hrhoM : rho ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc.toCtx10.toCtx4).2.2.2.2.1
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
    rcases (by simpa using hx) with rfl | rfl
    · exact hrho
    · exact p0_lam_normalizes_Q hc
  refine ⟨(p0_Q_le_R hc).trans (hc.R_le_O.trans (p0_O_le_M t tau x₁ x₂)), ?_⟩
  intro g hg k hk
  exact (Subgroup.mem_normalizer_iff.mp (hM hg) k).mp hk

theorem p0_base_le_Q (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    baseGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho := by
  rw [← hc.comm_rho, ctxQ]
  refine Subgroup.commutator_mono ?_ le_rfl
  rw [ctxW, hc.toCtx10.toCtx4.l43]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact hc.R_le_O (hc.X_le_R (Subgroup.subset_closure (by simp)))
  · rw [baseGrp, Subgroup.closure_le]
    intro x hx
    rcases (by simpa using hx) with rfl | rfl
    · exact hc.R_le_O (p0_x₁_x₂_mem_R hc.toCtx8c).1
    · exact hc.R_le_O (p0_x₁_x₂_mem_R hc.toCtx8c).2

theorem p0_R_eq (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    ctxR t tau x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊔ ctxX t tau x₁ x₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrhoM : rho ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc.toCtx10.toCtx4).2.2.2.2.1
  have hRX : (Subgroup.zpowers rho : Subgroup G) ≤
      Subgroup.normalizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact hc.normal_R.2 rho hrhoM h hh
    · intro hh
      have hinv : rho⁻¹ ∈ ctxM t tau x₁ x₂ := (ctxM t tau x₁ x₂).inv_mem hrhoM
      have h' := hc.normal_R.2 rho⁻¹ hinv (rho * h * rho⁻¹) hh
      simpa [mul_assoc] using h'
  have hRN : (Subgroup.zpowers rho : Subgroup G) ≤
      Subgroup.normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact (p0_normal_Q hc).2 rho hrhoM h hh
    · intro hh
      have hinv : rho⁻¹ ∈ ctxM t tau x₁ x₂ := (ctxM t tau x₁ x₂).inv_mem hrhoM
      have h' := (p0_normal_Q hc).2 rho⁻¹ hinv (rho * h * rho⁻¹) hh
      simpa [mul_assoc] using h'
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := (p0_Q_le_R hc).trans hc.R_le_O
  have hQ2 : IsPGroup 2 ↥(ctxQ t tau x₁ x₂ rho) := (p0_isPGroup_O t tau x₁ x₂).to_le hQO
  have hR3 : IsPGroup 3 ↥(Subgroup.zpowers rho) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hc.ord_rho]
    norm_num
  have hN3 : ¬ 3 ∣ Nat.card ↥(ctxQ t tau x₁ x₂ rho) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ2
    rw [hk]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hcomm : ⁅ctxR t tau x₁ x₂, Subgroup.zpowers rho⁆ ≤ ctxQ t tau x₁ x₂ rho := by
    rw [ctxQ]
    exact Subgroup.commutator_mono hc.R_le_O le_rfl
  have hcover := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    (p := 3) (X := ctxR t tau x₁ x₂) (N := ctxQ t tau x₁ x₂ rho) (R := Subgroup.zpowers rho)
    (p0_Q_le_R hc) hRX hRN hR3 hN3 hcomm
  have hcent : Subgroup.centralizer ((Subgroup.zpowers rho : Subgroup G) : Set G) =
      Subgroup.centralizer ({rho} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent, hc.CR_rho] at hcover
  apply le_antisymm
  · rw [← hcover]
    refine sup_le ?_ le_sup_left
    rw [Subgroup.closure_le]
    intro x hx
    rcases (by simpa using hx) with rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  · exact sup_le (p0_Q_le_R hc) hc.X_le_R

theorem p0_phi_Q (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ ctxPhi (ctxQ t tau x₁ x₂ rho) ∧
      ctxPhi (ctxQ t tau x₁ x₂ rho) ≤ ctxX t tau x₁ x₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := (p0_Q_le_R hc).trans hc.R_le_O
  haveI : Fact (IsPGroup 2 ↥(ctxQ t tau x₁ x₂ rho)) :=
    ⟨(p0_isPGroup_O t tau x₁ x₂).to_le hQO⟩
  constructor
  · have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
      p0_base_le_Q hc (Subgroup.subset_closure (by simp))
    have hx₂Q : x₂ ∈ ctxQ t tau x₁ x₂ rho :=
      p0_base_le_Q hc (Subgroup.subset_closure (by simp))
    have hprodQ : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho :=
      (ctxQ t tau x₁ x₂ rho).mul_mem hx₁Q hx₂Q
    rw [fourGrp, Subgroup.closure_le]
    intro y hy
    rcases (by simpa using hy) with rfl | rfl
    · rw [ctxPhi]
      exact Subgroup.mem_map.mpr
        ⟨(⟨x₁, hx₁Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) ^ 2,
          pth_power_mem_frattini_of_isPGroup (p := 2) _, by simp⟩
    · rw [ctxPhi]
      exact Subgroup.mem_map.mpr
        ⟨(⟨x₁ * x₂, hprodQ⟩ : ↥(ctxQ t tau x₁ x₂ rho)) ^ 2,
          pth_power_mem_frattini_of_isPGroup (p := 2) _, by simp⟩
  · rw [ctxPhi]
    refine Subgroup.map_le_iff_le_comap.mpr ?_
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    refine (Subgroup.closure_le (K := Subgroup.comap (ctxQ t tau x₁ x₂ rho).subtype
      (ctxX t tau x₁ x₂))).2 ?_
    intro z hz
    rcases hz with hz | hz
    · rw [commutator_eq_closure] at hz
      refine (Subgroup.closure_le (K := Subgroup.comap (ctxQ t tau x₁ x₂ rho).subtype
        (ctxX t tau x₁ x₂))).2 ?_ hz
      intro w hw
      rw [mem_commutatorSet_iff] at hw
      obtain ⟨u, v, rfl⟩ := hw
      exact hc.R_quot.2 u.1 (p0_Q_le_R hc u.2) v.1 (p0_Q_le_R hc v.2)
    · obtain ⟨x, rfl⟩ := hz
      exact hc.R_quot.1 x.1 (p0_Q_le_R hc x.2)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

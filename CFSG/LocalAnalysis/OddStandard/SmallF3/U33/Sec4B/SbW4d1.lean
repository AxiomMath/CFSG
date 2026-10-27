module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4Defs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4_X_comm
    (hc : Ctx4 t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxX t tau x₁ x₂) (hb : b ∈ ctxX t tau x₁ x₂) : a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm (S4A.ctxX_elemAbelian_of hc.toCtx hc.l44.1).1 ha hb

theorem w4_V_le_X (t tau x₁ x₂ : G) : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ :=
  (p0_V_le_N_le_X t tau x₁ x₂).1.trans (p0_V_le_N_le_X t tau x₁ x₂).2

theorem w4_tau_comm_V
    (hc : Ctx4 t L S x₁ x₂ lam rho tau) {v : G}
    (hv : v ∈ fourGrp x₁ x₂) : tau * v = v * tau :=
  w4_X_comm hc (Subgroup.subset_closure (by simp)) (w4_V_le_X t tau x₁ x₂ hv)

theorem w4_t_comm_tau
    (hc : Ctx4 t L S x₁ x₂ lam rho tau) : t * tau = tau * t :=
  w4_X_comm hc (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem w4_mem_normalizer_V {M : Subgroup G} (hV : NormalIn (fourGrp x₁ x₂) M) {g : G}
    (hg : g ∈ M) : g ∈ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => hV.2 g hg v hv, fun hv => ?_⟩
  have h := hV.2 g⁻¹ (inv_mem hg) _ hv
  simpa [mul_assoc] using h

theorem w4_mul_mem_smul {v : G} (hv : v ∈ fourGrp x₁ x₂) :
    tau * v ∈ tau • (fourGrp x₁ x₂ : Set G) :=
  Set.mem_smul_set.mpr ⟨v, hv, rfl⟩

@[expose] def w4Ktau (tau x₁ x₂ : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) ∧
    g * tau * g⁻¹ ∈ tau • (fourGrp x₁ x₂ : Set G)}
  mul_mem' := by
    rintro g h ⟨hgN, hgτ⟩ ⟨hhN, hhτ⟩
    refine ⟨mul_mem hgN hhN, ?_⟩
    obtain ⟨v, hv, hve⟩ := Set.mem_smul_set.mp hhτ
    obtain ⟨w, hw, hwe⟩ := Set.mem_smul_set.mp hgτ
    have hgv : g * v * g⁻¹ ∈ fourGrp x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
    refine Set.mem_smul_set.mpr ⟨w * (g * v * g⁻¹), mul_mem hw hgv, ?_⟩
    simp only [smul_eq_mul] at hve hwe ⊢
    calc tau * (w * (g * v * g⁻¹)) = (tau * w) * (g * v * g⁻¹) := by group
      _ = (g * tau * g⁻¹) * (g * v * g⁻¹) := by rw [hwe]
      _ = g * (tau * v) * g⁻¹ := by group
      _ = g * (h * tau * h⁻¹) * g⁻¹ := by rw [hve]
      _ = g * h * tau * (g * h)⁻¹ := by group
  one_mem' := ⟨one_mem _, Set.mem_smul_set.mpr ⟨1, one_mem _, by simp⟩⟩
  inv_mem' := by
    rintro g ⟨hgN, hgτ⟩
    refine ⟨inv_mem hgN, ?_⟩
    obtain ⟨v, hv, hve⟩ := Set.mem_smul_set.mp hgτ
    have hgv : g⁻¹ * v * g ∈ fourGrp x₁ x₂ := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hgN) v).mp hv
    refine Set.mem_smul_set.mpr ⟨(g⁻¹ * v * g)⁻¹, inv_mem hgv, ?_⟩
    simp only [smul_eq_mul] at hve ⊢
    have h1 : (g⁻¹ * tau * g) * (g⁻¹ * v * g) = tau := by
      calc (g⁻¹ * tau * g) * (g⁻¹ * v * g) = g⁻¹ * (tau * v) * g := by group
        _ = g⁻¹ * (g * tau * g⁻¹) * g := by rw [hve]
        _ = tau := by group
    have h2 : g⁻¹ * tau * g = tau * (g⁻¹ * v * g)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact h1
    simp only [inv_inv]
    exact h2.symm

theorem w4_mem_Ktau_of_comm {g : G}
    (hgN : g ∈ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G))
    (hg : g * tau = tau * g) : g ∈ w4Ktau tau x₁ x₂ := by
  refine ⟨hgN, Set.mem_smul_set.mpr ⟨1, one_mem _, ?_⟩⟩
  simp only [smul_eq_mul, mul_one]
  rw [hg, mul_assoc, mul_inv_cancel, mul_one]

theorem w4_conj_tau_eq_sq_mul_tau {a : G} (hinv : tau * a * tau⁻¹ = a⁻¹) :
    a * tau * a⁻¹ = a ^ 2 * tau := by
  calc a * tau * a⁻¹ = a * (tau * a⁻¹ * tau⁻¹) * tau := by group
    _ = a * (tau * a * tau⁻¹)⁻¹ * tau := by
          rw [show tau * a⁻¹ * tau⁻¹ = (tau * a * tau⁻¹)⁻¹ by group]
    _ = a * (a⁻¹)⁻¹ * tau := by rw [hinv]
    _ = a ^ 2 * tau := by rw [inv_inv, pow_two]

theorem w4_x₁_x₂_mem_Ktau
    (hc : W4Ctxa t L S x₁ x₂ lam rho tau) :
    x₁ ∈ w4Ktau tau x₁ x₂ ∧ x₂ ∈ w4Ktau tau x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  obtain ⟨-, -, hx₁M, hx₂M, -, -⟩ := p0_gens_mem_M hc4
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂V : x₂ ^ 2 ∈ fourGrp x₁ x₂ := by
    rw [WreathRel.x₂_sq hc4.wreath]
    exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  refine ⟨⟨w4_mem_normalizer_V hc.normal_V hx₁M, ?_⟩, ⟨w4_mem_normalizer_V hc.normal_V hx₂M, ?_⟩⟩
  · rw [w4_conj_tau_eq_sq_mul_tau hc4.tau_x₁, ← w4_tau_comm_V hc4 hyV]
    exact w4_mul_mem_smul hyV
  · rw [w4_conj_tau_eq_sq_mul_tau hc4.tau_x₂, ← w4_tau_comm_V hc4 hx₂V]
    exact w4_mul_mem_smul hx₂V

theorem w4_CMt_le_Ktau
    (hc : W4Ctxa t L S x₁ x₂ lam rho tau) :
    ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G) ≤ w4Ktau tau x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  obtain ⟨htM, htauM, hx₁M, hx₂M, hrhoM, hlamM⟩ := p0_gens_mem_M hc4
  have hN := fun {g : G} (hg : g ∈ ctxM t tau x₁ x₂) => w4_mem_normalizer_V hc.normal_V hg
  rw [p0_CMt_eq hc4]
  refine sup_le ?_ ?_
  · rw [ctxW, hc4.l43]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · exact w4_mem_Ktau_of_comm (hN htM) (w4_t_comm_tau hc4)
    · rw [baseGrp, Subgroup.closure_le]
      intro x hx
      rcases (by simpa using hx) with rfl | rfl
      · exact (w4_x₁_x₂_mem_Ktau hc).1
      · exact (w4_x₁_x₂_mem_Ktau hc).2
  · rw [Subgroup.closure_le]
    intro x hx
    rcases (by simpa using hx) with rfl | rfl | rfl
    · exact w4_mem_Ktau_of_comm (hN htauM) rfl
    · exact w4_mem_Ktau_of_comm (hN hrhoM) hc4.tau_rho.symm
    · exact w4_mem_Ktau_of_comm (hN hlamM) hc4.tau_lam.symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

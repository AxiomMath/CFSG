module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4d3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem w4_conj_mem_closure_of_gens {T : Set G} {g : G}
    (hgen : ∀ x ∈ T, g * x * g⁻¹ ∈ Subgroup.closure T) :
    ∀ w ∈ Subgroup.closure T, g * w * g⁻¹ ∈ Subgroup.closure T := by
  intro w hw
  refine Subgroup.closure_induction (p := fun w _ => g * w * g⁻¹ ∈ Subgroup.closure T)
    ?_ ?_ ?_ ?_ hw
  · intro x hx; exact hgen x hx
  · simp
  · intro x y hx hy ihx ihy
    have he : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [he]; exact mul_mem ihx ihy
  · intro x hx ihx
    have he : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [he]; exact inv_mem ihx

theorem w4_A_comm (hc : Ctx0 t L S x₁ x₂ lam rho) {a b : G} (ha : a ∈ baseGrp x₁ x₂)
    (hb : b ∈ baseGrp x₁ x₂) : a * b = b * a := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := hc.wreath.baseGrp_eq.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : baseGrp x₁ x₂) ⟨b, hb⟩)

theorem w4_tau_conj_baseGrp (hc : Ctx4 t L S x₁ x₂ lam rho tau) {b : G}
    (hb : b ∈ baseGrp x₁ x₂) : tau * b * tau⁻¹ = b⁻¹ := by
  rw [baseGrp] at hb
  refine Subgroup.closure_induction (p := fun b _ => tau * b * tau⁻¹ = b⁻¹) ?_ ?_ ?_ ?_ hb
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]; exact hc.tau_x₁
    · rw [h]; exact hc.tau_x₂
  · simp
  · intro y z hy hz ihy ihz
    have hyz : y * z = z * y := w4_A_comm hc.toCtx0 hy hz
    calc tau * (y * z) * tau⁻¹ = (tau * y * tau⁻¹) * (tau * z * tau⁻¹) := by group
      _ = y⁻¹ * z⁻¹ := by rw [ihy, ihz]
      _ = (y * z)⁻¹ := by rw [hyz]; group
  · intro y hy ihy
    rw [show tau * y⁻¹ * tau⁻¹ = (tau * y * tau⁻¹)⁻¹ by group, ihy]

theorem w4_sq_surj (hc : Ctx0 t L S x₁ x₂ lam rho) {v : G} (hv : v ∈ fourGrp x₁ x₂) :
    ∃ a ∈ baseGrp x₁ x₂, a ^ 2 = v := by
  rw [fourGrp] at hv
  refine Subgroup.closure_induction (p := fun v _ => ∃ a ∈ baseGrp x₁ x₂, a ^ 2 = v)
    ?_ ?_ ?_ ?_ hv
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with h | h
    · exact ⟨x₁, Subgroup.subset_closure (by simp), h.symm⟩
    · exact ⟨x₁ * x₂, mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)), h.symm⟩
  · exact ⟨1, one_mem _, one_pow 2⟩
  · rintro u w - - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, Commute.mul_pow (w4_A_comm hc ha hb) 2⟩
  · rintro u - ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, inv_mem ha, inv_pow a 2⟩

theorem w4_A_le_M (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    baseGrp x₁ x₂ ≤ ctxM t tau x₁ x₂ := by
  obtain ⟨-, -, hx₁M, hx₂M, -, -⟩ := p0_gens_mem_M hc
  rw [baseGrp, Subgroup.closure_le]
  intro x hx
  rcases (by simpa using hx) with h | h
  · rw [h]; exact hx₁M
  · rw [h]; exact hx₂M

theorem w4_conj_ttau_mem
    (hc : W4Ctxc t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) :
    g * (t * tau) * g⁻¹ ∈ (t * tau) • (fourGrp x₁ x₂ : Set G) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  obtain ⟨a, ha, hae⟩ := Set.mem_smul_set.mp (w4_conj_t_mem hc.toW4Ctx0 hg)
  obtain ⟨b, hb, hbe⟩ := Set.mem_smul_set.mp (w4_conj_tau_mem hc hg)
  simp only [smul_eq_mul] at hae hbe
  refine Set.mem_smul_set.mpr ⟨a * b, mul_mem ha hb, ?_⟩
  show t * tau * (a * b) = g * (t * tau) * g⁻¹
  calc t * tau * (a * b) = t * (tau * a) * b := by group
    _ = t * (a * tau) * b := by rw [w4_tau_comm_V hc4 ha]
    _ = (t * a) * (tau * b) := by group
    _ = (g * t * g⁻¹) * (g * tau * g⁻¹) := by rw [hae, hbe]
    _ = g * (t * tau) * g⁻¹ := by group

theorem w4_tauM
    (hc : W4Ctxc t L S x₁ x₂ lam rho tau) :
    conjIn (ctxM t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact w4_conj_tau_mem hc hg
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hw
    obtain ⟨a, haA, rfl⟩ := w4_sq_surj hc4.toCtx0 hv
    refine ⟨a, w4_A_le_M hc4 haA, ?_⟩
    rw [smul_eq_mul, w4_conj_tau_eq_sq_mul_tau (w4_tau_conj_baseGrp hc4 haA)]
    exact (w4_tau_comm_V hc4 hv).symm

theorem w4_ttauM
    (hc : W4Ctxc t L S x₁ x₂ lam rho tau) :
    conjIn (ctxM t tau x₁ x₂) (t * tau) = (t * tau) • (fourGrp x₁ x₂ : Set G) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact w4_conj_ttau_mem hc hg
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hw
    obtain ⟨a, haA, rfl⟩ := w4_sq_surj hc4.toCtx0 hv
    refine ⟨a, w4_A_le_M hc4 haA, ?_⟩
    have hat : a * t = t * a :=
      S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc4.hyp (w4_baseGrp_le_L hc4.toCtx0 haA))
    rw [smul_eq_mul]
    calc a * (t * tau) * a⁻¹ = (a * t) * tau * a⁻¹ := by group
      _ = (t * a) * tau * a⁻¹ := by rw [hat]
      _ = t * (a * tau * a⁻¹) := by group
      _ = t * (a ^ 2 * tau) := by rw [w4_conj_tau_eq_sq_mul_tau (w4_tau_conj_baseGrp hc4 haA)]
      _ = t * (tau * a ^ 2) := by rw [w4_tau_comm_V hc4 hv]
      _ = (t * tau) * a ^ 2 := by group

theorem w4_normal_N
    (hc : W4Ctxc t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxN tau x₁ x₂) (ctxM t tau x₁ x₂) := by
  have hVN : fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ := (p0_V_le_N_le_X t tau x₁ x₂).1
  have hNX : ctxN tau x₁ x₂ ≤ ctxX t tau x₁ x₂ := (p0_V_le_N_le_X t tau x₁ x₂).2
  refine ⟨hNX.trans Subgroup.le_normalizer, fun g hg n hn => ?_⟩
  rw [ctxN] at hn ⊢
  refine w4_conj_mem_closure_of_gens (g := g) ?_ n hn
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h
  · obtain ⟨v, hv, hve⟩ := Set.mem_smul_set.mp (w4_conj_tau_mem hc hg)
    simp only [smul_eq_mul] at hve
    rw [h, ← hve]
    exact mul_mem (Subgroup.subset_closure (by simp)) (hVN hv)
  · rw [h]
    exact hVN (hc.normal_V.2 g hg _ (Subgroup.subset_closure (by simp)))
  · rw [h]
    exact hVN (hc.normal_V.2 g hg _ (Subgroup.subset_closure (by simp)))

theorem w4_normal_tN
    (hc : W4Ctxc t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxN (t * tau) x₁ x₂) (ctxM t tau x₁ x₂) := by
  have hVN : fourGrp x₁ x₂ ≤ ctxN (t * tau) x₁ x₂ := (p0_V_le_N_le_X t (t * tau) x₁ x₂).1
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have htauX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have hNX : ctxN (t * tau) x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
    rw [ctxN, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact mul_mem htX htauX
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [h]; exact Subgroup.subset_closure (by simp)
  refine ⟨hNX.trans Subgroup.le_normalizer, fun g hg n hn => ?_⟩
  rw [ctxN] at hn ⊢
  refine w4_conj_mem_closure_of_gens (g := g) ?_ n hn
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h
  · obtain ⟨v, hv, hve⟩ := Set.mem_smul_set.mp (w4_conj_ttau_mem hc hg)
    simp only [smul_eq_mul] at hve
    rw [h, ← hve]
    exact mul_mem (Subgroup.subset_closure (by simp)) (hVN hv)
  · rw [h]
    exact hVN (hc.normal_V.2 g hg _ (Subgroup.subset_closure (by simp)))
  · rw [h]
    exact hVN (hc.normal_V.2 g hg _ (Subgroup.subset_closure (by simp)))

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

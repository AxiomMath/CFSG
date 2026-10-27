module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3Sig
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2d2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2s

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem rho_mem_LO (ha : Ctx4A t L S x₁ x₂ lam rho tau) : rho ∈ ctxLO t tau x₁ x₂ := by
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  have hs := isSylSL34_of_Ctx4L hl
  exact M_le_LO hc hs hc.rho_mem_M

theorem lamt_mem_LO (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    lam * t ∈ ctxLO t tau x₁ x₂ := by
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  have hs := isSylSL34_of_Ctx4L hl
  exact mul_mem (M_le_LO hc hs hc.lam_mem_M) (M_le_LO hc hs (hc.O_le_M hc.t_mem_O))

theorem O_le_LO (t tau : G) (x₁ x₂ : G) : ctxO t tau x₁ x₂ ≤ ctxLO t tau x₁ x₂ :=
  Subgroup.le_normalizer

theorem O_le_ctxPL (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    ctxO t tau x₁ x₂ ≤ ctxPL t tau x₁ x₂ := by
  have hc := ha.toCtx4L.toCtx4Q
  intro x hx
  exact Subgroup.mem_inf.mpr
    ⟨O_le_LO t tau x₁ x₂ hx,
      Subgroup.mem_centralizer_iff.mpr fun u hu => (V_comm_O hc hx hu).symm⟩

theorem normal_ctxPL (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxPL t tau x₁ x₂) (ctxLO t tau x₁ x₂) := by
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  have hs := isSylSL34_of_Ctx4L hl
  refine ⟨inf_le_left, fun g hg k hk => ?_⟩
  have hk_inf : k ∈ ctxLO t tau x₁ x₂ ⊓
      centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    simpa [ctxPL] using hk
  obtain ⟨hkL, hkC⟩ := Subgroup.mem_inf.mp hk_inf
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg hkL) (inv_mem hg), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : g⁻¹ * u * g ∈ fourGrp x₁ x₂ := by
    simpa using conj_V_of_mem_LO hc hs (inv_mem hg) hu
  have hk' : (g⁻¹ * u * g) * k = k * (g⁻¹ * u * g) :=
    Subgroup.mem_centralizer_iff.mp hkC _ hu'
  calc u * (g * k * g⁻¹) = g * ((g⁻¹ * u * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * u * g)) * g⁻¹ := by rw [hk']
    _ = (g * k * g⁻¹) * u := by group

theorem rho_not_mem_ctxPL (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    rho ∉ ctxPL t tau x₁ x₂ := by
  have hc := ha.toCtx4L.toCtx4Q
  intro hrho
  have hrho_inf : rho ∈ ctxLO t tau x₁ x₂ ⊓
      centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    simpa [ctxPL] using hrho
  have hrhoC := (Subgroup.mem_inf.mp hrho_inf).2
  have hy : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hcomm : (x₁ ^ 2) * rho = rho * (x₁ ^ 2) :=
    Subgroup.mem_centralizer_iff.mp hrhoC _ hy
  have hmem : x₁ ^ 2 ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
    ⟨hc.V_le_Q hy, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  rw [hc.CQ_rho, Subgroup.mem_bot] at hmem
  exact hc.y_ne_one hmem

theorem lamt_not_mem_ctxPL (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    lam * t ∉ ctxPL t tau x₁ x₂ := by
  have hc := ha.toCtx4L.toCtx4Q
  intro hmem
  have hmem_inf : lam * t ∈ ctxLO t tau x₁ x₂ ⊓
      centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    simpa [ctxPL] using hmem
  have hmemC := (Subgroup.mem_inf.mp hmem_inf).2
  have hy : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hcomm : (x₁ ^ 2) * (lam * t) = (lam * t) * (x₁ ^ 2) :=
    Subgroup.mem_centralizer_iff.mp hmemC _ hy
  have hfix : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 := by
    rw [← hcomm]; group
  have hq := q_conj_y hc
  rw [t_comm_lam hc] at hq
  have hyz : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 := hq.symm.trans hfix
  have hz : (x₁ * x₂) ^ 2 = 1 := by
    have h : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 * 1 := by rw [hyz, mul_one]
    exact mul_left_cancel h
  exact z_ne_one hc hz

theorem lamt_sq_mem_ctxPL (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    (lam * t) * (lam * t) ∈ ctxPL t tau x₁ x₂ := by
  have hc := ha.toCtx4L.toCtx4Q
  have h1 : (lam * t) * (lam * t) = 1 := by
    rw [← t_comm_lam hc]
    exact q_mul_self hc
  rw [h1]
  exact one_mem _

theorem card_LO_of_sig (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    Nat.card (ctxLO t tau x₁ x₂) = 3 * 2 ^ 11 := by
  have hc := ha.toCtx4L.toCtx4Q
  have hker : Nat.card σ.φ.ker = Nat.card (ctxO t tau x₁ x₂) := by
    rw [σ.ker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (O_le_LO t tau x₁ x₂)).toEquiv
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hmain : 2 ^ 8 * 24 = Nat.card (ctxLO t tau x₁ x₂) := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := σ.φ) σ.surj
    rw [hker, hperm, hc.card_O] at h
    exact h
  rw [← hmain]
  norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z

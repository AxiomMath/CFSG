module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13K0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem c13K_CK_t_le
    (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {k : G}
    (hk : k ∈ ctxK t tau x₁ x₂ rho) (hkt : k * t = t * k) : k ∈ ctxM t tau x₁ x₂ := by
  have hbase_eq : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = baseGrp x₁ x₂ :=
    (c13K_lemma4_12a hc).2.2.1
  have hkC : k ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hkt
  have hkNormQ : k ∈ Subgroup.normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    hc.K_le.2.1 (hc.K_le.1 hk)
  have hkNormC : k ∈ Subgroup.normalizer ((centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hkC
  have hkNorm : k ∈ Subgroup.normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    have h := Subgroup.inf_normalizer_le_normalizer_inf
      (H := ctxQ t tau x₁ x₂ rho) (K := centralizer ({t} : Set G)) ⟨hkNormQ, hkNormC⟩
    rwa [hbase_eq] at h
  have hkmem : k ∈ invCent t ⊓
      Subgroup.normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
    ⟨hkC, hkNorm⟩
  have hcl : closure ({rho, lam, tau} : Set G) = closure ({tau, rho, lam} : Set G) := by
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hCM : ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G) =
      ctxW t x₁ x₂ ⊔ closure ({tau, rho, lam} : Set G) :=
    p0_CMt_eq hc.toCtx10.toCtx4
  rw [hc.norm_baseGrp, hcl, ← hCM] at hkmem
  exact hkmem.1

theorem c13K_CK_t_eq
    (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ctxK t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) =
      ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G) := by
  apply le_antisymm
  · intro k hk
    exact ⟨c13K_CK_t_le hc hk.1 (Subgroup.mem_centralizer_singleton_iff.mp hk.2), hk.2⟩
  · intro k hk
    exact ⟨hc.M_le_K hk.1, hk.2⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

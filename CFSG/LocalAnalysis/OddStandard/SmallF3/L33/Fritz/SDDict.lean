module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDCtxBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDH8Cent

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup Equiv CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

include ctx

theorem k_mem_centralizer : ctx.C.k ∈ centralizer ({t} : Set X) :=
  ctx.A.T_le_centralizer ctx.C.k_mem

private noncomputable def genAP : ↥(SDAutP.P ctx.M.F) :=
  ⟨MulAut.conj ctx.M.F.x, (SDPresent.genA (MulAut.conj ctx.M.F.x)
    (MulAut.conj ctx.M.F.y) ctx.M.F.k).2⟩

private noncomputable def genBP : ↥(SDAutP.P ctx.M.F) :=
  ⟨MulAut.conj ctx.M.F.y, (SDPresent.genB (MulAut.conj ctx.M.F.x)
    (MulAut.conj ctx.M.F.y) ctx.M.F.k).2⟩

private noncomputable def genCP : ↥(SDAutP.P ctx.M.F) :=
  ⟨ctx.M.F.k, (SDPresent.genC (MulAut.conj ctx.M.F.x)
    (MulAut.conj ctx.M.F.y) ctx.M.F.k).2⟩

private theorem genAP_val : (genAP ctx : MulAut ↥L) = MulAut.conj ctx.M.F.x := rfl

private theorem genBP_val : (genBP ctx : MulAut ↥L) = MulAut.conj ctx.M.F.y := rfl

private theorem genCP_val : (genCP ctx : MulAut ↥L) = ctx.M.F.k := rfl

private theorem genAP_eq :
    genAP ctx = (SDPresent.genA (MulAut.conj ctx.M.F.x) (MulAut.conj ctx.M.F.y)
      ctx.M.F.k : ↥(SDAutP.P ctx.M.F)) :=
  Subtype.ext rfl

private theorem genBP_eq :
    genBP ctx = (SDPresent.genB (MulAut.conj ctx.M.F.x) (MulAut.conj ctx.M.F.y)
      ctx.M.F.k : ↥(SDAutP.P ctx.M.F)) :=
  Subtype.ext rfl

private theorem genCP_eq :
    genCP ctx = (SDPresent.genC (MulAut.conj ctx.M.F.x) (MulAut.conj ctx.M.F.y)
      ctx.M.F.k : ↥(SDAutP.P ctx.M.F)) :=
  Subtype.ext rfl

private theorem phi_genAP :
    (SDAutP.phi ctx.M.F (genAP ctx) : Perm (ZMod 8)) = aff8 u5 1 := by
  rw [genAP_eq]
  exact SDAutP.phi_genA ctx.M.F

private theorem phi_genBP :
    (SDAutP.phi ctx.M.F (genBP ctx) : Perm (ZMod 8)) = y8 := by
  rw [genBP_eq]
  exact SDAutP.phi_genB ctx.M.F

private theorem phi_genCP :
    (SDAutP.phi ctx.M.F (genCP ctx) : Perm (ZMod 8)) = k8 := by
  rw [genCP_eq]
  exact SDAutP.phi_genC ctx.M.F

theorem actX_k : ctx.actX ctx.C.k = ctx.M.F.k := by
  have h1 : (SDAutP.phi ctx.M.F
      ⟨ctx.actX ctx.C.k, ctx.actX_mem_P ctx.C.k_mem⟩ : Perm (ZMod 8)) = k8 := by
    rw [← ctx.ψ_eq ctx.C.k_mem, ctx.C.ψ_k]
  have h3 : (⟨ctx.actX ctx.C.k, ctx.actX_mem_P ctx.C.k_mem⟩ : ↥(SDAutP.P ctx.M.F)) =
      genCP ctx := by
    apply (SDAutP.phi ctx.M.F).injective
    apply Subtype.ext
    rw [h1, phi_genCP]
  have h4 := congrArg Subtype.val h3
  rw [genCP_val] at h4
  exact h4

theorem x0_eq : ctx.S.x₀ = ((ctx.M.F.x ^ 6 : ↥L) : X) := by
  have hT : ctx.S.x₀ ∈ ctx.A.T := ctx.S.x₀_mem.1
  have hψ : ctx.A.ψ ⟨ctx.S.x₀, hT⟩ = x8 := by
    rw [← SD.ψX_of_mem (A := ctx.A) (g := ctx.S.x₀) hT, ctx.S.ψ_x₀]
  have hphi : (SDAutP.phi ctx.M.F
      ⟨ctx.actX ctx.S.x₀, ctx.actX_mem_P hT⟩ : Perm (ZMod 8)) = x8 := by
    rw [← ctx.ψ_eq hT, hψ]
  have hgen : (SDAutP.phi ctx.M.F (genAP ctx ^ 6) : Perm (ZMod 8)) = x8 := by
    rw [map_pow, Subgroup.coe_pow, phi_genAP, SD.aff8_u5_one_pow_six]
  have heq : (⟨ctx.actX ctx.S.x₀, ctx.actX_mem_P hT⟩ : ↥(SDAutP.P ctx.M.F)) =
      genAP ctx ^ 6 := by
    apply (SDAutP.phi ctx.M.F).injective
    apply Subtype.ext
    rw [hphi, hgen]
  have hact : ctx.actX ctx.S.x₀ = MulAut.conj (ctx.M.F.x ^ 6) := by
    have h4 := congrArg Subtype.val heq
    rw [Subgroup.coe_pow, genAP_val] at h4
    rw [← map_pow (MulAut.conj : ↥L →* MulAut ↥L) ctx.M.F.x 6] at h4
    exact h4
  have hL : ctx.S.x₀ ∈ L := ctx.A.R_le_L ctx.S.x₀_mem
  let l : ↥L := ⟨ctx.S.x₀, hL⟩
  have hl : (l : X) = ctx.S.x₀ := rfl
  have hconj : MulAut.conj l = MulAut.conj (ctx.M.F.x ^ 6) := by
    rw [← ctx.actX_of_mem_L l, hl, hact]
  have hl_eq : l = ctx.M.F.x ^ 6 := ctx.conj_injective hconj
  simpa [l] using congrArg Subtype.val hl_eq

theorem y0_eq : ctx.S.y₀ = ((ctx.M.F.y : ↥L) : X) := by
  have hT : ctx.S.y₀ ∈ ctx.A.T := ctx.S.y₀_mem.1
  have hψ : ctx.A.ψ ⟨ctx.S.y₀, hT⟩ = y8 := by
    rw [← SD.ψX_of_mem (A := ctx.A) (g := ctx.S.y₀) hT, ctx.S.ψ_y₀]
  have hphi : (SDAutP.phi ctx.M.F
      ⟨ctx.actX ctx.S.y₀, ctx.actX_mem_P hT⟩ : Perm (ZMod 8)) = y8 := by
    rw [← ctx.ψ_eq hT, hψ]
  have heq : (⟨ctx.actX ctx.S.y₀, ctx.actX_mem_P hT⟩ : ↥(SDAutP.P ctx.M.F)) =
      genBP ctx := by
    apply (SDAutP.phi ctx.M.F).injective
    apply Subtype.ext
    rw [hphi, phi_genBP]
  have hact : ctx.actX ctx.S.y₀ = MulAut.conj ctx.M.F.y := by
    have h4 := congrArg Subtype.val heq
    rw [genBP_val] at h4
    exact h4
  have hL : ctx.S.y₀ ∈ L := ctx.A.R_le_L ctx.S.y₀_mem
  let l : ↥L := ⟨ctx.S.y₀, hL⟩
  have hl : (l : X) = ctx.S.y₀ := rfl
  have hconj : MulAut.conj l = MulAut.conj ctx.M.F.y := by
    rw [← ctx.actX_of_mem_L l, hl, hact]
  have hl_eq : l = ctx.M.F.y := ctx.conj_injective hconj
  simpa [l] using congrArg Subtype.val hl_eq

theorem z_eq : ctx.S.z = ((ctx.M.F.x ^ 4 : ↥L) : X) := by
  change ctx.S.x₀ ^ 2 = ((ctx.M.F.x ^ 4 : ↥L) : X)
  rw [x0_eq ctx, ← Subgroup.coe_pow]
  congr 1
  calc (ctx.M.F.x ^ 6 : ↥L) ^ 2 = ctx.M.F.x ^ (6 * 2) := by rw [pow_mul]
    _ = ctx.M.F.x ^ (8 + 4) := by norm_num
    _ = ctx.M.F.x ^ 8 * ctx.M.F.x ^ 4 := by rw [pow_add]
    _ = ctx.M.F.x ^ 4 := by rw [ctx.M.F.x_pow_eight, one_mul]

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx

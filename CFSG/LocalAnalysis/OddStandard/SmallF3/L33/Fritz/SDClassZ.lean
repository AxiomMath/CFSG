module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDict

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

include ctx

private theorem x4_sq : (ctx.M.F.x ^ 4 : ↥L) ^ 2 = 1 := by
  rw [← pow_mul, show (4 : ℕ) * 2 = 8 by norm_num, ctx.M.F.x_pow_eight]

private theorem x4_ne_one : (ctx.M.F.x ^ 4 : ↥L) ≠ 1 := ctx.M.F.x_pow_four_ne_one

private theorem conj_z_set :
    {b | ∃ g ∈ centralizer ({t} : Set X), g * ctx.S.z * g⁻¹ = b} =
      (fun u : ↥L => (u : X)) '' {u : ↥L | u ^ 2 = 1 ∧ u ≠ 1} := by
  ext b
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨ctx.actX g (ctx.M.F.x ^ 4), ⟨?_, ?_⟩, ?_⟩
    · rw [← map_pow, x4_sq ctx, map_one]
    · intro h
      exact x4_ne_one ctx ((ctx.actX g).injective (by rw [h, map_one]))
    · show (↑(ctx.actX g (ctx.M.F.x ^ 4)) : X) = g * ctx.S.z * g⁻¹
      rw [ctx.z_eq, ctx.actX_apply hg (ctx.M.F.x ^ 4)]
  · rintro ⟨u, ⟨hu2, hu1⟩, rfl⟩
    obtain ⟨a, ha⟩ := isConj_iff.mp
      (ctx.M.involutions_conj (u := ctx.M.F.x ^ 4) (v := u) (x4_sq ctx) (x4_ne_one ctx)
        hu2 hu1)
    refine ⟨(a : X), ctx.L_le_centralizer a.2, ?_⟩
    rw [ctx.z_eq, ← ha]
    rfl

theorem ncard_conj_z :
    {b | ∃ g ∈ centralizer ({t} : Set X), g * ctx.S.z * g⁻¹ = b}.ncard = 117 := by
  rw [conj_z_set ctx, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [← Nat.card_coe_set_eq]
  exact ctx.M.card_involutions

theorem card_conj_z
    (_ : ∀ g ∈ centralizer ({t} : Set X), g * ctx.S.x₀ ^ 2 * g⁻¹ ≠ t * ctx.S.x₀ ^ 2) :
    {b | ∃ g ∈ centralizer ({t} : Set X), g * ctx.S.x₀ ^ 2 * g⁻¹ = b}.ncard ≡ 1 [MOD 4] := by
  have h := ctx.ncard_conj_z
  change {b | ∃ g ∈ centralizer ({t} : Set X), g * ctx.S.x₀ ^ 2 * g⁻¹ = b}.ncard = 117 at h
  rw [h]
  decide

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx

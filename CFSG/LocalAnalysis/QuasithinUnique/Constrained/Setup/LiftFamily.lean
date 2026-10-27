module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyNatural
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDeleted

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Family

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem familyCommon (ctx : FamilyCtx H T n F r Lc) : EvenSL2FamilyCommon H T r Lc where
  J_eq := offenderJ_eq ctx
  B_comm := fun _ _ hij => blockB_comm ctx hij
  B_direct := blockB_direct ctx
  B_normal := blockB_normal ctx
  B_subnormal := blockB_subnormal ctx
  L_le_B := Lc_le_blockB ctx
  perm := fun _ ht i => family_perm ctx ht i
  trans := family_trans ctx
  B_fix_C := fun _ _ hb c hc => blockB_le_centSub_C ctx hb c hc
  B_fix_I := fun _ _ hji _ hb v hv => blockB_le_centSub_I ctx hji hb v hv
  I_eq_B := blockB_I_eq ctx
  C_eq_J := C_eq_J ctx
  I_inf_C := I_inf_C ctx
  V_sum := V_sum ctx
  sum_direct := sum_direct ctx
  H_perm_I := fun _ hh i => H_perm_I ctx hh i
  H_fix_C := fun _ hh _ hc => H_fix_C ctx hh hc
  faithful_VC := fun _ hh hf => faithful_VC ctx hh hf
  weight_eq := fun _ hA => weight_eq_of_mem ctx hA
  weight_le := ctx.layer.upper_bound

theorem family_output_of_ctx (ctx : FamilyCtx H T n F r Lc) : EvenSL2FamilyOutput H T n F r Lc := by
  refine ⟨ctx.layer, familyCommon ctx, ?_⟩
  rcases global_alt ctx with hglob | hglob
  · left
    have hnat := natural_family ctx hglob
    exact ⟨hnat, fun hdel => not_natural_and_deleted ctx hnat hdel⟩
  · right
    have hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i) := by
      intro A hA i hmove
      exact (alt_dichotomy ctx hA i hmove).resolve_left fun hN => hglob i A hA hmove hN.1
    have hD := deleted_family ctx hdel
    exact ⟨hD, fun hnat => not_natural_and_deleted ctx hnat hD⟩

end Family

end CFSG.QuasithinUnique.Setup.Lift

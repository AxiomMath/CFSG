module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDelB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyPerm

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Transp

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

structure DelModel (ctx : FamilyCtx H T n F r Lc) (i : Fin r) where
  ψ : ↥(blockB H (Lc i)) ≃* Equiv.Perm (ℙ F (Fin 2 → F))
  β : ↥(commGL (Lc i) ⊤) ≃ₗ[ZMod 2] ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))
  compat : ∀ (b : ↥(blockB H (Lc i))) (u u' : ↥(commGL (Lc i) ⊤)),
    (u' : V) = (b : V ≃ₗ[ZMod 2] V) (u : V) →
      ((β u' : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2) =
        SL2Modules.permAct (ψ b)
          ((β u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2)
  onL : ∀ l : ↥(Lc i), ψ ⟨l, Lc_le_blockB ctx i l.2⟩ =
    MulAction.toPerm (thetaL (Lc i) (ctx.α i) l)
  alt : ((Lc i).subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom =
    alternatingGroup (ℙ F (Fin 2 → F))

theorem nonempty_delModel (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (i : Fin r) : Nonempty (DelModel ctx i) := by
  obtain ⟨ψ, β, hc, hL, hA⟩ := exists_deleted_model ctx hdel i
  exact ⟨⟨ψ, β, hc, hL, hA⟩⟩

variable {ctx : FamilyCtx H T n F r Lc} {i : Fin r}

omit [Finite V] in
theorem DelModel.agree (M : DelModel ctx i) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) (hmove : ⁅Lc i, A⁆ ≠ ⊥) (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5)
    (ψA : ↥(Lc i ⊔ A) →* Equiv.Perm (ℙ F (Fin 2 → F)))
    (hψAL : ∀ l : ↥(Lc i), ψA ⟨l, Subgroup.mem_sup_left l.2⟩ =
      MulAction.toPerm (thetaL (Lc i) (ctx.α i) l))
    (a : V ≃ₗ[ZMod 2] V) (ha : a ∈ A) :
    M.ψ ⟨a, le_blockB_gen hA hmove ha⟩ = ψA ⟨a, Subgroup.mem_sup_right ha⟩ := by
  have hAn : a ∈ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) :=
    (ctx.offd A hA i hmove).1.A_norm ha
  have hcomm : ∀ τ ∈ alternatingGroup (ℙ F (Fin 2 → F)),
      (ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ * M.ψ ⟨a, le_blockB_gen hA hmove ha⟩ * τ =
        τ * ((ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ * M.ψ ⟨a, le_blockB_gen hA hmove ha⟩) := by
    intro τ hτ
    rw [← M.alt] at hτ
    obtain ⟨y, hy, rfl⟩ := hτ
    have hy' : (y : V ≃ₗ[ZMod 2] V) ∈ Lc i := hy
    have hl' : a * (y : V ≃ₗ[ZMod 2] V) * a⁻¹ ∈ Lc i :=
      (Subgroup.mem_normalizer_iff.1 hAn _).1 hy'
    have e0 : M.ψ y = MulAction.toPerm (thetaL (Lc i) (ctx.α i) ⟨y, hy'⟩) := M.onL ⟨y, hy'⟩
    have e1 : M.ψ ⟨a, le_blockB_gen hA hmove ha⟩ * M.ψ y *
        (M.ψ ⟨a, le_blockB_gen hA hmove ha⟩)⁻¹ =
        MulAction.toPerm (thetaL (Lc i) (ctx.α i) ⟨_, hl'⟩) := by
      have key : (⟨a, le_blockB_gen hA hmove ha⟩ * y * ⟨a, le_blockB_gen hA hmove ha⟩⁻¹ :
          ↥(blockB H (Lc i))) = ⟨(⟨_, hl'⟩ : ↥(Lc i)), Lc_le_blockB ctx i hl'⟩ := Subtype.ext rfl
      rw [← map_inv, ← map_mul, ← map_mul, key]
      exact M.onL ⟨_, hl'⟩
    have e2 : ψA ⟨a, Subgroup.mem_sup_right ha⟩ * ψA ⟨y, Subgroup.mem_sup_left hy'⟩ *
        (ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ =
        MulAction.toPerm (thetaL (Lc i) (ctx.α i) ⟨_, hl'⟩) := by
      have key : (⟨a, Subgroup.mem_sup_right ha⟩ * ⟨y, Subgroup.mem_sup_left hy'⟩ *
          ⟨a, Subgroup.mem_sup_right ha⟩⁻¹ : ↥(Lc i ⊔ A)) =
          ⟨(⟨_, hl'⟩ : ↥(Lc i)), Subgroup.mem_sup_left (⟨_, hl'⟩ : ↥(Lc i)).2⟩ := Subtype.ext rfl
      rw [← map_inv, ← map_mul, ← map_mul, key]
      exact hψAL ⟨_, hl'⟩
    have e3 : ψA ⟨y, Subgroup.mem_sup_left hy'⟩ = M.ψ y := by
      rw [e0]
      exact hψAL ⟨y, hy'⟩
    rw [e3] at e2
    have hh : M.ψ ⟨a, le_blockB_gen hA hmove ha⟩ * M.ψ y *
        (M.ψ ⟨a, le_blockB_gen hA hmove ha⟩)⁻¹ =
        ψA ⟨a, Subgroup.mem_sup_right ha⟩ * M.ψ y * (ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ :=
      e1.trans e2.symm
    show (ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ * M.ψ ⟨a, le_blockB_gen hA hmove ha⟩ * M.ψ y =
      M.ψ y * ((ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ * M.ψ ⟨a, le_blockB_gen hA hmove ha⟩)
    calc (ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ * M.ψ ⟨a, le_blockB_gen hA hmove ha⟩ * M.ψ y
        = (ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ * (M.ψ ⟨a, le_blockB_gen hA hmove ha⟩ * M.ψ y *
            (M.ψ ⟨a, le_blockB_gen hA hmove ha⟩)⁻¹) * M.ψ ⟨a, le_blockB_gen hA hmove ha⟩ := by
          group
      _ = (ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ * (ψA ⟨a, Subgroup.mem_sup_right ha⟩ * M.ψ y *
            (ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹) * M.ψ ⟨a, le_blockB_gen hA hmove ha⟩ := by
          rw [hh]
      _ = M.ψ y * ((ψA ⟨a, Subgroup.mem_sup_right ha⟩)⁻¹ * M.ψ ⟨a, le_blockB_gen hA hmove ha⟩) := by
          group
  have h1 := perm_eq_one_of_commute_alternating h5 hcomm
  exact (inv_mul_eq_one.1 h1).symm

omit [Finite V] in
theorem DelModel.map_agree (M : DelModel ctx i) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) (hmove : ⁅Lc i, A⁆ ≠ ⊥) (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5)
    (ψA : ↥(Lc i ⊔ A) →* Equiv.Perm (ℙ F (Fin 2 → F)))
    (hψAL : ∀ l : ↥(Lc i), ψA ⟨l, Subgroup.mem_sup_left l.2⟩ =
      MulAction.toPerm (thetaL (Lc i) (ctx.α i) l)) :
    (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom = (A.subgroupOf (Lc i ⊔ A)).map ψA := by
  ext σ
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : (b : V ≃ₗ[ZMod 2] V) ∈ A := hb
    exact ⟨⟨b, Subgroup.mem_sup_right hb'⟩, hb', (M.agree hA hmove h5 ψA hψAL b hb').symm⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : V ≃ₗ[ZMod 2] V) ∈ A := hy
    exact ⟨⟨y, le_blockB_gen hA hmove hy'⟩, hy', M.agree hA hmove h5 ψA hψAL y hy'⟩

end Transp

end CFSG.QuasithinUnique.Setup.Lift

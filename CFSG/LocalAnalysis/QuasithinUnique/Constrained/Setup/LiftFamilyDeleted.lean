module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDelE

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

theorem mem_iSup_exists_sum {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Fintype ι] [DecidableEq ι] (p : ι → Submodule R M) {v : M} (hv : v ∈ ⨆ i, p i) :
    ∃ x : ι → M, (∀ i, x i ∈ p i) ∧ v = ∑ i, x i := by
  refine Submodule.iSup_induction p
    (motive := fun v => ∃ x : ι → M, (∀ i, x i ∈ p i) ∧ v = ∑ i, x i) hv ?_ ?_ ?_
  · intro i v hv
    refine ⟨Pi.single i v, fun j => ?_, ?_⟩
    · by_cases hji : j = i
      · subst hji
        simpa using hv
      · simp [Pi.single_eq_of_ne hji]
    · simp [Finset.sum_pi_single']
  · exact ⟨0, fun i => (p i).zero_mem, by simp⟩
  · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, fun i => (p i).add_mem (hx i) (hy i), by simp [Finset.sum_add_distrib]⟩

section Deleted

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem deleted_family (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i)) :
    DeletedFamily H n r Lc := by
  classical
  have hmov : ∀ i, ∃ A, IsMinOffender H A ∧ ⁅Lc i, A⁆ = Lc i := ctx.layer.moving
  have hmove : ∀ i A, ⁅Lc i, A⁆ = Lc i → ⁅Lc i, A⁆ ≠ ⊥ := fun i A h => by
    rw [h]
    exact ctx.hLc.ne_bot i
  have hn2 : n = 2 := by
    obtain ⟨A, hA, hLA⟩ := hmov ⟨0, ctx.layer.r_pos⟩
    exact (hdel A hA _ (hmove _ _ hLA)).1
  have h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5 := by
    rw [card_projectiveLine, ctx.hF, hn2]
    norm_num
  have hZ : ∀ i, commGL (Lc i) ⊤ ⊓ fixGL (Lc i) = ⊥ := by
    intro i
    obtain ⟨A, hA, hLA⟩ := hmov i
    exact (hdel A hA i (hmove _ _ hLA)).2.1
  refine ⟨hn2, hZ, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨M⟩ := nonempty_delModel ctx hdel i
    obtain ⟨A₀, hA₀, hLA₀⟩ := hmov i
    apply le_antisymm
    · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
      have hxy : ⁅x, y⁆ ∈ blockB H (Lc i) := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
      refine (M.mem_iff_image M.alt ⟨⁅x, y⁆, hxy⟩).2 ?_
      have hh : (⟨⁅x, y⁆, hxy⟩ : ↥(blockB H (Lc i))) =
          ⁅(⟨x, hx⟩ : ↥(blockB H (Lc i))), ⟨y, hy⟩⁆ := rfl
      rw [hh, map_commutatorElement]
      exact commutatorElement_mem_alternatingGroup _ _
    · calc Lc i = ⁅Lc i, A₀⁆ := hLA₀.symm
        _ ≤ ⁅blockB H (Lc i), blockB H (Lc i)⁆ :=
          Subgroup.commutator_mono (Lc_le_blockB ctx i) (le_blockB_gen hA₀ (hmove _ _ hLA₀))
  · rw [eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    obtain ⟨x, hx, rfl⟩ := mem_iSup_exists_sum (fun i => commGL (Lc i) ⊤) hv1
    have hxz : ∀ j, x j = 0 := by
      intro j
      have h1 : x j ∈ fixGL (Lc j) := sum_direct ctx x hx hv2 j
      have h2 : x j ∈ commGL (Lc j) ⊤ ⊓ fixGL (Lc j) := ⟨hx j, h1⟩
      rw [hZ j] at h2
      exact (Submodule.mem_bot _).1 h2
    simp [hxz]
  · intro i
    obtain ⟨M⟩ := nonempty_delModel ctx hdel i
    refine ⟨ℙ F (Fin 2 → F), inferInstance, inferInstance, h5, M.ψ, M.β, M.compat, M.alt, ?_⟩
    intro A
    constructor
    · rintro ⟨hA, hmv⟩
      obtain ⟨x, y, hxy, h⟩ := M.single_transposition hdel hA hmv h5
      exact ⟨x, y, hxy, le_blockB_gen hA hmv, h⟩
    · rintro ⟨x, y, hxy, hAB, h⟩
      exact M.isMinOffender_of_transposition hdel h5 hxy hAB h

end Deleted

end CFSG.QuasithinUnique.Setup.Lift

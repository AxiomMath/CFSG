module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderDelClass
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamily

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Defs

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

structure EvenSL2OffenderOutput (H T : Subgroup (V ≃ₗ[ZMod 2] V)) (n : ℕ) (F : Type) [Field F]
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] (r : ℕ)
    (Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  family : EvenSL2FamilyOutput H T n F r Lc
  offender_iff : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), IsOffender H E ↔
    ∃ s : Finset (Subgroup (V ≃ₗ[ZMod 2] V)), s.Nonempty ∧ (∀ A ∈ s, IsMinOffender H A) ∧
      IsInternalProduct E s
  natural : NaturalFamily H F r Lc → ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), IsOffender H E ↔
    ∃ (I : Finset (Fin r)) (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)), I.Nonempty ∧
      (∀ i ∈ I, IsSylowTwoOf (U i) (Lc i)) ∧ E = ⨆ i ∈ I, U i
  deleted : DeletedFamily H n r Lc →
    ∃ (ψ : ∀ i, ↥(blockB H (Lc i)) ≃* Equiv.Perm (ℙ F (Fin 2 → F)))
      (β : ∀ i, ↥(commGL (Lc i) ⊤) ≃ₗ[ZMod 2] ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))),
      Fintype.card (ℙ F (Fin 2 → F)) = 5 ∧
      (∀ i, (∀ (b : ↥(blockB H (Lc i))) (u u' : ↥(commGL (Lc i) ⊤)),
          (u' : V) = (b : V ≃ₗ[ZMod 2] V) (u : V) →
            ((β i u' : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
                ℙ F (Fin 2 → F) → ZMod 2) =
              SL2Modules.permAct (ψ i b)
                ((β i u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
                  ℙ F (Fin 2 → F) → ZMod 2)) ∧
        ((Lc i).subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom =
          alternatingGroup (ℙ F (Fin 2 → F)) ∧
        ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), (IsMinOffender H A ∧ ⁅Lc i, A⁆ ≠ ⊥) ↔
          ∃ x y : ℙ F (Fin 2 → F), x ≠ y ∧ A ≤ blockB H (Lc i) ∧
            (A.subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom =
              Subgroup.closure {Equiv.swap x y}) ∧
      ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), IsOffender H E ↔
        ∃ (I : Finset (Fin r)) (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)), I.Nonempty ∧
          (∀ i ∈ I, IsTranspGroup (blockB H (Lc i)) (U i) (ψ i)) ∧ E = ⨆ i ∈ I, U i
  weight_eq : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), IsOffender H E →
    weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E = Nat.card V ∧ E ≤ offenderJ H
  J_eq : offenderJ H = ⨆ (E : Subgroup (V ≃ₗ[ZMod 2] V)) (_ : IsOffender H E), E

end Defs

section Main

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem even_SL2_whole_action_offenders
    {H T M E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (V ≃ₗ[ZMod 2] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N →
      N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[ZMod 2] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E)
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    {Lstar : Subgroup (V ≃ₗ[ZMod 2] V)} (hLstar : IsComponentIn Lstar H)
    (α : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* SL(2, F))
    {r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (hLc : IsCompListIn H r Lc) :
    EvenSL2OffenderOutput H T n F r Lc := by
  classical
  have layer := even_SL2_component_layer hns hO2 hT hTn hTM hMH hmax hEH hEne hEel hEoff hn hF
    hLstar α hLc
  let ctx : FamilyCtx H T n F r Lc := familyCtx_of_layer hn hF hLc layer
  have fam := family_output_of_ctx ctx
  have hweight : ∀ E', IsOffender H E' →
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E' = Nat.card V := fun E' hE' =>
    le_antisymm (ctx.layer.upper_bound E' hE'.1 hE'.2.1 hE'.2.2.1) hE'.2.2.2
  have hJ : ∀ (hprod : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V), IsOffender H E' →
      ∃ s : Finset (Subgroup (V ≃ₗ[ZMod 2] V)), s.Nonempty ∧ (∀ A ∈ s, IsMinOffender H A) ∧
        IsInternalProduct E' s),
      (∀ E' : Subgroup (V ≃ₗ[ZMod 2] V), IsOffender H E' → E' ≤ offenderJ H) ∧
        offenderJ H = ⨆ (E' : Subgroup (V ≃ₗ[ZMod 2] V)) (_ : IsOffender H E'), E' := by
    intro hprod
    have hle : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V), IsOffender H E' → E' ≤ offenderJ H := by
      intro E' hE'
      obtain ⟨s, -, hs, -, rfl, -⟩ := hprod E' hE'
      exact Finset.sup_le fun A hA => le_offenderJ (hs A hA)
    refine ⟨hle, le_antisymm ?_ (iSup₂_le fun E' hE' => hle E' hE')⟩
    exact iSup₂_le fun A hA => le_iSup₂_of_le A (IsMinOffender.isOffender hA) le_rfl
  rcases global_alt ctx with hglob | hglob
  · have hnat := natural_family ctx hglob
    have hprod := natural_internal_product_iff ctx hglob
    obtain ⟨hle, hJeq⟩ := hJ fun E' hE' => (hprod E').1 hE'
    exact ⟨fam, hprod, fun _ => natural_offender_iff ctx hglob,
      fun hdel => (not_natural_and_deleted ctx hnat hdel).elim,
      fun E' hE' => ⟨hweight E' hE', hle E' hE'⟩, hJeq⟩
  · have hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i) :=
      fun A hA i hmove => (alt_dichotomy ctx hA i hmove).resolve_left fun hN =>
        hglob i A hA hmove hN.1
    have h5 := card_five_of_deleted ctx hdel
    have hprod := deleted_internal_product_iff ctx hdel
    obtain ⟨hle, hJeq⟩ := hJ fun E' hE' => (hprod E').1 hE'
    exact ⟨fam, hprod,
      fun hnat => (not_natural_and_deleted ctx hnat (deleted_family ctx hdel)).elim,
      fun _ => ⟨fun i => (delModelOf ctx hdel i).ψ, fun i => (delModelOf ctx hdel i).β, h5,
        fun i => ⟨(delModelOf ctx hdel i).compat, (delModelOf ctx hdel i).alt,
          (delModelOf ctx hdel i).pmem_iff hdel h5⟩, deleted_offender_iff ctx hdel⟩,
      fun E' hE' => ⟨hweight E' hE', hle E' hE'⟩, hJeq⟩

end Main

end CFSG.QuasithinUnique.Setup.Lift

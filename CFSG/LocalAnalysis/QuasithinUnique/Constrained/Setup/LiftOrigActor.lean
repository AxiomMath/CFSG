module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMax
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorLayer

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Family
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization

section Transport

variable {A A' : Type} [Group A] [Group A']

theorem isCompListIn_map (ψ : A ≃* A') {H : Subgroup A} {r : ℕ} {L : Fin r → Subgroup A}
    (h : IsCompList H r L) :
    IsCompListIn (H.map ψ.toMonoidHom) r (fun i => (L i).map ψ.toMonoidHom) where
  injective := fun i j hij => h.injective (Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective hij)
  isComp := fun i => (isComponentIn_map_iff ψ).2 ((isComp_iff _ _).1 (h.isComp i))
  complete := fun D hD => by
    have e1 : (D.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = D := by
      rw [Subgroup.map_map]
      have : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id A' :=
        MonoidHom.ext ψ.apply_symm_apply
      rw [this, Subgroup.map_id]
    have hD' : IsComponentIn ((D.map ψ.symm.toMonoidHom).map ψ.toMonoidHom)
        (H.map ψ.toMonoidHom) := by
      rw [e1]
      exact hD
    obtain ⟨i, hi⟩ := h.complete (D.map ψ.symm.toMonoidHom)
      ((isComp_iff _ _).2 ((isComponentIn_map_iff ψ).1 hD'))
    exact ⟨i, by rw [hi, e1]⟩

theorem not_isSolvable_map (ψ : A ≃* A') {H : Subgroup A} (h : ¬ Group.IsSolvable ↥H) :
    ¬ Group.IsSolvable ↥(H.map ψ.toMonoidHom) := fun _hs =>
  h (Group.isSolvable_of_isSolvable_injective (f := (mapEquiv ψ H).toMonoidHom)
    (mapEquiv ψ H).injective)

@[expose] noncomputable def quotientCenterMap (ψ : A ≃* A') (D : Subgroup A) :
    (↥(D.map ψ.toMonoidHom) ⧸ Subgroup.center ↥(D.map ψ.toMonoidHom)) ≃*
      (↥D ⧸ Subgroup.center ↥D) :=
  QuotientGroup.congr _ _ (mapEquiv ψ D).symm (Subgroup.map_center_eq (mapEquiv ψ D).symm)

end Transport

section Main

structure FFCore (V : Type) [CommGroup V] (H T M E : Subgroup (MulAut V)) : Prop where
  o2_trivial : ∀ N : Subgroup (MulAut V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥
  sylow : IsSylowTwoOf T H
  not_normal : ¬ (T.subgroupOf H).Normal
  max : T ≤ M ∧ M < H ∧ ∀ X : Subgroup (MulAut V), T ≤ X → X < H → X ≤ M
  offender : E ≤ H ∧ E ≠ ⊥ ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
    Nat.card V ≤ Nat.card ↥E * Nat.card ↥(fixV E)

theorem even_SL2_actor_max_output_of_model
    {V : Type} [CommGroup V] [Finite V] {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (θ : V ≃* Multiplicative W)
    {H T M E : Subgroup (MulAut V)} (hFF : FFCore V H T M E)
    (hns : ¬ Group.IsSolvable ↥H) {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    {D : Subgroup (MulAut V)} (hD : IsComp D H) (α : CQ D ≃* SL(2, F))
    {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)} (hLc : IsCompList H r Lc) :
    EvenSL2MaxOutput (H.map (binPsi θ).toMonoidHom) (T.map (binPsi θ).toMonoidHom)
        (M.map (binPsi θ).toMonoidHom) n F r (fun i => (Lc i).map (binPsi θ).toMonoidHom) ∧
      IsSylowTwoOf (T.map (binPsi θ).toMonoidHom) (H.map (binPsi θ).toMonoidHom) ∧
      ∀ E' : Subgroup (MulAut V), E' ≤ H → E' ≠ ⊥ → IsElemAbelian2 E' →
        Nat.card ↥E' * Nat.card ↥(fixV E') ≤ Nat.card V := by
  classical
  obtain ⟨ho2', hsyl', hnn', ⟨hTM', hMH', hmax'⟩, hEH', hEne', hEel', hEoff'⟩ :=
    map_hypotheses θ hFF.o2_trivial hFF.sylow hFF.not_normal hFF.max hFF.offender
  have hout := even_SL2_maximal_subgroup_intersections (not_isSolvable_map (binPsi θ) hns) ho2'
    hsyl' hnn' hTM' hMH' hmax' hEH' hEne' hEel' hEoff' hn hF
    ((isComponentIn_map_iff (binPsi θ)).2 ((isComp_iff D H).1 hD))
    ((quotientCenterMap (binPsi θ) D).trans α) (isCompListIn_map (binPsi θ) hLc)
  refine ⟨hout, hsyl', fun E' hE'H hE'ne hE'el => ?_⟩
  have h1 := hout.offenders.family.common.weight_le (E'.map (binPsi θ).toMonoidHom)
    (Subgroup.map_mono hE'H) (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective E' (binPsi θ).injective])
    ((isElemAbelian2_iff_map θ E').1 hE'el)
  rwa [weight_map θ E', ← natCard_eq θ] at h1

theorem even_SL2_actor_max_output
    {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {H T M E : Subgroup (MulAut V)} (hFF : FFCore V H T M E)
    (hns : ¬ Group.IsSolvable ↥H) {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    {D : Subgroup (MulAut V)} (hD : IsComp D H) (α : CQ D ≃* SL(2, F))
    {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)} (hLc : IsCompList H r Lc) :
    (∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (θ : V ≃* Multiplicative W),
      EvenSL2MaxOutput (H.map (binPsi θ).toMonoidHom) (T.map (binPsi θ).toMonoidHom)
        (M.map (binPsi θ).toMonoidHom) n F r (fun i => (Lc i).map (binPsi θ).toMonoidHom)) ∧
    ∀ E' : Subgroup (MulAut V), E' ≤ H → E' ≠ ⊥ → IsElemAbelian2 E' →
      Nat.card ↥E' * Nat.card ↥(fixV E') ≤ Nat.card V := by
  classical
  obtain ⟨W, hW1, hW2, hW3, ⟨θ⟩⟩ := exists_binModel_of_binary hV
  obtain ⟨hout, -, hle⟩ := even_SL2_actor_max_output_of_model θ hFF hns hn hF hD α hLc
  exact ⟨⟨W, hW1, hW2, hW3, θ, hout⟩, hle⟩

end Main

end CFSG.QuasithinUnique.Setup.Lift

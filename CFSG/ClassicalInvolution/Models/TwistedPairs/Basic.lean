module

public import CFSG.ClassicalInvolution.WeakCT.AutExtend

public section

namespace CFSG.ClassicalInvolution.Models.TwistedPairs

open CFSG.ClassicalInvolution.WeakCT (torusHom diagConj2)
open scoped MatrixGroups

structure TwistedB2Model (F E : Type) [Field F] [Field E] (G : Type) [Group G] where
  lb : SL(2, F) →* G
  sb : SL(2, E) →* G
  nu : Eˣ → Fˣ
  mu : Fˣ → Eˣ
  conj_sl : ∀ (t : Eˣ) (A : SL(2, F)),
    sb (torusHom E t) * lb A * (sb (torusHom E t))⁻¹ = lb (diagConj2 (nu t) 1 A)
  conj_ls : ∀ (s : Fˣ) (B : SL(2, E)),
    lb (torusHom F s) * sb B * (lb (torusHom F s))⁻¹ = sb (diagConj2 (mu s) 1 B)

variable {F E : Type} [Field F] [Field E] {G : Type} [Group G]

@[expose] def TwistedB2Model.swap (P : TwistedB2Model F E G) : TwistedB2Model E F G where
  lb := P.sb
  sb := P.lb
  nu := P.mu
  mu := P.nu
  conj_sl := P.conj_ls
  conj_ls := P.conj_sl

@[expose] def TwistedB2Model.StandardPair (P : TwistedB2Model F E G) {X : Type} [Group X]
    (W U V : Subgroup X) : Prop :=
  ∃ θ : G →* X, θ.range = W ∧ θ.ker ≤ Subgroup.center G ∧
    Function.Injective (θ.comp P.lb) ∧ Function.Injective (θ.comp P.sb) ∧
    P.lb.range.map θ = U ∧ P.sb.range.map θ = V

theorem TwistedB2Model.StandardPair.map {P : TwistedB2Model F E G} {X Y : Type} [Group X]
    [Group Y] {W U V : Subgroup X} (h : P.StandardPair W U V) (φ : X →* Y)
    (hφ : Function.Injective φ) : P.StandardPair (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, hrange, hker, hl, hs, hU, hV⟩ := h
  refine ⟨φ.comp θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rwa [MonoidHom.ker_comp_of_injective θ φ hφ]
  · exact hφ.comp hl
  · exact hφ.comp hs
  · rw [← Subgroup.map_map, hU]
  · rw [← Subgroup.map_map, hV]

theorem TwistedB2Model.StandardPair.of_iso {G' : Type} [Group G'] {P : TwistedB2Model F E G}
    {P' : TwistedB2Model F E G'} (φ : G ≃* G') (hl : φ.toMonoidHom.comp P.lb = P'.lb)
    (hs : φ.toMonoidHom.comp P.sb = P'.sb) {X : Type} [Group X] {W U V : Subgroup X}
    (h : P.StandardPair W U V) : P'.StandardPair W U V := by
  obtain ⟨θ, hrange, hker, hl', hs', hU, hV⟩ := h
  have hcomp : ∀ f : SL(2, F) →* G, ∀ f' : SL(2, F) →* G', φ.toMonoidHom.comp f = f' →
      (θ.comp φ.symm.toMonoidHom).comp f' = θ.comp f := by
    intro f f' h
    rw [← h]
    refine MonoidHom.ext fun x => ?_
    simp
  have hcomp' : ∀ f : SL(2, E) →* G, ∀ f' : SL(2, E) →* G', φ.toMonoidHom.comp f = f' →
      (θ.comp φ.symm.toMonoidHom).comp f' = θ.comp f := by
    intro f f' h
    rw [← h]
    refine MonoidHom.ext fun x => ?_
    simp
  refine ⟨θ.comp φ.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 φ.symm.surjective, Subgroup.map_top]
    exact hrange
  · intro x hx
    have h1 : φ.symm x ∈ θ.ker := hx
    have h2 : φ.symm x ∈ Subgroup.center G := hker h1
    exact (MulEquivClass.apply_mem_center_iff φ.symm).1 h2
  · rw [hcomp _ _ hl]
    exact hl'
  · rw [hcomp' _ _ hs]
    exact hs'
  · rw [← MonoidHom.range_comp, hcomp _ _ hl, MonoidHom.range_comp]
    exact hU
  · rw [← MonoidHom.range_comp, hcomp' _ _ hs, MonoidHom.range_comp]
    exact hV

end CFSG.ClassicalInvolution.Models.TwistedPairs

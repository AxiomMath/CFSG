module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderOthers

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6
  CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Basic

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem commGL_conjSub (L : Subgroup (V ≃ₗ[ZMod 2] V)) (t : V ≃ₗ[ZMod 2] V) :
    commGL (conjSub t L) ⊤ = (commGL L ⊤).map (t : V →ₗ[ZMod 2] V) := by
  apply le_antisymm
  · rw [commSub_le_iff]
    intro b hb u _
    have hl : t⁻¹ * b * t ∈ L := mem_conjSub.1 hb
    refine ⟨(t⁻¹ * b * t) (t⁻¹ u) - t⁻¹ u, mem_commSub_of hl Submodule.mem_top, ?_⟩
    show t ((t⁻¹ * b * t) (t⁻¹ u) - t⁻¹ u) = (MonoidHom.id (V ≃ₗ[ZMod 2] V)) b u - u
    simp only [LinearEquiv.mul_apply, map_sub, MonoidHom.id_apply]
    rw [show t (t⁻¹ (b (t (t⁻¹ u)))) = b (t (t⁻¹ u)) from by simp, show t (t⁻¹ u) = u from by simp]
  · rw [Submodule.map_le_iff_le_comap, commSub_le_iff]
    intro l hl u hu
    have hb : t * l * t⁻¹ ∈ conjSub t L := mem_conjSub.2 (by simpa [mul_assoc] using hl)
    have hu' : (t u : V) ∈ (⊤ : Submodule (ZMod 2) V) := Submodule.mem_top
    have h1 := mem_commSub_of (ρ := MonoidHom.id (V ≃ₗ[ZMod 2] V)) hb hu'
    rw [Submodule.mem_comap]
    have e : (t : V →ₗ[ZMod 2] V) ((MonoidHom.id (V ≃ₗ[ZMod 2] V)) l u - u) =
        (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (t * l * t⁻¹) (t u) - t u := by
      simp [LinearEquiv.mul_apply]
    rw [e]
    exact h1

theorem blockB_conj {H L L' : Subgroup (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ H)
    (hL : conjSub t L = L') : conjSub t (blockB H L) = blockB H L' := by
  have key : ∀ {L L' : Subgroup (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V}, t ∈ H → conjSub t L = L' →
      conjSub t (blockB H L) ≤ blockB H L' := by
    intro L L' t ht hL
    unfold blockB
    rw [OrderIso.map_iSup]
    refine iSup_le fun A => ?_
    rw [OrderIso.map_iSup]
    refine iSup_le fun hA => ?_
    refine le_iSup₂_of_le (conjSub t A) ⟨hA.1.conj ht, ?_⟩ le_rfl
    intro hbot
    apply hA.2
    have h1 : ⁅conjSub t L, conjSub t A⁆ = conjSub t ⁅L, A⁆ := by
      show ⁅L.map (MulAut.conj t).toMonoidHom, A.map (MulAut.conj t).toMonoidHom⁆ =
        ⁅L, A⁆.map (MulAut.conj t).toMonoidHom
      rw [Subgroup.map_commutator]
    rw [← hL, h1] at hbot
    exact (conjSub t).injective (hbot.trans (conjSub t).map_bot.symm)
  apply le_antisymm (key ht hL)
  have h2 : conjSub t⁻¹ L' = L := by rw [← hL, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have := key (H.inv_mem ht) h2
  have h3 := (conjSub t).monotone this
  rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at h3

theorem le_blockB {H L A : Subgroup (V ≃ₗ[ZMod 2] V)} (hLH : L ≤ H) (hA : IsMinOffender H A)
    (hLA : ⁅L, A⁆ = L) (hL : L ≠ ⊥) : L ≤ blockB H L := by
  have hconj : ∀ l ∈ L, conjSub l A ≤ blockB H L := by
    intro l hl
    refine le_iSup₂_of_le (conjSub l A) ⟨hA.conj (hLH hl), ?_⟩ le_rfl
    intro hbot
    apply hL
    have h1 : ⁅L, conjSub l A⁆ = conjSub l ⁅L, A⁆ := by
      have : conjSub l L = L := conjSub_eq_self (Subgroup.le_normalizer hl)
      conv_lhs => rw [← this]
      show ⁅L.map (MulAut.conj l).toMonoidHom, A.map (MulAut.conj l).toMonoidHom⁆ =
        ⁅L, A⁆.map (MulAut.conj l).toMonoidHom
      rw [Subgroup.map_commutator]
    rw [h1, hLA, conjSub_eq_self (Subgroup.le_normalizer hl)] at hbot
    exact hbot
  have hAB : A ≤ blockB H L := by
    refine le_iSup₂_of_le A ⟨hA, ?_⟩ le_rfl
    intro hbot
    exact hL (hLA.symm.trans hbot)
  have hcomm : ⁅L, A⁆ ≤ blockB H L := by
    refine Subgroup.commutator_le.2 fun l hl a ha => ?_
    have h1 : l * a * l⁻¹ ∈ blockB H L :=
      hconj l hl (mem_conjSub.2 (by simpa [mul_assoc] using ha))
    have h2 : a ∈ blockB H L := hAB ha
    have : ⁅l, a⁆ = (l * a * l⁻¹) * a⁻¹ := by rw [commutatorElement_def]
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
  rwa [hLA] at hcomm

end Basic

section Context

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

structure FamilyCtx (H T : Subgroup (V ≃ₗ[ZMod 2] V)) (n : ℕ) (F : Type) [Field F] [Fintype F]
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] (r : ℕ)
    (Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) where
  hn : 2 ≤ n
  hF : Fintype.card F = 2 ^ n
  hLc : IsCompListIn H r Lc
  layer : EvenSL2LayerOutput H T r F Lc
  α : ∀ i, (↥(Lc i) ⧸ Subgroup.center ↥(Lc i)) ≃* SL(2, F)
  offd : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ →
    ComponentOffenderOutput (Lc i) A n (α i) (commGL (Lc i) ⊤) ∧
    ∀ C : Subgroup (V ≃ₗ[ZMod 2] V), IsComponentIn C H → C ≠ Lc i →
      (∀ c ∈ C, ∀ w ∈ commGL (Lc i) ⊤, c w = w) ∧ ∀ c ∈ C, ∀ a ∈ A, c * a = a * c

noncomputable def familyCtx_of_layer
    [Finite V] {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] {r : ℕ}
    {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (hLc : IsCompListIn H r Lc)
    (layer : EvenSL2LayerOutput H T r F Lc) : FamilyCtx H T n F r Lc :=
  let α : ∀ i, (↥(Lc i) ⧸ Subgroup.center ↥(Lc i)) ≃* SL(2, F) := fun i =>
    ((QuotientGroup.quotientMulEquivOfEq (layer.center_trivial i)).trans
      QuotientGroup.quotientBot).trans (layer.iso i).some
  { hn := hn
    hF := hF
    hLc := hLc
    layer := layer
    α := α
    offd := fun _ hA i hmove =>
      minimal_even_SL2_component_offender (hLc.isComp i) hn hF (α i) hA.1 hA.2.2.1 hA.2.1
        hA.2.2.2.1 hA.2.2.2.2 hmove }

end Context

end CFSG.QuasithinUnique.Setup.Lift

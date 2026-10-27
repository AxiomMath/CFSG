module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Split
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual CFSG.Open
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Frame

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem exists_frame_mu (h : A2Core σ d q) (μ : Kˣ) (hm : (d : K) * σ (μ : K) = μ) :
    ∃ ψ : SL(3, fixedField σ.toRingHom) →* adjointGroup d4 K,
        (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c) =
          fP1 σ.toRingHom h.cube_apply (c : K)) ∧
        (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c) =
          fP2 σ.toRingHom h.cube_apply μ (c : K)) ∧
        (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c) =
          fP3 σ.toRingHom h.cube_apply μ (c : K)) ∧
        (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c) =
          fM1 σ.toRingHom h.cube_apply (c : K)) ∧
        (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c) =
          fM2 σ.toRingHom h.cube_apply μ (c : K)) ∧
        (∀ c, ψ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c) =
          fM3 σ.toRingHom h.cube_apply μ (c : K)) := by
  have H := frameHyp_of_core h hm
  have hσ := h.cube_apply
  set F := fixedField σ.toRingHom with hF
  have hfix : ∀ c : F, σ.toRingHom (c : K) = c := fun c => c.2
  exact exists_hom_sl3_of_frame_of_eq (F := F) (G := adjointGroup d4 K)
    (fun c => fP1 σ.toRingHom hσ (c : K)) (fun c => fP2 σ.toRingHom hσ μ (c : K))
    (fun c => fP3 σ.toRingHom hσ μ (c : K)) (fun c => fM1 σ.toRingHom hσ (c : K))
    (fun c => fM2 σ.toRingHom hσ μ (c : K)) (fun c => fM3 σ.toRingHom hσ μ (c : K))
    (theta1 σ.toRingHom hσ F) (theta2 σ.toRingHom hσ μ F) (wSL2 F) rfl
    (fun c => theta1_upper hσ F c) (fun c => theta1_lower hσ F c)
    (fun c => theta2_upper hσ μ F c) (fun c => theta2_lower hσ μ F c)
    (fun a b => by simpa using fP3_add hσ μ (a : K) (b : K))
    (fun a b => by simpa using fM3_add hσ μ (a : K) (b : K))
    (fun u w => by simpa using rel12 H (u : K) (w : K) (hfix u) (hfix w))
    (fun u w => comm13 H (u : K) (w : K) (hfix u) (hfix w))
    (fun u w => comm23 H (u : K) (w : K) (hfix u) (hfix w))
    (fun c => by rw [theta1_w hσ F]; rfl)
    (fun c => by rw [theta1_w hσ F]; exact e2_id H (c : K))
    (fun c => by rw [theta1_w hσ F]; rfl)
    (fun c => by rw [theta1_w hσ F]; exact e4_id H (c : K))
    (fun c => by rw [theta2_w hσ μ F]; simpa using f1_id H (c : K))
    (fun c => by rw [theta2_w hσ μ F]; exact f2_id H (c : K))
    (fun c => by rw [theta2_w hσ μ F]; simpa using f3_id H (c : K))
    (fun c => by rw [theta2_w hσ μ F]; exact f4_id H (c : K))


theorem exists_hom_fixSub_mu (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (μ : Kˣ) (hm : (d : K) * σ (μ : K) = μ) :
    ∃ ρ : SL(3, fixedField σ.toRingHom) →* ↥(fixSub φ),
      (∃ g, ρ g ≠ 1) ∧ Nat.card ↥(fixSub φ) = Nat.card SL(3, fixedField σ.toRingHom) ∧
        (∀ c, (((ρ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c) :
            ↥(fixSub φ)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
          ((fP1 σ.toRingHom h.cube_apply (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((ρ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c) :
            ↥(fixSub φ)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
          ((fP2 σ.toRingHom h.cube_apply μ (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((ρ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c) :
            ↥(fixSub φ)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
          ((fP3 σ.toRingHom h.cube_apply μ (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((ρ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c) :
            ↥(fixSub φ)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
          ((fM1 σ.toRingHom h.cube_apply (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((ρ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c) :
            ↥(fixSub φ)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
          ((fM2 σ.toRingHom h.cube_apply μ (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((ρ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c) :
            ↥(fixSub φ)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
          ((fM3 σ.toRingHom h.cube_apply μ (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) := by
  obtain ⟨ψ, h1, h2, h3, h4, h5, h6⟩ := exists_frame_mu h μ hm
  have hσ := h.cube_apply
  have hmem : ∀ x, ψ x ∈ twistedGroup σ.toRingHom :=
    forall_mem_of_transvections _ ψ (fun c => by rw [h1]; exact mem_P1 h _)
      (fun c => by rw [h2]; exact mem_P2 h μ _) (fun c => by rw [h3]; exact mem_P3 h μ _)
      (fun c => by rw [h4]; exact mem_M1 h _) (fun c => by rw [h5]; exact mem_M2 h μ _)
      (fun c => by rw [h6]; exact mem_M3 h μ _)
  let Fx : Subgroup (adjointGroup d4 K) :=
    { carrier := {x | a2Conj σ d (x : ModGL TwistTag.D4.tag K) = x}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul, a2Conj_mul] at hx hy ⊢
        rw [hx, hy]
      one_mem' := by
        simp only [Set.mem_setOf_eq, OneMemClass.coe_one]
        exact a2Conj_one σ d
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at hx ⊢
        rw [a2Conj_inv, hx] }
  have hfx : ∀ x, ψ x ∈ Fx :=
    forall_mem_of_transvections Fx ψ (fun c => by rw [h1]; exact fix_P1 h _ c.2)
      (fun c => by rw [h2]; exact fix_P2 h μ hm _ c.2) (fun c => by rw [h3]; exact fix_P3 h μ hm _ c.2)
      (fun c => by rw [h4]; exact fix_M1 h _ c.2) (fun c => by rw [h5]; exact fix_M2 h μ hm _ c.2)
      (fun c => by rw [h6]; exact fix_M3 h μ hm _ c.2)
  let ψt : SL(3, fixedField σ.toRingHom) →* twistedGroup σ.toRingHom :=
    ψ.codRestrict (twistedGroup σ.toRingHom) hmem
  let ρY : SL(3, fixedField σ.toRingHom) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (A2Core.a2Equiv h).toMonoidHom.comp ψt
  have hcoe : ∀ x, ((ρY x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = ((ψ x : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) :=
    fun x => rfl
  have hρfix : ∀ x, ρY x ∈ fixSub φ := fun x => by
    show φ (ρY x) = ρY x
    apply Subtype.ext
    rw [hφ, hcoe]
    exact hfx x
  let ρ : SL(3, fixedField σ.toRingHom) →* ↥(fixSub φ) := ρY.codRestrict (fixSub φ) hρfix
  have hρc : ∀ x, (((ρ x : ↥(fixSub φ)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = ((ψ x : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) :=
    fun x => rfl
  refine ⟨ρ, ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1ρ
    have h7 := h1 1
    have h8 : ψ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1) = 1 := by
      apply Subtype.ext
      rw [← hρc, h1ρ]
      rfl
    rw [h8] at h7
    exact fP1_one_ne_one hσ (by simpa using h7.symm)
  · rw [A2Core.a2_card_fixSub h φ hφ, card_sl3_eq h.two_le
      (CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom h.two_le h.card h.frob)]
  · intro c; rw [hρc, h1]
  · intro c; rw [hρc, h2]
  · intro c; rw [hρc, h3]
  · intro c; rw [hρc, h4]
  · intro c; rw [hρc, h5]
  · intro c; rw [hρc, h6]

end Frame

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

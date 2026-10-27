module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Coordinates

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace CoordsAux

section Field

variable {τ : Tag} {F : Type} [Field F]

theorem Qθ_le_of_gens {H : Subgroup (ModGL τ F)}
    (h₁ : ∀ β ∈ Deg1 τ, ∀ t : F, pinnedX τ F β t ∈ H)
    (h₂ : ∀ t : F, pinnedX τ F (highRoot τ) t ∈ H) : Qθ τ F ≤ H := by
  show rootSpan τ F (parabolicRadicalRoots τ (Jθ τ)) ≤ H
  refine iSup₂_le fun α hα => ?_
  intro g hg
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hg
  rcases (CoordAux.mem_radRoots_iff α).1 hα with h | rfl
  · exact h₁ α h t
  · exact h₂ t

private theorem pinnedX_mem_Qθ_of_Deg1 {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) (t : F) :
    pinnedX τ F β t ∈ Qθ τ F :=
  pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff β).2 (Or.inl hβ)) t

private theorem pinnedX_highRoot_mem_Qθ (t : F) : pinnedX τ F (highRoot τ) t ∈ Qθ τ F :=
  pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff (highRoot τ)).2 (Or.inr rfl)) t

theorem Qθ_induction {P : ModGL τ F → Prop}
    (hone : P 1) (hmul : ∀ x y, x ∈ Qθ τ F → y ∈ Qθ τ F → P x → P y → P (x * y))
    (hinv : ∀ x, x ∈ Qθ τ F → P x → P x⁻¹)
    (h₁ : ∀ β ∈ Deg1 τ, ∀ t : F, P (pinnedX τ F β t))
    (h₂ : ∀ t : F, P (pinnedX τ F (highRoot τ) t)) :
    ∀ x ∈ Qθ τ F, P x := by
  let H : Subgroup (ModGL τ F) :=
    { carrier := {x | x ∈ Qθ τ F ∧ P x}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, hmul x y hx.1 hy.1 hx.2 hy.2⟩
      one_mem' := ⟨one_mem _, hone⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, hinv x hx.1 hx.2⟩ }
  have hle : Qθ τ F ≤ H :=
    Qθ_le_of_gens (fun β hβ t => ⟨pinnedX_mem_Qθ_of_Deg1 hβ t, h₁ β hβ t⟩)
      (fun t => ⟨pinnedX_highRoot_mem_Qθ t, h₂ t⟩)
  exact fun x hx => (hle hx).2

@[expose] def frob (Fr : F →+* F) : ModGL τ F →* ModGL τ F := Units.map (entrywiseHom (τ := τ) Fr)

theorem frob_pinnedX (Fr : F →+* F) (β : Fin τ.rank → ℤ) (t : F) :
    frob (τ := τ) Fr (pinnedX τ F β t) = pinnedX τ F β (Fr t) := by
  show Units.map (entrywiseHom Fr) (pinnedX τ F β t) = pinnedX τ F β (Fr t)
  rw [Units.ext_iff, Units.coe_map]
  show entrywise Fr _ = _
  rw [entrywise_pinnedX]

theorem frob_Qθ (Fr : F →+* F) {x : ModGL τ F} (hx : x ∈ Qθ τ F) :
    frob (τ := τ) Fr x ∈ Qθ τ F ∧
      heisCoord τ F (frob (τ := τ) Fr x) = fun β => Fr (heisCoord τ F x β) := by
  refine Qθ_induction (P := fun x => frob (τ := τ) Fr x ∈ Qθ τ F ∧
      heisCoord τ F (frob (τ := τ) Fr x) = fun β => Fr (heisCoord τ F x β)) ?_ ?_ ?_ ?_ ?_ x hx
  · refine ⟨by rw [map_one]; exact one_mem _, ?_⟩
    rw [map_one, heisCoord_one]
    funext β
    simp
  · rintro x y hx hy ⟨hxQ, hxc⟩ ⟨hyQ, hyc⟩
    refine ⟨by rw [map_mul]; exact mul_mem hxQ hyQ, ?_⟩
    rw [map_mul, (heisCoord_spec τ F).mul _ hxQ _ hyQ, (heisCoord_spec τ F).mul _ hx _ hy, hxc,
      hyc]
    funext β
    simp only [Pi.add_apply, map_add]
  · rintro x hx ⟨hxQ, hxc⟩
    refine ⟨by rw [map_inv]; exact inv_mem hxQ, ?_⟩
    rw [map_inv, heisCoord_inv hxQ, heisCoord_inv hx, hxc]
    funext β
    simp only [Pi.neg_apply, map_neg]
  · intro β hβ t
    rw [frob_pinnedX]
    refine ⟨pinnedX_mem_Qθ_of_Deg1 hβ _, ?_⟩
    rw [(heisCoord_spec τ F).pinnedX_deg1 β hβ, (heisCoord_spec τ F).pinnedX_deg1 β hβ]
    funext γ
    by_cases h : γ = β
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]
  · intro t
    rw [frob_pinnedX]
    refine ⟨pinnedX_highRoot_mem_Qθ _, ?_⟩
    rw [(heisCoord_spec τ F).pinnedX_highRoot, (heisCoord_spec τ F).pinnedX_highRoot]
    funext γ
    simp

theorem degθ_smul_of_fix {w : WeylGroup τ} (hw : w • highRoot τ = highRoot τ)
    (β : Fin τ.rank → ℤ) : (w • β) (iθ τ) = β (iθ τ) := by
  have h := CFSG.LieType.Chevalley.iform_smul w (highRoot τ) β
  rw [hw, iform_highRoot_apply, iform_highRoot_apply] at h
  exact mul_left_cancel₀ (cθ_ne_zero τ) h

theorem exists_monomial {w : WeylGroup τ} (hw : w • highRoot τ = highRoot τ) :
    ∃ ε : (Fin τ.rank → ℤ) → F, (∀ β ∈ Deg1 τ, ε β * ε β = 1) ∧ ∀ x ∈ Qθ τ F,
      canonicalRep (coxeterSystem τ) F w * x * (canonicalRep (coxeterSystem τ) F w)⁻¹ ∈ Qθ τ F ∧
      ∀ β ∈ Deg1 τ, heisCoord τ F (canonicalRep (coxeterSystem τ) F w * x *
        (canonicalRep (coxeterSystem τ) F w)⁻¹) (w • β) = ε β * heisCoord τ F x β := by
  have hex : ∀ β : Fin τ.rank → ℤ, ∃ e : F, IsRoot τ β → e * e = 1 ∧ ∀ c : F,
      canonicalRep (coxeterSystem τ) F w * pinnedX τ F β c *
        (canonicalRep (coxeterSystem τ) F w)⁻¹ = pinnedX τ F (w • β) (e * c) := by
    intro β
    by_cases hβ : IsRoot τ β
    · obtain ⟨e, he, hc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv F w hβ
      exact ⟨e, fun _ => ⟨he, hc⟩⟩
    · exact ⟨1, fun h => absurd h hβ⟩
  choose ε hε using hex
  obtain ⟨e₀, -, hθ⟩ := exists_canonicalRep_mul_pinnedX_mul_inv F w (isRoot_highRoot τ)
  refine ⟨ε, fun β hβ => (hε β (CoordAux.mem_Deg1.1 hβ).1).1, ?_⟩
  generalize canonicalRep (coxeterSystem τ) F w = n at hε hθ ⊢
  refine Qθ_induction ?_ ?_ ?_ ?_ ?_
  · refine ⟨by rw [mul_one, mul_inv_cancel]; exact one_mem _, fun β _ => ?_⟩
    rw [mul_one, mul_inv_cancel, heisCoord_one, Pi.zero_apply, Pi.zero_apply, mul_zero]
  · rintro x y hx hy ⟨hxQ, hxc⟩ ⟨hyQ, hyc⟩
    have e : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
    refine ⟨by rw [e]; exact mul_mem hxQ hyQ, fun β hβ => ?_⟩
    rw [e, (heisCoord_spec τ F).mul _ hxQ _ hyQ, (heisCoord_spec τ F).mul _ hx _ hy,
      Pi.add_apply, Pi.add_apply, hxc β hβ, hyc β hβ, mul_add]
  · rintro x hx ⟨hxQ, hxc⟩
    have e : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
    refine ⟨by rw [e]; exact inv_mem hxQ, fun β hβ => ?_⟩
    rw [e, heisCoord_inv hxQ, heisCoord_inv hx, Pi.neg_apply, Pi.neg_apply, hxc β hβ, mul_neg]
  · intro γ hγ t
    have hγr : IsRoot τ γ := (CoordAux.mem_Deg1.1 hγ).1
    have hwγ : w • γ ∈ Deg1 τ :=
      CoordAux.mem_Deg1.2 ⟨IsRoot.smul hγr w, by
        rw [degθ_smul_of_fix hw γ]; exact (CoordAux.mem_Deg1.1 hγ).2⟩
    rw [(hε γ hγr).2 t]
    refine ⟨pinnedX_mem_Qθ_of_Deg1 hwγ _, fun β _ => ?_⟩
    rw [(heisCoord_spec τ F).pinnedX_deg1 _ hwγ, (heisCoord_spec τ F).pinnedX_deg1 _ hγ]
    by_cases hβγ : β = γ
    · subst hβγ
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · have hne : w • β ≠ w • γ := fun h => hβγ ((smul_left_cancel_iff w).1 h)
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hβγ, mul_zero]
  · intro t
    rw [hθ t, hw]
    refine ⟨pinnedX_highRoot_mem_Qθ _, fun β _ => ?_⟩
    rw [(heisCoord_spec τ F).pinnedX_highRoot, (heisCoord_spec τ F).pinnedX_highRoot,
      Pi.zero_apply, Pi.zero_apply, mul_zero]

end Field

end CoordsAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

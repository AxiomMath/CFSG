module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Datum

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis

section SL2

variable {F : Type*} [Field F]

theorem HSL_mul (s t : Fˣ) : (HSL (s * t) : SL2 F) = HSL s * HSL t := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, Units.val_mul, mul_inv_rev]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSL_one : (HSL (1 : Fˣ) : SL2 F) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_HSL]

end SL2

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem xC_injective (a : Fin t.foldedTag.rank) : Function.Injective (xC t K σ a) :=
  fun c c' h => by
    have h1 : ((xC t K σ a c : ↥(graphFixedRootGroup t K σ)) : ModGL t.tag K) =
        ((xC t K σ a c' : ↥(graphFixedRootGroup t K σ)) : ModGL t.tag K) := congrArg Subtype.val h
    exact orbitX_injective σ a (Subtype.ext h1)

variable [Finite K] {p : ℕ} [CharP K p] {D₀ : LongestData t} {hσ : Function.Surjective σ}
  {q : ℕ} {hq : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card}

theorem mem_X_twistedDatum {a : Fin t.foldedTag.rank} {x : ↥(graphFixedRootGroup t K σ)} :
    x ∈ (twistedDatum p D₀ hσ hq).X a ↔ ∃ c : orbitField t K σ a, xC t K σ a c = x := by
  change (x : ModGL t.tag K) ∈ Xg t K σ a ↔ _
  rw [mem_Xg_iff]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, Subtype.ext hc⟩, fun ⟨c, hc⟩ => ⟨c, congrArg Subtype.val hc⟩⟩

theorem xC_mem_X (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    xC t K σ a c ∈ (twistedDatum p D₀ hσ hq).X a :=
  mem_X_twistedDatum.mpr ⟨c, rfl⟩

theorem heckeT_twistedDatum (a : Fin t.foldedTag.rank) [Fintype (orbitField t K σ a)]
    {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k ↥(graphFixedRootGroup t K σ) V)
    (v : V) :
    (twistedDatum p D₀ hσ hq).heckeT ρ a v = ∑ c : orbitField t K σ a, ρ (xC t K σ a c * nC t K σ a) v := by
  have := Fintype.ofFinite ((twistedDatum p D₀ hσ hq).X a)
  rw [CurtisDatum.heckeT_apply]
  symm
  refine Fintype.sum_bijective (fun c => ⟨xC t K σ a c, xC_mem_X a c⟩) ⟨fun c d h =>
    xC_injective a (congrArg Subtype.val h), fun x => ?_⟩ _ _ fun c => rfl
  obtain ⟨c, hc⟩ := mem_X_twistedDatum.mp x.2
  exact ⟨c, Subtype.ext hc⟩

theorem hC_mem_H (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    hC t K σ a u ∈ (twistedDatum p D₀ hσ hq).H :=
  hC_mem a u

variable (p D₀ hσ hq) in
@[expose] def IsTwType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k ↥(graphFixedRootGroup t K σ) V) (y : V)
    (χ : ↥(graphFixedRootGroup t K σ) → k) (J : Finset (Fin t.foldedTag.rank)) : Prop :=
  y ∈ (twistedDatum p D₀ hσ hq).fixU ρ ∧ y ≠ 0 ∧
    (∀ h ∈ (twistedDatum p D₀ hσ hq).H, ρ h y = χ h • y) ∧
    ∀ a, a ∈ J ↔ (∀ u : (orbitField t K σ a)ˣ, χ (hC t K σ a u) = 1) ∧
      (twistedDatum p D₀ hσ hq).heckeT ρ a y = 0

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

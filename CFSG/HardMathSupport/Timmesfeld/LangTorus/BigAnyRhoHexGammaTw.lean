module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTwE6Class
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRhoHexGamma
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FixUnitaryTwo
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwE6ModelIndex

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Fix

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem twistedLine_fix_le_Γ_of_two (hAlg : S.IsAlgebraic) (hq2 : S.D.q = 2)
    (h2 : ∀ m ∈ S.D.model, m ^ 2 ∈ S.Γ → m ∈ S.Γ)
    {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j, i ≠ j → S.ρ (σ i j) = σ (π j) (π i)) :
    ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) ≤ S.Γ := by
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := exists_char_pow S
  obtain ⟨k, hk, hcl⟩ := twistedLine_exists_field S hAlg
  obtain ⟨Fr, hFr, -⟩ := S.D.steinberg
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFr, hq]
  have hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L, S.D.step (pinnedX τ L (σ i j) c) =
      pinnedX τ L (σ (π j) (π i)) ((b : L) * Fr c) := by
    intro i j hij
    obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S (h.isRoot i j hij)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hμ c, hπ i j hij, Units.val_mk0, hFr]
  have hM : ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) ≤ S.D.model :=
    inf_le_inf_right _ h.range_le_adjointGroup
  exact unitaryFrame_fix_le_of_two h hinj hℓ hf (hq.symm.trans hq2) (hk.trans hq) Fr hFr'
    S.D.step (splitLine_step_injective S) π hΨ S.Γ fun x hx hx2 => h2 x (hM hx) hx2

end Fix

section Hex


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)

theorem twistedLine_hexGroup_le_of_two (hAlg : S.IsAlgebraic) (hq2 : S.D.q = 2)
    (h2 : ∀ m ∈ S.D.model, m ^ 2 ∈ S.Γ → m ∈ S.Γ)
    (hrel : ∀ δ, IsRoot Tag.E6 δ → S.ρ (S.ρ δ) = S.ρ δ - δ)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    rootSpan Tag.E6 L {x | ∃ j : ℕ, x = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] γ} ⊓ S.D.model ≤
      S.Γ := by
  obtain ⟨ρ', σ, hfr, hinj, h01, h12⟩ := twistedLine_hex_frame S hrel hγ
  obtain ⟨hπ, hset⟩ := twistedLine_hex_shape S hrel hγ hfr h01 h12
  have hY := twistedLine_fix_le_Γ_of_two S hAlg hq2 h2 hfr hinj (finRotate 3) hπ
  rw [hset, ← hfr.range]
  rintro x ⟨hx1, hx2⟩
  exact hY ⟨hx1, (Subgroup.mem_inf.1 hx2).2⟩

end Hex

section Main


theorem twE6HexGamma_holds : TwE6HexGamma := by
  intro L _ _ p S hcl hp7 hAlg
  by_cases hq3 : 3 ≤ S.D.q
  · exact S.hexGroupInGamma_of_hexStep_E6 (S.hexStep_of_twE6SixClass hcl) hAlg hq3
  · have hq2 : S.D.q = 2 := le_antisymm (by omega) S.hqpow.1.two_le
    have hex := S.hexStep_of_twE6SixClass hcl
    obtain ⟨Fr, hFr, hΦ, -⟩ := hcl
    obtain ⟨k, hk⟩ := twE6_model_pow_mem_Γ S hAlg Fr hFr hΦ
    exact fun γ hγ => twistedLine_hexGroup_le_of_two S hAlg hq2
      (fun m hm hm2 => mem_of_sq_mem_of_pow_mem S.Γ k (hk m hm) hm2) hex.rel6 hγ

end Main

end CFSG.HardMathSupport.Timmesfeld.LangTorus

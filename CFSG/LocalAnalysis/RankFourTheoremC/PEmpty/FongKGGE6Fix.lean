module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6Form
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotEndFieldEvenAut

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.E6Pilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

set_option linter.unusedSectionVars false


abbrev kggScales {F : Type} [Field F] (x : ModGL Tag.E6 F) : Prop :=
  ∃ μ : Fˣ, ∀ c : F, x * pinnedX Tag.E6 F e6HighestRoot c * x⁻¹ =
    pinnedX Tag.E6 F e6HighestRoot ((μ : F) * c)

theorem kggScales_one {F : Type} [Field F] : kggScales (1 : ModGL Tag.E6 F) :=
  ⟨1, fun c => by simp⟩

theorem kggScales_mul {F : Type} [Field F] {x y : ModGL Tag.E6 F} (hx : kggScales x)
    (hy : kggScales y) : kggScales (x * y) := by
  obtain ⟨μx, hx⟩ := hx
  obtain ⟨μy, hy⟩ := hy
  refine ⟨μx * μy, fun c => ?_⟩
  calc x * y * pinnedX Tag.E6 F e6HighestRoot c * (x * y)⁻¹
      = x * (y * pinnedX Tag.E6 F e6HighestRoot c * y⁻¹) * x⁻¹ := by
        simp only [mul_inv_rev, mul_assoc]
    _ = x * pinnedX Tag.E6 F e6HighestRoot ((μy : F) * c) * x⁻¹ := by rw [hy c]
    _ = pinnedX Tag.E6 F e6HighestRoot ((μx : F) * ((μy : F) * c)) := hx _
    _ = pinnedX Tag.E6 F e6HighestRoot (((μx * μy : Fˣ) : F) * c) := by
        rw [Units.val_mul, mul_assoc]

theorem kggScales_inv {F : Type} [Field F] {x : ModGL Tag.E6 F} (hx : kggScales x) :
    kggScales x⁻¹ := by
  obtain ⟨μ, hμ⟩ := hx
  refine ⟨μ⁻¹, fun c => ?_⟩
  have hc : (μ : F) * (((μ⁻¹ : Fˣ) : F) * c) = c := by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have h1 := hμ (((μ⁻¹ : Fˣ) : F) * c)
  rw [hc] at h1
  rw [inv_inv, ← h1]
  simp [mul_assoc]

def kggSub (F : Type) [Field F] : Subgroup (ModGL Tag.E6 F) where
  carrier := {x | kggScales x}
  one_mem' := kggScales_one
  mul_mem' := fun hx hy => kggScales_mul hx hy
  inv_mem' := fun hx => kggScales_inv hx

theorem kgg_borel_scales {F : Type} [Field F] {b : ModGL Tag.E6 F}
    (hb : b ∈ borelGroup Tag.E6 F) : kggScales b := by
  have hle : borelGroup Tag.E6 F ≤ kggSub F := by
    unfold borelGroup
    refine sup_le ?_ ?_
    · unfold torusGroup
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨i, u⟩, rfl⟩
      show kggScales (torusElt Tag.E6 F i u)
      rw [torusElt_eq_rootDiagUnit]
      exact ⟨_, fun c => rootDiagUnit_conj_pinnedX _ isRoot_e6HighestRoot c⟩
    · intro u hu
      show kggScales u
      refine ⟨1, fun c => ?_⟩
      have hcomm : u * pinnedX Tag.E6 F e6HighestRoot c =
          pinnedX Tag.E6 F e6HighestRoot c * u :=
        (commute_e6HighestRoot_of_mem_posUnipotent F hu c).eq
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one, Units.val_one, one_mul]
  exact hle hb

theorem e6_fix_theta {F : Type} [Field F] [Finite F] [CharP F 2]
    (Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2))
    (hΘ : ∀ (g : C6 F) (a : Fin Tag.E6.rank → Fˣ) (ρ : F ≃+* F) (ε : ℕ),
      Θ (MulAut.conj g * exactNormalAut .E6 F a ρ ε) = (ρ, Multiplicative.ofAdd (ε : ZMod 2)))
    {τ : MulAut (C6 F)} (hτ : τ ∈ stabU F) (hτ2 : τ * τ = 1)
    (hΘτ : Θ τ = (1, Multiplicative.ofAdd (1 : ZMod 2))) (c : F) :
    τ (xPar (rootOperatorFamily Tag.E6) e6HighestRoot c) =
      xPar (rootOperatorFamily Tag.E6) e6HighestRoot c := by
  obtain ⟨g, a, ρ, ε, hgB, hτeq⟩ := e6_form_of_stabU hτ
  have hΘg : Θ τ = (ρ, Multiplicative.ofAdd (ε : ZMod 2)) := by
    rw [hτeq]
    exact hΘ g a ρ ε
  rw [hΘτ] at hΘg
  have hρ : ρ = 1 := (Prod.mk.inj hΘg).1.symm
  have hε1 : ((ε : ℕ) : ZMod 2) = 1 :=
    (Multiplicative.ofAdd.injective (Prod.mk.inj hΘg).2).symm
  have hεodd : ε % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one ε with h | h
    · exfalso
      have h0 : ((ε : ℕ) : ZMod 2) = 0 := by
        rw [← ZMod.natCast_mod, h, Nat.cast_zero]
      rw [h0] at hε1
      exact absurd hε1 (by decide)
    · exact h
  subst hρ
  have hN : exactNormalAut Tag.E6 F a 1 ε = exactNormalAut Tag.E6 F a 1 1 := by
    have h := CFSG.SeitzReduction.E6Pilot.exactNormalAut_mod_two_E6 (K := F) a 1 ε
    rw [hεodd] at h
    exact h.symm
  rw [hN] at hτeq
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  obtain ⟨μg, hμg⟩ := kgg_borel_scales (F := F) hgB
  have hXcoe : ∀ d : F, ((xPar (rootOperatorFamily Tag.E6) e6HighestRoot d : C6 F) :
      ModGL Tag.E6 F) = pinnedX Tag.E6 F e6HighestRoot d :=
    fun d => CFSG.SeitzReduction.E6Pilot.coe_xPar_eq_pinnedX isRoot_e6HighestRoot d
  have hXinj : ∀ d₁ d₂ : F, xPar (rootOperatorFamily Tag.E6) e6HighestRoot d₁ =
      xPar (rootOperatorFamily Tag.E6) e6HighestRoot d₂ → d₁ = d₂ := by
    intro d₁ d₂ h
    refine pinnedX_injective (τ := Tag.E6) (R := F) e6HighestRoot ?_
    rw [← hXcoe d₁, ← hXcoe d₂, h]
  have hNX : ∀ d : F, ((exactNormalAut Tag.E6 F a 1 1
      (xPar (rootOperatorFamily Tag.E6) e6HighestRoot d) : C6 F) : ModGL Tag.E6 F) =
      pinnedX Tag.E6 F e6HighestRoot
        (((CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a e6HighestRoot :
          Fˣ) : F) * d) := by
    intro d
    obtain ⟨Q, hQdef⟩ : ∃ Q : ModGL Tag.E6 F, Q = diagramMap TwistTag.E6 F := ⟨_, rfl⟩
    have hid : Units.map (entrywiseHom (1 : F ≃+* F).toRingHom)
        (pinnedX Tag.E6 F e6HighestRoot d) = pinnedX Tag.E6 F e6HighestRoot d :=
      Units.ext (entrywise_id _)
    have hQ : exactQ Tag.E6 F 1 = Q := by
      rw [hQdef]
      exact pow_one _
    have hD : Q * pinnedX Tag.E6 F e6HighestRoot d * Q⁻¹ = pinnedX Tag.E6 F e6HighestRoot d := by
      rw [hQdef]
      exact CFSG.LieType.Chevalley.E6GraphLevi.diagramMap_conj_pinnedX_theta (E := F) h2 true d
    have hR := rootDiagUnit_conj_pinnedX (τ := Tag.E6) (K := F) a isRoot_e6HighestRoot d
    rw [CFSG.LieType.Chevalley.coe_exactNormalAut, hXcoe, hid, hQ]
    calc _ = rootDiagUnit Tag.E6 a * (Q * pinnedX Tag.E6 F e6HighestRoot d * Q⁻¹) *
          (rootDiagUnit Tag.E6 a)⁻¹ := by simp only [mul_assoc]
      _ = rootDiagUnit Tag.E6 a * pinnedX Tag.E6 F e6HighestRoot d * (rootDiagUnit Tag.E6 a)⁻¹ := by
          rw [hD]
      _ = _ := hR
  have hτX : ∀ d : F, ((τ (xPar (rootOperatorFamily Tag.E6) e6HighestRoot d) : C6 F) :
      ModGL Tag.E6 F) = pinnedX Tag.E6 F e6HighestRoot ((μg : F) *
        (((CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a e6HighestRoot :
          Fˣ) : F) * d)) := by
    intro d
    rw [hτeq, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hNX d, hμg]
  obtain ⟨μ, hμ⟩ : ∃ μ : Fˣ, ∀ d : F, τ (xPar (rootOperatorFamily Tag.E6) e6HighestRoot d) =
      xPar (rootOperatorFamily Tag.E6) e6HighestRoot ((μ : F) * d) := by
    refine ⟨μg * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a
      e6HighestRoot, fun d => ?_⟩
    apply Subtype.ext
    rw [hτX d, hXcoe, Units.val_mul, mul_assoc]
  have hinv : ∀ d : F, τ (τ (xPar (rootOperatorFamily Tag.E6) e6HighestRoot d)) =
      xPar (rootOperatorFamily Tag.E6) e6HighestRoot d := by
    intro d
    have h := DFunLike.congr_fun hτ2 (xPar (rootOperatorFamily Tag.E6) e6HighestRoot d)
    simpa using h
  have hμμ : (μ : F) * (μ : F) = 1 := by
    have h1 := hinv 1
    rw [hμ 1, hμ ((μ : F) * 1)] at h1
    have h3 := hXinj _ _ h1
    rw [mul_one] at h3
    exact h3
  have hμ1 : (μ : F) = 1 := eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hμμ
  rw [hμ c, hμ1, one_mul]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

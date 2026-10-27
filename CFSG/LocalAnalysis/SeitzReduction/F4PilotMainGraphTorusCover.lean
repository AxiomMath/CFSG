module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusNormal

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL descendAut conjAut dualAut)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

section Generic

variable {n : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem exists_cover_of_descendAut_eq (hn : 3 ≤ n) (Φ : SpecialLinearGroup (Fin n) F →* G)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin n) F)) {t : G}
    {β : MulAut (SpecialLinearGroup (Fin n) F)} (hβ : ∀ g, Φ (β g) = t * Φ g * t⁻¹)
    {H C : GL (Fin n) F}
    (hHC : descendAut n F β = conjAut n F H * (conjAut n F C * dualAut n F) * (conjAut n F H)⁻¹) :
    ∃ Φ₁ : SpecialLinearGroup (Fin n) F →* G, Φ₁.range = Φ.range ∧
      Φ₁.ker ≤ center (SpecialLinearGroup (Fin n) F) ∧
      ∀ g, t * Φ₁ g * t⁻¹ = Φ₁ ((slConjugation n F C * slGraphAut n F) g) := by
  have hβeq : β = slConjugation n F H * (slConjugation n F C * slGraphAut n F) *
      (slConjugation n F H)⁻¹ := by
    apply graphTorus_descendAut_injective hn
    rw [hHC, map_mul, map_mul, map_mul, map_inv]
    rfl
  set sH : MulAut (SpecialLinearGroup (Fin n) F) := slConjugation n F H with hsH
  refine ⟨Φ.comp sH.toMonoidHom, ?_, ?_, fun g => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 sH.surjective, ← MonoidHom.range_eq_map]
  · intro g hg
    have h1 : sH g ∈ center (SpecialLinearGroup (Fin n) F) := hker hg
    have h2 := Subgroup.map_center_eq (sH.symm : SpecialLinearGroup (Fin n) F ≃* _)
    rw [← h2]
    exact ⟨sH g, h1, sH.symm_apply_apply g⟩
  · have e1 : sH ((slConjugation n F C * slGraphAut n F) g) = β (sH g) := by
      rw [hβeq]
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    change t * Φ (sH g) * t⁻¹ = Φ (sH ((slConjugation n F C * slGraphAut n F) g))
    rw [e1, hβ]

end Generic

section Setting


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_graphCover6_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .linear6) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ f) (Φ : SpecialLinearGroup (Fin 6) F →* G)
    (hE : Φ.range = neighbourCore e .X) (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) F)) :
    ∃ Φ₁ : SpecialLinearGroup (Fin 6) F →* G, Φ₁.range = neighbourCore e .X ∧
      Φ₁.ker ≤ center (SpecialLinearGroup (Fin 6) F) ∧
      ∀ g, t * Φ₁ g * t⁻¹ = Φ₁ ((slConjugation 6 F (graphGram6 F) * slGraphAut 6 F) g) := by
  obtain ⟨β, hβ, -, hα2, hαo, hfix⟩ := exists_graphLift_X hw hf e (by decide) (by decide) hX
    (m := 5) (by norm_num) Φ hE hker
  obtain ⟨H, hH⟩ := exists_eq_conj_graphGram6 (by omega) hF (descendAut 6 F β) hα2 hαo hfix
  obtain ⟨Φ₁, hr, hk, hc⟩ := exists_cover_of_descendAut_eq (by norm_num) Φ hker hβ hH
  exact ⟨Φ₁, hr.trans hE, hk, hc⟩

theorem exists_graphCover7_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .linear7) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ f) (Φ : SpecialLinearGroup (Fin 7) F →* G)
    (hE : Φ.range = neighbourCore e .X) (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin 7) F)) :
    ∃ Φ₁ : SpecialLinearGroup (Fin 7) F →* G, Φ₁.range = neighbourCore e .X ∧
      Φ₁.ker ≤ center (SpecialLinearGroup (Fin 7) F) ∧
      ∀ g, t * Φ₁ g * t⁻¹ = Φ₁ ((slConjugation 7 F (graphGram7 F) * slGraphAut 7 F) g) := by
  obtain ⟨β, hβ, -, hα2, hαo, hfix⟩ := exists_graphLift_X hw hf e (by decide) (by decide) hX
    (m := 6) (by norm_num) Φ hE hker
  obtain ⟨H, hH⟩ := exists_eq_conj_graphGram7 (by omega) hF (descendAut 7 F β) hα2 hαo hfix
  obtain ⟨Φ₁, hr, hk, hc⟩ := exists_cover_of_descendAut_eq (by norm_num) Φ hker hβ hH
  exact ⟨Φ₁, hr.trans hE, hk, hc⟩

end Setting

end CFSG.SeitzReduction.F4Pilot

module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenAction

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)

section ConjAction

variable {G : Type} [Group G] {W : Type*} [Group W] {X : Subgroup W} {A : Subgroup G}

@[expose] def conjAction (ψ : normalizer (A : Set G) →* W) (g : G) :
    normalizer (rightConjugate A g : Set G) →* W :=
  ψ.comp
    { toFun := fun x => ⟨g * x * g⁻¹, (AS76b.mem_normalizer_rightConjugate_iff A g x).1 x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change g * (x * y : G) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)
        group) }

theorem conjAction_apply (ψ : normalizer (A : Set G) →* W) (g x : G)
    (hx : x ∈ normalizer (rightConjugate A g : Set G)) :
    conjAction ψ g ⟨x, hx⟩ =
      ψ ⟨g * x * g⁻¹, (AS76b.mem_normalizer_rightConjugate_iff A g x).1 hx⟩ :=
  rfl

theorem isActionHom_conjAction {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    (g : G) : IsActionHom (rightConjugate A g) X (conjAction ψ g) := by
  refine ⟨fun a ha => ?_, fun x hx => ?_, fun n => ?_⟩
  · rw [conjAction_apply]
    exact hψ.map_mem _ ((mem_rightConjugate_iff A g a).1 ha)
  · obtain ⟨a, ha, h⟩ := hψ.exists_eq x hx
    have ha' : g⁻¹ * a * g ∈ rightConjugate A g := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using ha
    refine ⟨g⁻¹ * a * g, ha', ?_⟩
    rw [conjAction_apply, ← h]
    congr 1
    apply Subtype.ext
    simp only
    group
  · obtain ⟨x, hx⟩ := n
    rw [conjAction_apply, hψ.eq_one_iff, RankTwoL3Even.mem_centralizer_rightConjugate_iff]

end ConjAction

section Choice

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

theorem sec3_mul_left (hc : Sec3 A R T g) {b : G} (hb : b ∈ A) : Sec3 A R T (b * g) := by
  have hbN : b ∈ normalizer (centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq hc.hyp.standard]
    exact le_normalizer hb
  refine ⟨hc.hyp, hc.sylowR, fun h => hc.not_mem ?_, ?_, hc.le_centralizer⟩
  · have := mul_mem (inv_mem (le_normalizer hb)) h
    rwa [inv_mul_cancel_left] at this
  · rw [← rightConjugate_mul, (rightConjugate_eq_self_iff _ b).2 hbN]
    exact hc.sylowT

omit [Finite G] in
theorem rightConjugate_inv_mul_inv (R : Subgroup G) (b g : G) :
    rightConjugate R (b⁻¹ * g)⁻¹ = rightConjugate (rightConjugate R g⁻¹) b := by
  rw [mul_inv_rev, inv_inv, rightConjugate_mul]

omit [Finite G] in
theorem conj_mem_rightConjugate_inv {r : G} (hr : r ∈ R) (g : G) :
    g * r * g⁻¹ ∈ rightConjugate R g⁻¹ := by
  rw [mem_rightConjugate_iff]
  simpa [mul_assoc] using hr

end Choice

end CFSG.ComponentClassification.RankTwoExceptional

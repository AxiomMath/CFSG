module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Free.Wreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Factors
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.LeCommutator

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.RankThree.Literature.FSmith

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem AschbacherHyp.exists_hom_swap [Finite C] (hC : AschbacherHyp C Q) {t : C}
    (ht : IsOuterInvolution Q t) :
    ∃ (θ : ↥(commutator C) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))
      (σ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
        (Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)))
      (s : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) ≃*
        alternatingGroup (Fin 5) × alternatingGroup (Fin 5)),
      Function.Surjective θ ∧ (∀ l : ↥(commutator C), θ l = 1 ↔ (l : C) ∈ Q) ∧
      (∀ l : ↥(commutator C), σ (θ l) = conjLinEquiv hQn (l : C)) ∧ Function.Injective σ ∧
      (∀ U : Submodule (ZMod 2) (Additive (Abelianization Q)),
        (∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∀ u ∈ U, σ g u ∈ U) →
          U = ⊥ ∨ U = ⊤) ∧
      Swap.SwapsFactorsAut s ∧
      (∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
        conjLinEquiv hQn t * σ g * (conjLinEquiv hQn t)⁻¹ = σ (s g)) := by
  classical
  obtain ⟨e, θ, σ, hθs, hθk, hθe, hσθ, hσi, hirr⟩ := hC.exists_hom_baseEmb
  let u : A5WrTwo := e (QuotientGroup.mk t)
  have hu2 : u ^ 2 = 1 := by
    have h : u = e (QuotientGroup.mk' Q t) := rfl
    rw [h, ← map_pow, show (QuotientGroup.mk' Q t : C ⧸ Q) ^ 2 =
      QuotientGroup.mk' Q (t ^ 2) from (map_pow (QuotientGroup.mk' Q) t 2).symm, ht.2.1]
    simp
  have hu : u ∉ commutator A5WrTwo := by
    rw [← A5WrTwo.range_baseEmb]
    rintro ⟨g, hg⟩
    obtain ⟨l, hl⟩ := hθs g
    have heq : e (QuotientGroup.mk (l : C)) = e (QuotientGroup.mk t) := by
      rw [← hθe l, hl, hg]
    have hmk : (QuotientGroup.mk (l : C) : C ⧸ Q) = QuotientGroup.mk t := e.injective heq
    have hmem : (l : C)⁻¹ * t ∈ Q := QuotientGroup.eq.mp hmk
    have htL : t ∈ commutator C := by
      have h1 : (l : C) * ((l : C)⁻¹ * t) ∈ commutator C :=
        (commutator C).mul_mem l.2 (hC.le_commutator hmem)
      simpa using h1
    exact ht.1 htL
  obtain ⟨x₀, hx₀⟩ := A5WrTwo.exists_conj_baseEmb hu hu2
  let s : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) ≃*
      alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
    { toFun := fun p => (x₀ * p.2 * x₀⁻¹, x₀⁻¹ * p.1 * x₀)
      invFun := fun p => (x₀ * p.2 * x₀⁻¹, x₀⁻¹ * p.1 * x₀)
      left_inv := fun p => by apply Prod.ext <;> group
      right_inv := fun p => by apply Prod.ext <;> group
      map_mul' := fun p q => by
        apply Prod.ext <;> simp only [Prod.fst_mul, Prod.snd_mul] <;> group }
  have hs : Swap.SwapsFactorsAut s := by
    unfold Swap.SwapsFactorsAut
    constructor
    · intro x
      exact ⟨x₀⁻¹ * x * x₀, by apply Prod.ext <;> simp [s]⟩
    · intro y
      exact ⟨x₀ * y * x₀⁻¹, by apply Prod.ext <;> simp [s]⟩
  have hkey : ∀ l : ↥(commutator C),
      θ ⟨t * (l : C) * t⁻¹,
          (inferInstance : (commutator C).Normal).conj_mem (l : C) l.2 t⟩ = s (θ l) := by
    intro l
    apply A5WrTwo.baseEmb_injective
    have hΦ : e (QuotientGroup.mk (t * (l : C) * t⁻¹)) =
        u * e (QuotientGroup.mk (l : C)) * u⁻¹ := by
      have hq : (QuotientGroup.mk (t * (l : C) * t⁻¹) : C ⧸ Q) =
          QuotientGroup.mk t * QuotientGroup.mk (l : C) * (QuotientGroup.mk t)⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hq, map_mul, map_mul, map_inv]
    rw [hθe, hΦ, ← hθe l]
    simpa [s] using hx₀ (θ l).1 (θ l).2
  have hrel : ∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      conjLinEquiv hQn t * σ g * (conjLinEquiv hQn t)⁻¹ = σ (s g) := by
    intro g
    obtain ⟨l, hl⟩ := hθs g
    let l' : ↥(commutator C) :=
      ⟨t * (l : C) * t⁻¹,
        (inferInstance : (commutator C).Normal).conj_mem (l : C) l.2 t⟩
    have hθl' : θ l' = s (θ l) := hkey l
    calc conjLinEquiv hQn t * σ g * (conjLinEquiv hQn t)⁻¹
        = conjLinEquiv hQn t * σ (θ l) * (conjLinEquiv hQn t)⁻¹ := by rw [hl]
      _ = conjLinEquiv hQn t * conjLinEquiv hQn (l : C) * (conjLinEquiv hQn t)⁻¹ := by
            rw [hσθ l]
      _ = conjLinEquiv hQn (t * (l : C) * t⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = conjLinEquiv hQn (l' : C) := by rw [show (l' : C) = t * (l : C) * t⁻¹ from rfl]
      _ = σ (θ l') := by rw [hσθ l']
      _ = σ (s (θ l)) := by rw [hθl']
      _ = σ (s g) := by rw [hl]
  exact ⟨θ, σ, s, hθs, hθk, hσθ, hσi, hirr, hs, hrel⟩

end CFSG.EvenSporadicStandard.HNRecog

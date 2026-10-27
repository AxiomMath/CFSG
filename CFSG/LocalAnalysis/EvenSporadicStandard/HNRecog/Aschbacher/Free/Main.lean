module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Free.Abstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Free.Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup Module CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem AschbacherHyp.exists_free_involution [Finite C] (hC : AschbacherHyp C Q) {t : C}
    (ht : IsOuterInvolution Q t) :
    4 ≤ finrank (ZMod 2) (LinearMap.range
      ((conjLinEquiv hQn t : Additive (Abelianization Q) →ₗ[ZMod 2] Additive (Abelianization Q)) + 1)) := by
  classical
  haveI : Finite Q := hC.plus.finite
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  obtain ⟨e, θ, σ, hθs, hθk, hθe, hσθ, hσi, hirr⟩ := hC.exists_hom_baseEmb
  let u : A5WrTwo := e (QuotientGroup.mk t)
  let b : Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q) := conjLinEquiv hQn t
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
  have hb : b * b = 1 := by
    change conjLinEquiv hQn t * conjLinEquiv hQn t = 1
    rw [← map_mul, show t * t = t ^ 2 from (pow_two t).symm, ht.2.1, map_one]
  have hcomm : ∀ y : alternatingGroup (Fin 5),
      σ (x₀ * y * x₀⁻¹, y) * b = b * σ (x₀ * y * x₀⁻¹, y) := by
    intro y
    obtain ⟨l, hl⟩ := hθs (x₀ * y * x₀⁻¹, y)
    let l' : ↥(commutator C) :=
      ⟨t * (l : C) * t⁻¹,
        (inferInstance : (commutator C).Normal).conj_mem (l : C) l.2 t⟩
    have hl'_eq : (l' : C) = t * (l : C) * t⁻¹ := rfl
    have hΦ : e (QuotientGroup.mk (l' : C)) = u * e (QuotientGroup.mk (l : C)) * u⁻¹ := by
      have hq : (QuotientGroup.mk (l' : C) : C ⧸ Q) =
          QuotientGroup.mk t * QuotientGroup.mk (l : C) * (QuotientGroup.mk t)⁻¹ := by
        rw [hl'_eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hq, map_mul, map_mul, map_inv]
    have hθl' : θ l' = θ l := by
      apply A5WrTwo.baseEmb_injective
      rw [hθe l', hθe l, hΦ]
      have hg : A5WrTwo.baseEmb (x₀ * y * x₀⁻¹, y) = e (QuotientGroup.mk (l : C)) := by
        rw [← hθe l, hl]
      have hfixg : u * A5WrTwo.baseEmb (x₀ * y * x₀⁻¹, y) * u⁻¹ =
          A5WrTwo.baseEmb (x₀ * y * x₀⁻¹, y) := by
        have hx := hx₀ (x₀ * y * x₀⁻¹) y
        rw [show x₀⁻¹ * (x₀ * y * x₀⁻¹) * x₀ = y from by group] at hx
        exact hx
      rw [← hg]
      exact hfixg
    have hll' : conjLinEquiv hQn (l : C) = conjLinEquiv hQn (l' : C) := by
      rw [← hσθ l, ← hσθ l', hθl']
    have hl'_mul : conjLinEquiv hQn (l' : C) =
        conjLinEquiv hQn t * conjLinEquiv hQn (l : C) * (conjLinEquiv hQn t)⁻¹ := by
      rw [hl'_eq, map_mul, map_mul, map_inv]
    have hconj : conjLinEquiv hQn (l : C) =
        conjLinEquiv hQn t * conjLinEquiv hQn (l : C) * (conjLinEquiv hQn t)⁻¹ :=
      hll'.trans hl'_mul
    have hσg : σ (x₀ * y * x₀⁻¹, y) = conjLinEquiv hQn (l : C) := by
      rw [← hl, hσθ l]
    rw [hσg, show b = conjLinEquiv hQn t from rfl]
    have hAB : conjLinEquiv hQn (l : C) * conjLinEquiv hQn t =
        conjLinEquiv hQn t * conjLinEquiv hQn (l : C) := by
      conv_lhs => rw [hconj]
      group
    exact hAB
  obtain ⟨T, htT, hS1', hS2'⟩ := hC.exists_sylow_meets_factors θ hθs hθk ht.1 ht.2.1
  let S : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    Subgroup.map θ (Subgroup.comap (commutator C).subtype (T : Subgroup C))
  have hS1 : ∃ x : alternatingGroup (Fin 5), x ≠ 1 ∧ (x, 1) ∈ S := by
    obtain ⟨x, hx1, l, hlT, hlθ⟩ := hS1'
    exact ⟨x, hx1, Subgroup.mem_map.mpr ⟨l, Subgroup.mem_comap.mpr hlT, hlθ⟩⟩
  have hS2 : ∃ y : alternatingGroup (Fin 5), y ≠ 1 ∧ (1, y) ∈ S := by
    obtain ⟨y, hy1, l, hlT, hlθ⟩ := hS2'
    exact ⟨y, hy1, Subgroup.mem_map.mpr ⟨l, Subgroup.mem_comap.mpr hlT, hlθ⟩⟩
  obtain ⟨x, hxQ, hxs, hxt⟩ := ht.2.2 T htT
  let w : Additive (Abelianization Q) := Additive.ofMul (Abelianization.of (⟨x, hxQ⟩ : Q))
  have hfix : ∀ g : C, g ∈ (T : Subgroup C) → g ∈ commutator C →
      conjLinEquiv hQn g w = w := by
    intro g hgT hgL
    have hc : ⁅x, g⁆ ∈ centerOf Q := hxs g ⟨hgT, hgL⟩
    have hc' : ⁅g, x⁆ ∈ centerOf Q := by
      rw [← commutatorElement_inv x g]
      exact (centerOf Q).inv_mem hc
    have h := (extraspecialConjOrth_apply_eq_iff hE g ⟨x, hxQ⟩).2 hc'
    have hcoe : conjLinEquiv hQn g =
        (extraspecialConjOrth hE hQn g :
          Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) := rfl
    rw [hcoe]
    simpa [w] using h
  have hw : ∀ s ∈ S, σ s w = w := by
    intro s hs
    obtain ⟨l, hlT, hlθ⟩ := Subgroup.mem_map.mp hs
    have hlT' : (l : C) ∈ (T : Subgroup C) := hlT
    have hσs : σ s = conjLinEquiv hQn (l : C) := by rw [← hlθ, hσθ l]
    rw [hσs]
    exact hfix (l : C) hlT' l.2
  have hbw : b w ≠ w := by
    intro h
    have hcoe : conjLinEquiv hQn t =
        (extraspecialConjOrth hE hQn t :
          Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) := rfl
    have h' : conjLinEquiv hQn t
        (Additive.ofMul (Abelianization.of (⟨x, hxQ⟩ : Q))) =
        Additive.ofMul (Abelianization.of (⟨x, hxQ⟩ : Q)) := h
    rw [hcoe] at h'
    exact hxt ((extraspecialConjOrth_apply_eq_iff hE t ⟨x, hxQ⟩).1 h')
  have hbS : ∀ s ∈ S, σ s (b w) = b w := by
    intro s hs
    obtain ⟨l, hlT, hlθ⟩ := Subgroup.mem_map.mp hs
    have hlT' : (l : C) ∈ (T : Subgroup C) := hlT
    have hgT : t⁻¹ * (l : C) * t ∈ (T : Subgroup C) :=
      (T : Subgroup C).mul_mem
        ((T : Subgroup C).mul_mem ((T : Subgroup C).inv_mem htT) hlT') htT
    have hgL : t⁻¹ * (l : C) * t ∈ commutator C := by
      simpa using (inferInstance : (commutator C).Normal).conj_mem (l : C) l.2 t⁻¹
    have hσs : σ s = conjLinEquiv hQn (l : C) := by rw [← hlθ, hσθ l]
    rw [hσs]
    calc conjLinEquiv hQn (l : C) (b w)
        = conjLinEquiv hQn (l : C) (conjLinEquiv hQn t w) := by
            rw [show b = conjLinEquiv hQn t from rfl]
      _ = conjLinEquiv hQn ((l : C) * t) w := by rw [map_mul, LinearEquiv.mul_apply]
      _ = conjLinEquiv hQn (t * (t⁻¹ * (l : C) * t)) w := by
            rw [show (l : C) * t = t * (t⁻¹ * (l : C) * t) from by group]
      _ = conjLinEquiv hQn t (conjLinEquiv hQn (t⁻¹ * (l : C) * t) w) := by
            rw [map_mul, LinearEquiv.mul_apply]
      _ = conjLinEquiv hQn t w := by rw [hfix (t⁻¹ * (l : C) * t) hgT hgL]
      _ = b w := by rw [show b = conjLinEquiv hQn t from rfl]
  exact Free.four_le_finrank_range_of_fixed σ hσi hirr b hb x₀ hcomm S hS1 hS2 w hw hbw hbS

end CFSG.EvenSporadicStandard.HNRecog

module

public import CFSG.ClassicalGroups.Orthogonal.Transitive
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {W : Submodule K V}

theorem polar_restrict (x y : W) : polar (Q.restrict W) x y = polar Q x y := by
  simp [polar, QuadraticMap.restrict_apply]

theorem restrict_apply' (x : W) : Q.restrict W x = Q x := rfl

theorem nondegenerate_polarBilin_restrict (hW : PolarNondegOn Q W) :
    (polarBilin (Q.restrict W)).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    exact hW x x.2 fun y hy => by simpa [polar_restrict] using hx ⟨y, hy⟩
  · intro y hy
    apply Subtype.ext
    refine hW y y.2 fun x hx => ?_
    rw [polar_comm]
    simpa [polar_restrict] using hy ⟨x, hx⟩

def HypPair.restrict (P : HypPair Q) (he : P.e ∈ W) (hf : P.f ∈ W) :
    HypPair (Q.restrict W) where
  e := ⟨P.e, he⟩
  f := ⟨P.f, hf⟩
  Q_e := P.Q_e
  Q_f := P.Q_f
  polar_ef := by rw [polar_restrict]; exact P.polar_ef

theorem HypPair.Orth.restrict {P P' : HypPair Q} (h : P.Orth P') (he : P.e ∈ W) (hf : P.f ∈ W)
    (he' : P'.e ∈ W) (hf' : P'.f ∈ W) : (P.restrict he hf).Orth (P'.restrict he' hf') where
  ee := by rw [polar_restrict]; exact h.ee
  ef := by rw [polar_restrict]; exact h.ef
  fe := by rw [polar_restrict]; exact h.fe
  ff := by rw [polar_restrict]; exact h.ff

theorem exists_extend_of_mem_elementaryGroup_restrict {g' : W ≃ₗ[K] W}
    (hg' : g' ∈ elementaryGroup (Q.restrict W)) :
    ∃ g ∈ elementaryGroup Q, (∀ x : W, g x = g' x) ∧
      ∀ z, (∀ x ∈ W, polar Q z x = 0) → g z = z := by
  induction hg' using Subgroup.closure_induction with
  | mem g' hg' =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hg'
    have hu' : Q u = 0 := hu
    have hw' : polar Q u w = 0 := by rwa [polar_restrict] at hw
    refine ⟨eichler Q u w, eichler_mem_elementaryGroup Q _ _, fun x => ?_, fun z hz => ?_⟩
    · rw [eichler_apply hu' hw', eichler_apply hu hw]
      simp [polar_restrict]
    · exact eichler_apply_of_polar_eq_zero (hz u u.2) (hz w w.2)
  | one => exact ⟨1, one_mem _, fun x => rfl, fun z _ => rfl⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨g, hg, hgx, hgz⟩ := iha
    obtain ⟨h, hh, hhx, hhz⟩ := ihb
    refine ⟨g * h, mul_mem hg hh, fun x => ?_, fun z hz => ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hhx, hgx]
    · rw [LinearEquiv.mul_apply, hhz z hz, hgz z hz]
  | inv a _ iha =>
    obtain ⟨g, hg, hgx, hgz⟩ := iha
    refine ⟨g⁻¹, inv_mem hg, fun x => ?_, fun z hz => ?_⟩
    · apply g.injective
      rw [LinearEquiv.apply_inv_apply', hgx, LinearEquiv.apply_inv_apply']
    · apply g.injective
      rw [LinearEquiv.apply_inv_apply', hgz z hz]

theorem exists_mem_elementaryGroup_apply_eq_of_mem (hW : PolarNondegOn Q W) {P P' : HypPair Q}
    (h : P.Orth P') (he : P.e ∈ W) (hf : P.f ∈ W) (he' : P'.e ∈ W) (hf' : P'.f ∈ W) {x y : V}
    (hxW : x ∈ W) (hyW : y ∈ W) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Q x = Q y) :
    ∃ g ∈ elementaryGroup Q, g x = y ∧ (∀ w ∈ W, g w ∈ W) ∧
      ∀ z, (∀ w ∈ W, polar Q z w = 0) → g z = z := by
  obtain ⟨g', hg', hg'x⟩ := exists_mem_elementaryGroup_apply_eq
    (nondegenerate_polarBilin_restrict hW) (h.restrict he hf he' hf')
    (x := ⟨x, hxW⟩) (y := ⟨y, hyW⟩) (fun h0 => hx (congrArg Subtype.val h0))
    (fun h0 => hy (congrArg Subtype.val h0)) hxy
  obtain ⟨g, hg, hgW, hgz⟩ := exists_extend_of_mem_elementaryGroup_restrict hg'
  refine ⟨g, hg, ?_, fun w hw => ?_, hgz⟩
  · have := hgW ⟨x, hxW⟩
    rw [hg'x] at this
    exact this
  · rw [show w = ((⟨w, hw⟩ : W) : V) from rfl, hgW]
    exact (g' ⟨w, hw⟩).2

end CFSG.ClassicalGroups.Orthogonal

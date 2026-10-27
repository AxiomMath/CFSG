module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSevenPair
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace OmSeven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem polarNondegOn_span_pair (h3 : (3 : K) ≠ 0) {Q : QuadraticForm K V} {x y : V}
    (hxy : Q x = Q y) (hB : polar Q x y = Q y) (hy : Q y ≠ 0) :
    PolarNondegOn Q (Submodule.span K {x, y}) := by
  intro p hp hp0
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hp
  have hx' : x ∈ Submodule.span K {x, y} := Submodule.subset_span (by simp)
  have hy' : y ∈ Submodule.span K {x, y} := Submodule.subset_span (by simp)
  have e1 := hp0 x hx'
  have e2 := hp0 y hy'
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_self_eq_two_mul,
    polar_comm Q y x, hB, hxy] at e1
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_self_eq_two_mul, hB] at e2
  have hc : (3 : K) * Q y ≠ 0 := mul_ne_zero h3 hy
  have ha : a = 0 := by
    have : ((3 : K) * Q y) * a = 0 := by linear_combination 2 * e1 - e2
    exact (mul_eq_zero.1 this).resolve_left hc
  have hb : b = 0 := by
    have : ((3 : K) * Q y) * b = 0 := by linear_combination 2 * e2 - e1
    exact (mul_eq_zero.1 this).resolve_left hc
  rw [ha, hb, zero_smul, zero_smul, add_zero]

theorem restrict_polarBilin_nondegenerate {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : PolarNondegOn Q W) : (LinearMap.BilinForm.restrict (polarBilin Q) W).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    refine hW x x.2 fun y hy => ?_
    have := hx ⟨y, hy⟩
    simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      polarBilin_apply_apply] using this
  · intro y hy
    apply Subtype.ext
    refine hW y y.2 fun x hx => ?_
    rw [polar_comm]
    have := hy ⟨x, hx⟩
    simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      polarBilin_apply_apply] using this

theorem exists_complement_of_goodPair [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1) {x y : V}
    (hxy : GoodPair Q g x y) :
    ∃ U : Submodule K V, PolarNondegOn Q U ∧ (∀ u ∈ U, polar Q x u = 0 ∧ polar Q y u = 0) ∧
      (∀ u ∈ U, g u ∈ U) ∧ Module.finrank K V ≤ Module.finrank K U + 2 := by
  classical
  obtain ⟨hQe, hB, hy, hg'⟩ := hxy
  set P : Submodule K V := Submodule.span K {x, y} with hP
  have hPnd : PolarNondegOn Q P := polarNondegOn_span_pair h3 hQe hB hy
  have hx' : x ∈ P := Submodule.subset_span (by simp)
  have hy' : y ∈ P := Submodule.subset_span (by simp)
  have hPg : ∀ p ∈ P, g p ∈ P := by
    intro p hp
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hp
    rw [map_add, map_smul, map_smul]
    rcases hg' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact P.add_mem (P.smul_mem a hx') (P.smul_mem b hy')
    · rw [h1, h2]
      exact P.add_mem (P.smul_mem a (P.neg_mem hy')) (P.smul_mem b (P.sub_mem hx' hy'))
  have hcompl : IsCompl P (LinearMap.BilinForm.orthogonal (polarBilin Q) P) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (QuadraticMap.isSymm_polarBilin Q).isRefl (restrict_polarBilin_nondegenerate hPnd)
  set U := LinearMap.BilinForm.orthogonal (polarBilin Q) P with hU
  have hUperp : ∀ u ∈ U, ∀ p ∈ P, polar Q p u = 0 := fun u hu p hp => by
    have := (LinearMap.BilinForm.mem_orthogonal_iff.1 hu) p hp
    simpa [LinearMap.BilinForm.isOrtho_def, polarBilin_apply_apply] using this
  refine ⟨U, ?_, fun u hu => ⟨hUperp u hu x hx', hUperp u hu y hy'⟩, ?_, ?_⟩
  · intro u hu hu0
    apply eq_zero_of_polar_eq_zero hQ
    intro v
    obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.1
      (hcompl.sup_eq_top ▸ Submodule.mem_top : v ∈ P ⊔ U)
    rw [polar_add_right, hu0 w hw, polar_comm Q u p, hUperp u hu p hp, add_zero]
  · intro u hu
    refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun p hp => ?_
    rw [polarBilin_apply_apply]
    have hg3' := apply_apply_apply_of_pow_three hg3
    have := polar_map_of_mem hg (g (g p)) u
    rw [hg3'] at this
    rw [this]
    exact hUperp u hu _ (hPg _ (hPg _ hp))
  · have h1 := Submodule.finrank_add_eq_of_isCompl hcompl
    have h2 : Module.finrank K P ≤ 2 := by
      have h := finrank_span_finset_le_card (R := K) ({x, y} : Finset V)
      have h' : (({x, y} : Finset V) : Set V) = {x, y} := by simp
      rw [Set.finrank, h'] at h
      exact h.trans Finset.card_le_two
    omega

end OmSeven

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

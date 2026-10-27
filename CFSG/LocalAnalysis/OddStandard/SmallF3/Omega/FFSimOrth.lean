module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimRep
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ff_aux_radical_restrict_polar {W : Submodule (ZMod 3) V} {x : W}
    (hx : x ∈ (Q.restrict W).radical) (y : W) : polar Q (x : V) (y : V) = 0 := by
  have hx1 : Q (x : V) = 0 := (QuadraticMap.mem_radical_iff'.mp hx).1
  have hkey : Q ((x : V) + (y : V)) = Q (y : V) :=
    (QuadraticMap.mem_radical_iff'.mp hx).2 y
  rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq Q (x : V) (y : V), hx1,
    zero_add] at hkey
  have h : Q (y : V) + polar Q (x : V) (y : V) = Q (y : V) + 0 := by rw [hkey, add_zero]
  exact add_left_cancel h

theorem ff_restrict_nondegenerate_single {u : V} (hu : Q u ≠ 0) :
    (Q.restrict (Submodule.span (ZMod 3) {u})).Nondegenerate := by
  let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) {u}
  let v : W := ⟨u, Submodule.mem_span_singleton_self u⟩
  have hspan : Submodule.span (ZMod 3) {v} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro z
    rw [Submodule.mem_span_singleton]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp z.2
    exact ⟨c, Subtype.ext (by simpa [v] using hc)⟩
  have hv : (Q.restrict W) v ≠ 0 := by
    simpa only [QuadraticMap.restrict_apply, v] using hu
  exact TauCeti.nondegenerate_of_span_singleton_eq_top hspan hv

theorem ff_restrict_nondegenerate_pair {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (huv : polar Q u v = 0) : (Q.restrict (Submodule.span (ZMod 3) {u, v})).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.2
  have hxu : polar Q u (x : V) = 0 := by
    rw [polar_comm]
    exact ff_aux_radical_restrict_polar hx ⟨u, Submodule.subset_span (by simp)⟩
  have hxv : polar Q v (x : V) = 0 := by
    rw [polar_comm]
    exact ff_aux_radical_restrict_polar hx ⟨v, Submodule.subset_span (by simp)⟩
  have ha : a = 0 := by
    have h : polar Q u (a • u + b • v) = 0 := by rw [hab]; exact hxu
    rw [polar_add_right, polar_smul_right, polar_smul_right, huv, smul_zero, add_zero,
      polar_self, smul_eq_mul, nsmul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero (by decide) hu)
  have hb : b = 0 := by
    have h : polar Q v (a • u + b • v) = 0 := by rw [hab]; exact hxv
    rw [polar_add_right, polar_smul_right, polar_smul_right, polar_comm Q v u, huv,
      smul_zero, zero_add, polar_self, smul_eq_mul, nsmul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero (by decide) hv)
  apply Subtype.ext
  simp [← hab, ha, hb]

theorem ff_finrank_span_pair {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0) (huv : polar Q u v = 0) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {u, v}) = 2 := by
  have hli : LinearIndependent (ZMod 3) ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : s = 0 := by
      have h := congrArg (polar Q u) hst
      rw [polar_add_right, polar_smul_right, polar_smul_right, huv, smul_zero, add_zero,
        polar_zero_right, polar_self, smul_eq_mul, nsmul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero (by decide) hu)
    have ht : t = 0 := by
      have h := congrArg (polar Q v) hst
      rw [polar_add_right, polar_smul_right, polar_smul_right, polar_comm Q v u, huv,
        smul_zero, zero_add, polar_zero_right, polar_self, smul_eq_mul, nsmul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero (by decide) hv)
    exact ⟨hs, ht⟩
  have hrange : Set.range ![u, v] = ({u, v} : Set V) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have h := finrank_span_eq_card hli
  rw [hrange] at h
  simpa using h

theorem ff_mem_orth_pair_iff {u v w : V} :
    w ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span (ZMod 3) {u, v}) ↔
      polar Q u w = 0 ∧ polar Q v w = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨by simpa using h u (Submodule.subset_span (by simp)),
      by simpa using h v (Submodule.subset_span (by simp))⟩
  · rintro ⟨hu, hv⟩ n hn
    rw [Submodule.mem_span_pair] at hn
    obtain ⟨a, b, rfl⟩ := hn
    rw [QuadraticMap.polarBilin_apply_apply, polar_add_left, polar_smul_left, polar_smul_left,
      hu, hv, smul_zero, smul_zero, add_zero]

theorem ff_finrank_orth_pair (hQ : Q.Nondegenerate) {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (huv : polar Q u v = 0) :
    Module.finrank (ZMod 3)
        (LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span (ZMod 3) {u, v})) + 2 =
      Module.finrank (ZMod 3) V := by
  have hB : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hfr := LinearMap.BilinForm.finrank_orthogonal (B := Q.polarBilin) hB
    (Submodule.span (ZMod 3) {u, v})
  have hle : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {u, v}) ≤
      Module.finrank (ZMod 3) V := Submodule.finrank_le _
  rw [ff_finrank_span_pair hu hv huv] at hfr hle
  omega

theorem ff_exists_orth_single_pair (hQ : Q.Nondegenerate) (h4 : 4 ≤ Module.finrank (ZMod 3) V)
    {u : V} (hu : Q u ≠ 0) {d : ZMod 3} (hd : d ≠ 0) :
    ∃ w₁ w₂ : V, polar Q u w₁ = 0 ∧ polar Q u w₂ = 0 ∧ Q w₁ = d ∧ Q w₂ = d ∧
      LinearIndependent (ZMod 3) ![w₁, w₂] := by
  classical
  have hB : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  set W1 : Submodule (ZMod 3) V :=
    LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span (ZMod 3) {u}) with hW1
  have hW1nd : (Q.restrict W1).Nondegenerate := by
    rw [hW1]
    exact QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal hQ
      (ff_restrict_nondegenerate_single hu)
  have hu0 : u ≠ 0 := fun h => hu (by rw [h, map_zero])
  have hfr : Module.finrank (ZMod 3) W1 = Module.finrank (ZMod 3) V - 1 := by
    rw [hW1, LinearMap.BilinForm.finrank_orthogonal hB, finrank_span_singleton hu0]
  have h3 : 3 ≤ Module.finrank (ZMod 3) W1 := by rw [hfr]; omega
  obtain ⟨w1, w2, hw1, hw2, hli⟩ :=
    ff_exists_pair_eq_of_nondegenerate (R := Q.restrict W1) hW1nd h3 hd
  have hmem1 : polar Q u (w1 : V) = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp w1.2) u
      (Submodule.mem_span_singleton_self u)
    simpa only [QuadraticMap.polarBilin_apply_apply] using h
  have hmem2 : polar Q u (w2 : V) = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp w2.2) u
      (Submodule.mem_span_singleton_self u)
    simpa only [QuadraticMap.polarBilin_apply_apply] using h
  refine ⟨(w1 : V), (w2 : V), hmem1, hmem2, ?_, ?_, ?_⟩
  · simpa only [QuadraticMap.restrict_apply] using hw1
  · simpa only [QuadraticMap.restrict_apply] using hw2
  · have hliV : LinearIndependent (ZMod 3) ![(w1 : V), (w2 : V)] := by
      have hmap := hli.map' W1.subtype (by rw [Submodule.ker_subtype])
      convert hmap using 1
      funext i
      fin_cases i <;> rfl
    exact hliV

theorem ff_exists_orth_pair_nonsingular (hQ : Q.Nondegenerate)
    (h4 : 4 ≤ Module.finrank (ZMod 3) V) {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0)
    (hxy : polar Q x y = 0) : ∃ z : V, polar Q x z = 0 ∧ polar Q y z = 0 ∧ Q z ≠ 0 := by
  classical
  set W2 : Submodule (ZMod 3) V :=
    LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span (ZMod 3) {x, y}) with hW2
  have hW2nd : (Q.restrict W2).Nondegenerate := by
    rw [hW2]
    exact QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal hQ
      (ff_restrict_nondegenerate_pair hx hy hxy)
  have hfr := ff_finrank_orth_pair hQ hx hy hxy
  have h2 : 2 ≤ Module.finrank (ZMod 3) W2 := by rw [hW2]; omega
  obtain ⟨z, hz⟩ := ff_exists_eq_of_nondegenerate (R := Q.restrict W2) hW2nd h2
    (by decide : (1 : ZMod 3) ≠ 0)
  have hzmem : (z : V) ∈ LinearMap.BilinForm.orthogonal Q.polarBilin
      (Submodule.span (ZMod 3) {x, y}) := by rw [← hW2]; exact z.2
  obtain ⟨hzx, hzy⟩ := ff_mem_orth_pair_iff.mp hzmem
  refine ⟨(z : V), hzx, hzy, ?_⟩
  have hzq : Q (z : V) = 1 := by simpa only [QuadraticMap.restrict_apply] using hz
  rw [hzq]; exact one_ne_zero

end CFSG.OddStandard.SmallF3.Omega

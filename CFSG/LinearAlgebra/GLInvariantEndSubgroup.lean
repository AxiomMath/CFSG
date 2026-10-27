module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.GL4Vanish
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

public section

namespace CFSG.LinearAlgebra

open Module Submodule
open CFSG.GroupTheory.GLnTwoSplitting

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private lemma transvection_apply' (φ : Dual (ZMod 2) V) {w : V} (h : φ w = 0) (x : V) :
    LinearEquiv.transvection h x = x + φ x • w := rfl

private lemma transvection_toLin (φ : Dual (ZMod 2) V) {w : V} (h : φ w = 0) :
    (LinearEquiv.transvection h).toLinearMap = LinearMap.id + φ.smulRight w := by
  ext x
  rw [LinearEquiv.coe_toLinearMap]
  change LinearEquiv.transvection h x = _
  rw [transvection_apply', LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply]

private lemma transvection_symm (φ : Dual (ZMod 2) V) {w : V} (h : φ w = 0) :
    (LinearEquiv.transvection h).symm.toLinearMap = (LinearEquiv.transvection h).toLinearMap := by
  have h' : (LinearEquiv.transvection h).symm = LinearEquiv.transvection h := transvection_inv h
  rw [h']

private lemma transvection_conj_sub (f : V →ₗ[ZMod 2] V) (φ : Dual (ZMod 2) V) {w : V}
    (h : φ w = 0) :
    (LinearEquiv.transvection h).toLinearMap ∘ₗ f ∘ₗ
        (LinearEquiv.transvection h).symm.toLinearMap - f =
      (φ.comp f).smulRight w + φ.smulRight (f w + φ (f w) • w) := by
  ext x
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    transvection_symm, transvection_toLin]
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, map_add, map_smul, h, smul_zero, add_zero]
  abel

private lemma conjSub_apply (f : V →ₗ[ZMod 2] V) (φ : Dual (ZMod 2) V) {w : V}
    (h : φ w = 0) (x : V) :
    ((LinearEquiv.transvection h).toLinearMap ∘ₗ f ∘ₗ
        (LinearEquiv.transvection h).symm.toLinearMap - f) x =
      φ (f x) • w + φ x • (f w + φ (f w) • w) := by
  rw [transvection_conj_sub f φ h]
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]

private lemma conjSub_apply_self (f : V →ₗ[ZMod 2] V) (φ : Dual (ZMod 2) V) {w : V}
    (h : φ w = 0) :
    ((LinearEquiv.transvection h).toLinearMap ∘ₗ f ∘ₗ
        (LinearEquiv.transvection h).symm.toLinearMap - f) w = φ (f w) • w := by
  rw [conjSub_apply, h]
  simp

private lemma range_conjSub_le_span_pair (f : V →ₗ[ZMod 2] V) (φ : Dual (ZMod 2) V) {w : V}
    (h : φ w = 0) :
    LinearMap.range ((LinearEquiv.transvection h).toLinearMap ∘ₗ f ∘ₗ
        (LinearEquiv.transvection h).symm.toLinearMap - f) ≤
      Submodule.span (ZMod 2) ({w, f w} : Set V) := by
  rintro y ⟨x, rfl⟩
  rw [conjSub_apply]
  have h1 : φ (f x) • w ∈ Submodule.span (ZMod 2) ({w, f w} : Set V) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have h2 : f w + φ (f w) • w ∈ Submodule.span (ZMod 2) ({w, f w} : Set V) := by
    exact Submodule.add_mem _
      (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

private lemma exists_smulRight_of_range_le_span {r : V →ₗ[ZMod 2] V} {u : V}
    (hu : u ≠ 0) (hrange : LinearMap.range r ≤ Submodule.span (ZMod 2) ({u} : Set V)) :
    ∃ ψ : Dual (ZMod 2) V, r = ψ.smulRight u := by
  classical
  obtain ⟨φ, hφu, -⟩ := CFSG.EvenSporadicStandard.ThStd.exists_dual_one_of_notMem
    (p := (⊥ : Submodule (ZMod 2) V)) (v := u) (by simpa using hu)
  refine ⟨φ.comp r, ?_⟩
  ext x
  have hrx : r x ∈ Submodule.span (ZMod 2) ({u} : Set V) := hrange ⟨x, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hrx
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, ← hc, map_smul, hφu, smul_eq_mul,
    mul_one]

private lemma exists_mem_notMem_span_of_card_lt [FiniteDimensional (ZMod 2) V]
    {U : Submodule (ZMod 2) V} {s : Finset V}
    (hs : ∀ x ∈ s, x ∈ U) (hcard : s.card < finrank (ZMod 2) U) :
    ∃ v ∈ U, v ∉ Submodule.span (ZMod 2) (s : Set V) := by
  by_contra hcon
  push Not at hcon
  have hle : U ≤ Submodule.span (ZMod 2) (s : Set V) := fun x hx => hcon x hx
  have h1 : finrank (ZMod 2) U ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (s : Set V)) :=
    Submodule.finrank_mono hle
  have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) (s : Set V)) ≤ s.card :=
    finrank_span_finset_le_card s
  omega

private lemma linearIndependent_three_of_notMem {w e2 e3 : V}
    (hw : w ≠ 0) (he2 : e2 ∉ Submodule.span (ZMod 2) ({w} : Set V))
    (he3 : e3 ∉ Submodule.span (ZMod 2) ({w, e2} : Set V)) :
    LinearIndependent (ZMod 2) ![w, e2, e3] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_three] at hg
  change g 0 • w + g 1 • e2 + g 2 • e3 = 0 at hg
  have hg2 : g 2 = 0 := by
    by_contra h2
    rw [zmod_two_eq_one_of_ne_zero h2, one_smul] at hg
    apply he3
    rw [Submodule.mem_span_pair]
    have h' : g 0 • w + g 1 • e2 + e3 = 0 := by simpa [add_assoc] using hg
    have hneg : e3 = -(g 0 • w + g 1 • e2) := eq_neg_of_add_eq_zero_right h'
    rw [two_neg] at hneg
    exact ⟨g 0, g 1, hneg.symm⟩
  have hg1 : g 1 = 0 := by
    by_contra h1
    rw [hg2, zmod_two_eq_one_of_ne_zero h1, one_smul] at hg
    simp only [zero_smul, add_zero] at hg
    apply he2
    rw [Submodule.mem_span_singleton]
    have hneg : e2 = -(g 0 • w) := eq_neg_of_add_eq_zero_right hg
    rw [two_neg] at hneg
    exact ⟨g 0, hneg.symm⟩
  have hg0 : g 0 = 0 := by
    by_contra h0
    rw [hg1, hg2] at hg
    simp only [zero_smul, add_zero] at hg
    rw [zmod_two_eq_one_of_ne_zero h0, one_smul] at hg
    exact hw hg
  fin_cases i <;> assumption

private lemma linearIndependent_four_of_three {w y e2 e3 : V} (ψ : Dual (ZMod 2) V)
    (hψw : ψ w = 0) (hψy : ψ y = 1) (hψe2 : ψ e2 = 0) (hψe3 : ψ e3 = 0)
    (h3 : LinearIndependent (ZMod 2) ![w, e2, e3]) :
    LinearIndependent (ZMod 2) ![w, y, e2, e3] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_four] at hg
  change g 0 • w + g 1 • y + g 2 • e2 + g 3 • e3 = 0 at hg
  have hg1 : g 1 = 0 := by
    have h := congrArg ψ hg
    simpa [map_add, map_smul, hψw, hψy, hψe2, hψe3] using h
  rw [hg1] at hg
  simp only [zero_smul, add_zero] at hg
  have h3sum : (∑ i, (![g 0, g 2, g 3] : Fin 3 → ZMod 2) i • ![w, e2, e3] i) = 0 := by
    rw [Fin.sum_univ_three]
    simpa using hg
  have hvals := (Fintype.linearIndependent_iff.1 h3) ![g 0, g 2, g 3] h3sum
  have hg0 : g 0 = 0 := hvals 0
  have hg2 : g 2 = 0 := hvals 1
  have hg3 : g 3 = 0 := hvals 2
  fin_cases i <;> assumption

private lemma exists_basis_of_nilpotent [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 4) {ψ : Dual (ZMod 2) V} {w : V}
    (hψ : ψ ≠ 0) (hw : w ≠ 0) (hψw : ψ w = 0) :
    ∃ b : Basis (Fin 4) (ZMod 2) V, b 0 = w ∧ b.coord 1 = ψ := by
  classical
  have hker_ge : 3 ≤ finrank (ZMod 2) (LinearMap.ker ψ) := by
    have h := finrank_ker_add_one_ge ψ
    omega
  have hker_ne_top : LinearMap.ker ψ ≠ ⊤ := by
    intro htop
    apply hψ
    ext x
    have hx : x ∈ LinearMap.ker ψ := by rw [htop]; trivial
    simpa using hx
  have hker_lt : finrank (ZMod 2) (LinearMap.ker ψ) < 4 := by
    simpa [hV] using Submodule.finrank_lt hker_ne_top
  have hker3 : finrank (ZMod 2) (LinearMap.ker ψ) = 3 := by omega
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (LinearMap.ext h)
  have hy1 : ψ y = 1 := zmod_two_eq_one_of_ne_zero hy
  have hwker : w ∈ LinearMap.ker ψ := LinearMap.mem_ker.2 hψw
  obtain ⟨e2, he2ker, he2span⟩ := exists_mem_notMem_span_of_card_lt
    (U := LinearMap.ker ψ) (s := ({w} : Finset V))
    (by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst x
      exact hwker)
    (by rw [Finset.card_singleton, hker3]; omega)
  have hwne2 : w ≠ e2 := by
    intro h
    apply he2span
    rw [h]
    exact Submodule.subset_span (by simp)
  obtain ⟨e3, he3ker, he3span⟩ := exists_mem_notMem_span_of_card_lt
    (U := LinearMap.ker ψ) (s := ({w, e2} : Finset V))
    (by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hwker
      · exact he2ker)
    (by rw [Finset.card_pair hwne2, hker3]; omega)
  have hψe2 : ψ e2 = 0 := LinearMap.mem_ker.1 he2ker
  have hψe3 : ψ e3 = 0 := LinearMap.mem_ker.1 he3ker
  have he2span' : e2 ∉ Submodule.span (ZMod 2) ({w} : Set V) := by simpa using he2span
  have he3span' : e3 ∉ Submodule.span (ZMod 2) ({w, e2} : Set V) := by simpa using he3span
  have htriple : LinearIndependent (ZMod 2) ![w, e2, e3] :=
    linearIndependent_three_of_notMem hw he2span' he3span' 
  have hquad : LinearIndependent (ZMod 2) ![w, y, e2, e3] :=
    linearIndependent_four_of_three ψ hψw hy1 hψe2 hψe3 htriple
  let b : Basis (Fin 4) (ZMod 2) V :=
    basisOfLinearIndependentOfCardEqFinrank hquad (by simp [hV])
  have hb0 : b 0 = w := by simp [b, basisOfLinearIndependentOfCardEqFinrank]
  have hb1 : b 1 = y := by simp [b, basisOfLinearIndependentOfCardEqFinrank]
  have hb2 : b 2 = e2 := by simp [b, basisOfLinearIndependentOfCardEqFinrank]
  have hb3 : b 3 = e3 := by simp [b, basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨b, hb0, ?_⟩
  apply Module.Basis.ext b
  intro i
  rw [Module.Basis.coord_apply]
  fin_cases i
  · change (b.repr (b 0)) 1 = ψ (b 0)
    rw [Module.Basis.repr_self_apply]
    simp [show ψ (b 0) = 0 from by rw [hb0, hψw]]
  · change (b.repr (b 1)) 1 = ψ (b 1)
    rw [Module.Basis.repr_self_apply]
    simp [show ψ (b 1) = 1 from by rw [hb1, hy1]]
  · change (b.repr (b 2)) 1 = ψ (b 2)
    rw [Module.Basis.repr_self_apply]
    simp [show ψ (b 2) = 0 from by rw [hb2, hψe2]]
  · change (b.repr (b 3)) 1 = ψ (b 3)
    rw [Module.Basis.repr_self_apply]
    simp [show ψ (b 3) = 0 from by rw [hb3, hψe3]]

private lemma coord_self (b : Basis (Fin 4) (ZMod 2) V) (i : Fin 4) :
    b.coord i (b i) = 1 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply b i i]
  simp

private lemma coord_of_ne (b : Basis (Fin 4) (ZMod 2) V) {i j : Fin 4} (h : i ≠ j) :
    b.coord i (b j) = 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply b j i, if_neg (Ne.symm h)]

private lemma neg_eq_self_zmod2 (a : ZMod 2) : -a = a := by
  have h : a + a = 0 := zmod_two_add_self a
  exact neg_eq_of_add_eq_zero_left h

private noncomputable abbrev E (b : Basis (Fin 4) (ZMod 2) V) (i j : Fin 4) : V →ₗ[ZMod 2] V :=
  (b.coord j).smulRight (b i)

private lemma conjSub_E01 (b : Basis (Fin 4) (ZMod 2) V) (j : Fin 4) (hj0 : j ≠ 0)
    (hj1 : j ≠ 1) :
    (LinearEquiv.transvection (coord_of_ne b hj1)).toLinearMap ∘ₗ E b 0 1 ∘ₗ
        (LinearEquiv.transvection (coord_of_ne b hj1)).symm.toLinearMap - E b 0 1 = E b 0 j := by
  classical
  rw [transvection_conj_sub]
  ext x
  simp [E, LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
    Ne.symm hj0, Ne.symm hj1]

private lemma conjSub_E0j (b : Basis (Fin 4) (ZMod 2) V) (i j : Fin 4) (hi0 : i ≠ 0)
    (hij : i ≠ j) :
    (LinearEquiv.transvection (coord_of_ne b (Ne.symm hi0))).toLinearMap ∘ₗ E b 0 j ∘ₗ
        (LinearEquiv.transvection (coord_of_ne b (Ne.symm hi0))).symm.toLinearMap - E b 0 j = E b i j := by
  classical
  rw [transvection_conj_sub]
  ext x
  simp [E, LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
    hi0, hij]


private noncomputable def swap01 (b : Basis (Fin 4) (ZMod 2) V) : V ≃ₗ[ZMod 2] V :=
  b.equiv b (Equiv.swap (0 : Fin 4) 1)

private lemma swap01_symm (b : Basis (Fin 4) (ZMod 2) V) : (swap01 b).symm = swap01 b := by
  rw [swap01, Module.Basis.equiv_symm]
  have h : (Equiv.swap (0 : Fin 4) 1).symm = Equiv.swap (0 : Fin 4) 1 := by
    ext i
    simp [Equiv.swap_apply_def]
  rw [h]

private lemma swap01_apply (b : Basis (Fin 4) (ZMod 2) V) (i : Fin 4) :
    swap01 b (b i) = b (Equiv.swap (0 : Fin 4) 1 i) := by
  simpa [swap01] using Module.Basis.equiv_apply b i b (Equiv.swap (0 : Fin 4) 1)

private lemma conj_swap_E01 (b : Basis (Fin 4) (ZMod 2) V) :
    (swap01 b).toLinearMap ∘ₗ E b 0 1 ∘ₗ (swap01 b).symm.toLinearMap = E b 1 0 := by
  classical
  apply Module.Basis.ext b
  intro i
  rw [LinearMap.comp_apply, LinearMap.comp_apply, swap01_symm]
  simp only [LinearEquiv.coe_toLinearMap]
  rw [swap01_apply, LinearMap.smulRight_apply, map_smul, swap01_apply,
    LinearMap.smulRight_apply]
  fin_cases i <;> simp [E, coord_self, coord_of_ne, Equiv.swap_apply_def]

private lemma conjSub_E10_Ei0 (b : Basis (Fin 4) (ZMod 2) V) (i : Fin 4)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    (LinearEquiv.transvection (coord_of_ne b (Ne.symm hi1))).toLinearMap ∘ₗ E b 1 0 ∘ₗ
        (LinearEquiv.transvection (coord_of_ne b (Ne.symm hi1))).symm.toLinearMap -
      E b 1 0 = E b i 0 := by
  classical
  rw [transvection_conj_sub]
  ext x
  simp [E, LinearMap.smulRight_apply, coord_self, coord_of_ne, hi0, hi1]

private abbrev OffDiag := {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2}

private lemma linearIndependent_offDiag (b : Basis (Fin 4) (ZMod 2) V) :
    LinearIndependent (ZMod 2) (fun p : OffDiag => E b p.1.1 p.1.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have h := congrArg (fun f : V →ₗ[ZMod 2] V => b.coord p.1.1 (f (b p.1.2))) hg
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    LinearMap.zero_apply] at h
  simp only [E, LinearMap.smulRight_apply, map_smul, smul_eq_mul] at h
  have hsingle : (∑ q : OffDiag,
      g q * (b.coord q.1.2 (b p.1.2) * b.coord p.1.1 (b q.1.1))) = g p := by
    rw [Fintype.sum_eq_single p]
    · rw [coord_self, coord_self]
      ring
    · intro q hq
      by_cases h2 : q.1.2 = p.1.2
      · have h1 : q.1.1 ≠ p.1.1 := by
          intro h1
          apply hq
          apply Subtype.ext
          exact Prod.ext h1 h2
        rw [h2, coord_of_ne b (Ne.symm h1)]
        ring
      · rw [coord_of_ne b h2]
        ring
  rw [hsingle] at h
  simpa using h

private lemma offDiag_mem (b : Basis (Fin 4) (ZMod 2) V)
    {W : AddSubgroup (Module.End (ZMod 2) V)}
    (hconj : ∀ (g : V ≃ₗ[ZMod 2] V) {f : Module.End (ZMod 2) V}, f ∈ W →
      g.toLinearMap ∘ₗ f ∘ₗ (g.symm : V →ₗ[ZMod 2] V) ∈ W)
    (hE01 : E b 0 1 ∈ W) : ∀ p : OffDiag, E b p.1.1 p.1.2 ∈ W := by
  classical
  have hE02 : E b 0 2 ∈ W := by
    let τ := LinearEquiv.transvection (coord_of_ne b (by decide : (2 : Fin 4) ≠ 1))
    have h := hconj τ hE01
    have hsub : τ.toLinearMap ∘ₗ E b 0 1 ∘ₗ τ.symm.toLinearMap - E b 0 1 ∈ W :=
      W.sub_mem h hE01
    rwa [conjSub_E01 b 2 (by decide) (by decide)] at hsub
  have hE03 : E b 0 3 ∈ W := by
    let τ := LinearEquiv.transvection (coord_of_ne b (by decide : (3 : Fin 4) ≠ 1))
    have h := hconj τ hE01
    have hsub : τ.toLinearMap ∘ₗ E b 0 1 ∘ₗ τ.symm.toLinearMap - E b 0 1 ∈ W :=
      W.sub_mem h hE01
    rwa [conjSub_E01 b 3 (by decide) (by decide)] at hsub
  have hE0j : ∀ j : Fin 4, j ≠ 0 → E b 0 j ∈ W := by
    intro j hj0
    fin_cases j
    · exact absurd rfl hj0
    · exact hE01
    · exact hE02
    · exact hE03
  have hEij : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → E b i j ∈ W := by
    intro i j hi0 hj0 hij
    let τ := LinearEquiv.transvection (coord_of_ne b (Ne.symm hi0))
    have h0 := hE0j j hj0
    have h := hconj τ h0
    have hsub : τ.toLinearMap ∘ₗ E b 0 j ∘ₗ τ.symm.toLinearMap - E b 0 j ∈ W :=
      W.sub_mem h h0
    rwa [conjSub_E0j b i j hi0 hij] at hsub
  have hE10 : E b 1 0 ∈ W := by
    have h := hconj (swap01 b) hE01
    rwa [conj_swap_E01 b] at h
  have hE20 : E b 2 0 ∈ W := by
    let τ := LinearEquiv.transvection (coord_of_ne b (by decide : (1 : Fin 4) ≠ 2))
    have h := hconj τ hE10
    have hsub : τ.toLinearMap ∘ₗ E b 1 0 ∘ₗ τ.symm.toLinearMap - E b 1 0 ∈ W :=
      W.sub_mem h hE10
    rwa [conjSub_E10_Ei0 b 2 (by decide) (by decide)] at hsub
  have hE30 : E b 3 0 ∈ W := by
    let τ := LinearEquiv.transvection (coord_of_ne b (by decide : (1 : Fin 4) ≠ 3))
    have h := hconj τ hE10
    have hsub : τ.toLinearMap ∘ₗ E b 1 0 ∘ₗ τ.symm.toLinearMap - E b 1 0 ∈ W :=
      W.sub_mem h hE10
    rwa [conjSub_E10_Ei0 b 3 (by decide) (by decide)] at hsub
  have h12 : E b 1 2 ∈ W := hEij 1 2 (by decide) (by decide) (by decide)
  have h13 : E b 1 3 ∈ W := hEij 1 3 (by decide) (by decide) (by decide)
  have h21 : E b 2 1 ∈ W := hEij 2 1 (by decide) (by decide) (by decide)
  have h23 : E b 2 3 ∈ W := hEij 2 3 (by decide) (by decide) (by decide)
  have h31 : E b 3 1 ∈ W := hEij 3 1 (by decide) (by decide) (by decide)
  have h32 : E b 3 2 ∈ W := hEij 3 2 (by decide) (by decide) (by decide)
  rintro ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [hE01, hE02, hE03, hE10, hE20, hE30, h12, h13, h21, h23, h31, h32]
  all_goals exact (hij rfl).elim

private lemma card_ge_of_nilpotent [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 4) {W : AddSubgroup (Module.End (ZMod 2) V)}
    (hconj : ∀ (g : V ≃ₗ[ZMod 2] V) {f : Module.End (ZMod 2) V}, f ∈ W →
      g.toLinearMap ∘ₗ f ∘ₗ (g.symm : V →ₗ[ZMod 2] V) ∈ W)
    {ψ : Dual (ZMod 2) V} {w : V} (hψ : ψ ≠ 0) (hw : w ≠ 0) (hψw : ψ w = 0)
    (hnW : ψ.smulRight w ∈ W) : 2 ^ 12 ≤ Nat.card W := by
  classical
  obtain ⟨b, hb0, hbcoord⟩ := exists_basis_of_nilpotent hV hψ hw hψw
  have hE01 : E b 0 1 ∈ W := by
    rw [show E b 0 1 = ψ.smulRight w by simp [E, hb0, hbcoord]]
    exact hnW
  have hmem : ∀ p : OffDiag, E b p.1.1 p.1.2 ∈ W := offDiag_mem b hconj hE01
  let Wsub : Submodule (ZMod 2) (Module.End (ZMod 2) V) := AddSubgroup.toZModSubmodule 2 W
  have hmem_sub : ∀ p : OffDiag, E b p.1.1 p.1.2 ∈ Wsub := by
    intro p
    rw [AddSubgroup.mem_toZModSubmodule]
    exact hmem p
  let s : OffDiag → Wsub := fun p => ⟨E b p.1.1 p.1.2, hmem_sub p⟩
  have hLI : LinearIndependent (ZMod 2) s := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    exact (Fintype.linearIndependent_iff.1 (linearIndependent_offDiag b)) g
      (by simpa using congrArg Subtype.val hg)
  have hcardOff : Fintype.card OffDiag = 12 := by
    decide
  have hfin : Fintype.card OffDiag ≤ finrank (ZMod 2) Wsub := by
    have hspan := finrank_span_eq_card hLI
    rw [← hspan]
    exact (Submodule.finrank_mono (show Submodule.span (ZMod 2) (Set.range s) ≤ ⊤ from le_top)).trans
      (by simp)
  have h12 : 12 ≤ finrank (ZMod 2) Wsub := by omega
  have hcardW := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Wsub)
  rw [Nat.card_zmod] at hcardW
  calc
    2 ^ 12 ≤ 2 ^ finrank (ZMod 2) Wsub := Nat.pow_le_pow_right (by norm_num) h12
    _ = Nat.card Wsub := hcardW.symm
    _ = Nat.card W := rfl


private lemma smul_one_mem {W : AddSubgroup (Module.End (ZMod 2) V)}
    (h1 : (1 : Module.End (ZMod 2) V) ∈ W) (c : ZMod 2) : c • (1 : Module.End (ZMod 2) V) ∈ W := by
  let Wsub : Submodule (ZMod 2) (Module.End (ZMod 2) V) := AddSubgroup.toZModSubmodule 2 W
  have h1sub : (1 : Module.End (ZMod 2) V) ∈ Wsub := by
    rwa [AddSubgroup.mem_toZModSubmodule]
  have hcsub : c • (1 : Module.End (ZMod 2) V) ∈ Wsub := Submodule.smul_mem Wsub c h1sub
  rwa [AddSubgroup.mem_toZModSubmodule] at hcsub

private lemma exists_nilpotent_of_eigen {W : AddSubgroup (Module.End (ZMod 2) V)}
    (hconj : ∀ (g : V ≃ₗ[ZMod 2] V) {f : Module.End (ZMod 2) V}, f ∈ W →
      g.toLinearMap ∘ₗ f ∘ₗ (g.symm : V →ₗ[ZMod 2] V) ∈ W)
    (h1 : (1 : Module.End (ZMod 2) V) ∈ W) {f : Module.End (ZMod 2) V} (hfW : f ∈ W)
    (hf0 : f ≠ 0) (hf1 : f ≠ 1) {v : V} {c : ZMod 2} (hv : v ≠ 0) (hfv : f v = c • v) :
    ∃ (ψ : Dual (ZMod 2) V) (w : V), ψ ≠ 0 ∧ w ≠ 0 ∧ ψ w = 0 ∧ ψ.smulRight w ∈ W := by
  classical
  let r : Module.End (ZMod 2) V := f - c • (1 : Module.End (ZMod 2) V)
  have hrW : r ∈ W := W.sub_mem hfW (smul_one_mem h1 c)
  have hrne : r ≠ 0 := by
    intro hr0
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · apply hf0
      simpa [r] using hr0
    · apply hf1
      have h := hr0
      rw [show r = f - (1 : Module.End (ZMod 2) V) by simp [r], sub_eq_zero] at h
      exact h
  have hrv : r v = 0 := by
    rw [show r = f - c • (1 : Module.End (ZMod 2) V) from rfl, LinearMap.sub_apply,
      LinearMap.smul_apply, hfv, sub_eq_zero]
    simp
  by_cases hle : LinearMap.range r ≤ Submodule.span (ZMod 2) ({v} : Set V)
  · obtain ⟨ψ, hψr⟩ := exists_smulRight_of_range_le_span hv hle
    have hψv : ψ v = 0 := by
      have hval : (ψ.smulRight v) v = 0 := by
        rw [← hψr]
        exact hrv
      rw [LinearMap.smulRight_apply] at hval
      exact (smul_eq_zero.1 hval).resolve_right hv
    have hψne : ψ ≠ 0 := by
      intro hψ0
      apply hrne
      rw [hψr, hψ0]
      simp
    exact ⟨ψ, v, hψne, hv, hψv, by rw [← hψr]; exact hrW⟩
  · obtain ⟨y, hyrange, hyspan⟩ := SetLike.not_le_iff_exists.1 hle
    obtain ⟨x, rfl⟩ := hyrange
    obtain ⟨φ, hφy, hφv⟩ := CFSG.EvenSporadicStandard.ThStd.exists_dual_one_of_notMem
      (p := Submodule.span (ZMod 2) ({v} : Set V)) (v := r x) hyspan
    have hφv0 : φ v = 0 := hφv v (Submodule.subset_span (by simp))
    let τ := LinearEquiv.transvection hφv0
    let g : Module.End (ZMod 2) V := τ.toLinearMap ∘ₗ f ∘ₗ τ.symm.toLinearMap - f
    have hgW : g ∈ W := W.sub_mem (hconj τ hfW) hfW
    have hg_eq : g = (φ.comp r).smulRight v := by
      rw [show g = τ.toLinearMap ∘ₗ f ∘ₗ τ.symm.toLinearMap - f from rfl]
      rw [transvection_conj_sub f φ hφv0]
      ext z
      simp [r, LinearMap.smulRight_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        map_sub, map_smul, hfv, hφv0, smul_add, add_smul, smul_smul, mul_comm,
        mul_left_comm, mul_assoc]
      rw [sub_eq_add_neg, neg_eq_self_zmod2, ← add_smul]
    have hψne : φ.comp r ≠ 0 := by
      intro hψ0
      have hval : (φ.comp r) x = 0 := by simp [hψ0]
      rw [LinearMap.comp_apply] at hval
      rw [hval] at hφy
      exact zero_ne_one hφy
    have hψv : (φ.comp r) v = 0 := by
      rw [LinearMap.comp_apply, hrv, map_zero]
    exact ⟨φ.comp r, v, hψne, hv, hψv, by rwa [← hg_eq]⟩


private lemma exists_nilpotent_of_not_scalar [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 4) {W : AddSubgroup (Module.End (ZMod 2) V)}
    (hconj : ∀ (g : V ≃ₗ[ZMod 2] V) {f : Module.End (ZMod 2) V}, f ∈ W →
      g.toLinearMap ∘ₗ f ∘ₗ (g.symm : V →ₗ[ZMod 2] V) ∈ W)
    (h1 : (1 : Module.End (ZMod 2) V) ∈ W) {f : Module.End (ZMod 2) V} (hfW : f ∈ W)
    (hf0 : f ≠ 0) (hf1 : f ≠ 1) :
    ∃ (ψ : Dual (ZMod 2) V) (w : V), ψ ≠ 0 ∧ w ≠ 0 ∧ ψ w = 0 ∧ ψ.smulRight w ∈ W := by
  classical
  by_cases heig : ∃ (v : V) (c : ZMod 2), v ≠ 0 ∧ f v = c • v
  · obtain ⟨v, c, hv, hfv⟩ := heig
    exact exists_nilpotent_of_eigen hconj h1 hfW hf0 hf1 hv hfv
  · push Not at heig
    have hnt : Nontrivial V :=
      Module.nontrivial_of_finrank_pos (R := ZMod 2) (M := V) (by rw [hV]; norm_num)
    obtain ⟨a, ha⟩ : ∃ a : V, a ≠ 0 := by
      obtain ⟨x, y, hxy⟩ := exists_pair_ne V
      by_cases hx : x = 0
      · exact ⟨y, by simpa [hx] using hxy.symm⟩
      · exact ⟨x, hx⟩
    have hnotscalar : ∀ c : ZMod 2, f ≠ c • (1 : Module.End (ZMod 2) V) := by
      intro c hc
      apply heig a c ha
      rw [hc]
      simp
    have hnotnorm : ¬ CFSG.EvenSporadicStandard.ThStd.TransvNormalised f a := by
      intro hM
      obtain ⟨c, hc⟩ := hM.exists_smul (by omega) ha
      exact hnotscalar c (LinearMap.ext hc)
    unfold CFSG.EvenSporadicStandard.ThStd.TransvNormalised at hnotnorm
    push Not at hnotnorm
    obtain ⟨φ, w, hφw, hφa, hne⟩ := hnotnorm
    let τ := LinearEquiv.transvection hφw
    have hτne : τ.toLinearMap ∘ₗ f ∘ₗ τ.symm.toLinearMap ≠ f := by
      intro heq
      obtain ⟨u, hu⟩ := hne 0
      apply hu
      have h := congrArg (fun g : Module.End (ZMod 2) V => g (τ.toLinearMap u)) heq
      have h' : τ.toLinearMap (f u) = f (τ.toLinearMap u) := by
        simpa [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using h
      have hformula : f u + φ (f u) • w = f (u + φ u • w) := by
        calc
          f u + φ (f u) • w = τ.toLinearMap (f u) := by
            exact (transvection_apply' φ hφw (f u)).symm
          _ = f (τ.toLinearMap u) := h'
          _ = f (u + φ u • w) := by
            exact congrArg f (transvection_apply' φ hφw u)
      simpa using hformula
    let g : Module.End (ZMod 2) V := τ.toLinearMap ∘ₗ f ∘ₗ τ.symm.toLinearMap - f
    have hgne : g ≠ 0 := by
      intro hg0
      apply hτne
      simpa [g, sub_eq_zero] using hg0
    have hgW : g ∈ W := W.sub_mem (hconj τ hfW) hfW
    have hgw0 : w ≠ 0 := by
      intro hw0
      apply hτne
      have hτ1 : τ.toLinearMap = 1 := by
        have hzero : φ.smulRight (0 : V) = 0 := by
          ext x
          simp
        rw [transvection_toLin φ hφw, hw0, hzero, add_zero]
        rfl
      have hτ1s : τ.symm.toLinearMap = 1 := by
        rw [transvection_symm φ hφw, hτ1]
      rw [hτ1, hτ1s]
      rfl
    have hrange : LinearMap.range g ≤ Submodule.span (ZMod 2) ({w, f w} : Set V) := by
      rw [show g = τ.toLinearMap ∘ₗ f ∘ₗ τ.symm.toLinearMap - f from rfl]
      exact range_conjSub_le_span_pair f φ hφw
    have hrank : finrank (ZMod 2) (LinearMap.range g) ≤ 2 :=
      (Submodule.finrank_mono hrange).trans (finrank_span_pair_le w (f w))
    have hgne1 : g ≠ 1 := by
      intro hg1
      have htop : finrank (ZMod 2) (LinearMap.range g) = 4 := by
        rw [hg1, LinearMap.range_eq_top.2 (fun x => ⟨x, rfl⟩), finrank_top, hV]
      omega
    have hgw : g w = φ (f w) • w := by
      rw [show g = τ.toLinearMap ∘ₗ f ∘ₗ τ.symm.toLinearMap - f from rfl]
      exact conjSub_apply_self f φ hφw
    exact exists_nilpotent_of_eigen hconj h1 hgW hgne hgne1 hgw0 hgw


theorem end_eq_zero_or_one_of_conj_invariant_of_card_le [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 4) {W : AddSubgroup (Module.End (ZMod 2) V)}
    (hconj : ∀ (g : V ≃ₗ[ZMod 2] V) {f : Module.End (ZMod 2) V}, f ∈ W →
      g.toLinearMap ∘ₗ f ∘ₗ (g.symm : V →ₗ[ZMod 2] V) ∈ W)
    (h1 : (1 : Module.End (ZMod 2) V) ∈ W) (hcard : Nat.card W ≤ 2 ^ 10) :
    ∀ f ∈ W, f = 0 ∨ f = 1 := by
  intro f hfW
  by_contra h
  push Not at h
  obtain ⟨hf0, hf1⟩ := h
  obtain ⟨ψ, w, hψ, hw, hψw, hnW⟩ :=
    exists_nilpotent_of_not_scalar hV hconj h1 hfW hf0 hf1
  have hge := card_ge_of_nilpotent hV hconj hψ hw hψw hnW
  norm_num at hge hcard
  omega


private noncomputable def monoidHomToAddEquiv (H : Type*) [CommGroup H] :
    Additive (H →* H) ≃+ (Additive H →+ Additive H) where
  toFun f := MonoidHom.toAdditive (Additive.toMul f)
  invFun g := Additive.ofMul ((MonoidHom.toAdditive).symm g)
  left_inv f := by
    change Additive.ofMul (MonoidHom.toAdditive.symm (MonoidHom.toAdditive (Additive.toMul f))) = f
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv g := by
    change MonoidHom.toAdditive ((MonoidHom.toAdditive).symm g) = g
    rw [Equiv.apply_symm_apply]
  map_add' f g := by
    ext x
    rfl

private lemma natCard_map_addEquiv {A B : Type*} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (K : AddSubgroup A) :
    Nat.card (AddSubgroup.map e.toAddMonoidHom K) = Nat.card K := by
  apply Nat.card_congr
  refine
  { toFun := fun y => ⟨e.symm y.1, (AddSubgroup.mem_map_equiv (f := e)).1 y.2⟩
    invFun := fun x => ⟨e x.1, AddSubgroup.mem_map.2 ⟨x.1, x.2, rfl⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro y
    ext
    exact e.apply_symm_apply y.1
  · intro x
    ext
    exact e.symm_apply_apply x.1


theorem monoidHom_eq_one_or_id_of_conj_invariant_of_card_le {H : Type*} [CommGroup H]
    (hsq : ∀ x : H, x ^ 2 = 1) (hcardH : Nat.card H = 16) {W : Subgroup (H →* H)}
    (hconj : ∀ (σ : H ≃* H) {f : H →* H}, f ∈ W →
      (σ : H →* H).comp (f.comp (σ.symm : H →* H)) ∈ W)
    (hid : MonoidHom.id H ∈ W) (hcardW : Nat.card W ≤ 2 ^ 10) :
    ∀ f ∈ W, f = 1 ∨ f = MonoidHom.id H := by
  classical
  have h2 : ∀ x : Additive H, 2 • x = 0 := fun x => by
    apply Additive.toMul.injective
    simpa using hsq (Additive.toMul x)
  let _ : Module (ZMod 2) (Additive H) := AddCommGroup.zmodModule h2
  have : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have : FiniteDimensional (ZMod 2) (Additive H) := Module.Finite.of_finite
  have hdim : finrank (ZMod 2) (Additive H) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive H)
    rw [Nat.card_congr (Additive.toMul : Additive H ≃ H), hcardH, Nat.card_zmod] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num))
  let eEnd : Additive (H →* H) ≃+ Module.End (ZMod 2) (Additive H) :=
    (monoidHomToAddEquiv H).trans (AddMonoidHom.toZModLinearMapEquiv 2)
  let Wadd : AddSubgroup (Module.End (ZMod 2) (Additive H)) :=
    (Subgroup.toAddSubgroup W).map eEnd.toAddMonoidHom
  have hcardWadd : Nat.card Wadd ≤ 2 ^ 10 := by
    rw [show Wadd = AddSubgroup.map eEnd.toAddMonoidHom (Subgroup.toAddSubgroup W) from rfl,
      natCard_map_addEquiv]
    exact hcardW
  have hidEnd : eEnd (Additive.ofMul (MonoidHom.id H)) = 1 := by
    ext x
    rfl
  have h1Wadd : (1 : Module.End (ZMod 2) (Additive H)) ∈ Wadd := by
    rw [AddSubgroup.mem_map_equiv]
    rw [← hidEnd, AddEquiv.symm_apply_apply]
    exact hid
  have hconjWadd : ∀ (g : Additive H ≃ₗ[ZMod 2] Additive H)
      {f : Module.End (ZMod 2) (Additive H)}, f ∈ Wadd →
      g.toLinearMap ∘ₗ f ∘ₗ (g.symm : Additive H →ₗ[ZMod 2] Additive H) ∈ Wadd := by
    intro g f hf
    rw [AddSubgroup.mem_map_equiv] at hf ⊢
    let F : H →* H := Additive.toMul (eEnd.symm f)
    have hFW : F ∈ W := hf
    let σ : H ≃* H := MulEquiv.toAdditive.symm g.toAddEquiv
    have hconjσ : (σ : H →* H).comp (F.comp (σ.symm : H →* H)) ∈ W := hconj σ hFW
    have hσ : MulEquiv.toAdditive σ = g.toAddEquiv := Equiv.apply_symm_apply _ _
    have hkey : eEnd (Additive.ofMul ((σ : H →* H).comp (F.comp (σ.symm : H →* H)))) =
        g.toLinearMap ∘ₗ f ∘ₗ (g.symm : Additive H →ₗ[ZMod 2] Additive H) := by
      ext x
      change g (((AddMonoidHom.toZModLinearMapEquiv 2).symm f) (g.symm x)) =
        g (f (g.symm x))
      rfl
    rw [← hkey]
    exact hconjσ
  have hmain := end_eq_zero_or_one_of_conj_invariant_of_card_le hdim hconjWadd h1Wadd hcardWadd
  intro f hfW
  have hfWadd : eEnd (Additive.ofMul f) ∈ Wadd := by
    rw [AddSubgroup.mem_map_equiv, AddEquiv.symm_apply_apply]
    exact hfW
  have h := hmain (eEnd (Additive.ofMul f)) hfWadd
  rcases h with h0 | h1
  · left
    have h0' : Additive.ofMul f = 0 := by
      apply eEnd.injective
      simpa using h0
    simpa using congrArg Additive.toMul h0'
  · right
    have h1' : Additive.ofMul f = Additive.ofMul (MonoidHom.id H) := by
      apply eEnd.injective
      rw [h1, hidEnd]
    exact Additive.ofMul.injective h1'

end CFSG.LinearAlgebra

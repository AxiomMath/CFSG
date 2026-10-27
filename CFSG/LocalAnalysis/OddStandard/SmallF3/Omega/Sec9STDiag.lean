module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem zmod3_ne_zero_eq_one_or_neg_one (x : ZMod 3) (hx : x ≠ 0) :
    x = 1 ∨ x = -1 := by
  revert x
  decide

private theorem zmod3_mul_self_eq_one (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  revert x
  decide

private theorem repr_apply_of_diag {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    (g : V ≃ₗ[ZMod 3] V) (ε : Fin n → ZMod 3)
    (hg : ∀ m, g (b m) = ε m • b m) (w : V) (j : Fin n) :
    b.repr (g w) j = ε j * b.repr w j :=
  b.repr_apply_of_apply_basis (f := (g : V →ₗ[ZMod 3] V)) (a := ε) hg w j

theorem sec9t_scalar_of_commute {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    {Ft : Subgroup (OGroup Q)} (hb : IsEvenFrame b Ft) (hn : 3 ≤ n) {σ : V ≃ₗ[ZMod 3] V}
    (hσ : ∀ g ∈ Ft, σ * (g : V ≃ₗ[ZMod 3] V) = (g : V ≃ₗ[ZMod 3] V) * σ) (i : Fin n) :
    ∃ x : ZMod 3, x ≠ 0 ∧ σ (b i) = x • b i := by
  classical
  have hzero : ∀ j : Fin n, j ≠ i → b.repr (σ (b i)) j = 0 := by
    intro j hji
    obtain ⟨g, hg, hgi, hgj⟩ := IsEvenFrame.exists_sep hb hn hji.symm
    obtain ⟨S, -, hgS⟩ := hb.1 g hg
    let ε : Fin n → ZMod 3 := fun m => if m ∈ S then -1 else 1
    have hgdiag : ∀ m, (g : V ≃ₗ[ZMod 3] V) (b m) = ε m • b m := fun m => hgS m
    have hgw : (g : V ≃ₗ[ZMod 3] V) (σ (b i)) = -σ (b i) := by
      have hcomm : σ * (g : V ≃ₗ[ZMod 3] V) = (g : V ≃ₗ[ZMod 3] V) * σ := hσ g hg
      calc (g : V ≃ₗ[ZMod 3] V) (σ (b i))
          = ((g : V ≃ₗ[ZMod 3] V) * σ) (b i) := by rw [LinearEquiv.mul_apply]
        _ = (σ * (g : V ≃ₗ[ZMod 3] V)) (b i) := by rw [hcomm]
        _ = σ ((g : V ≃ₗ[ZMod 3] V) (b i)) := by rw [LinearEquiv.mul_apply]
        _ = σ (-(b i)) := by rw [hgi]
        _ = -σ (b i) := map_neg (σ : V →ₗ[ZMod 3] V) (b i)
    have hεj : ε j = 1 := by
      have hEq : ε j • b j = (1 : ZMod 3) • b j := by
        rw [← hgdiag j, hgj, one_smul]
      have hsub : (ε j - 1) • b j = 0 := by
        rw [sub_smul, hEq, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right (b.ne_zero j))
    have h1 : b.repr ((g : V ≃ₗ[ZMod 3] V) (σ (b i))) j = b.repr (σ (b i)) j := by
      rw [repr_apply_of_diag (g := (g : V ≃ₗ[ZMod 3] V)) (ε := ε) hgdiag (σ (b i)) j,
        hεj, one_mul]
    have h2 : b.repr ((g : V ≃ₗ[ZMod 3] V) (σ (b i))) j = -b.repr (σ (b i)) j := by
      rw [hgw, map_neg]
      simpa using map_neg (Finsupp.lapply j) (b.repr (σ (b i)))
    have heq : b.repr (σ (b i)) j = -b.repr (σ (b i)) j := h1.symm.trans h2
    have hsum : b.repr (σ (b i)) j + b.repr (σ (b i)) j = 0 := by
      rw [← eq_neg_iff_add_eq_zero]
      exact heq
    have h2x : (2 : ZMod 3) * b.repr (σ (b i)) j = 0 := by
      rw [two_mul]
      exact hsum
    exact (mul_eq_zero.mp h2x).resolve_left (by decide)
  have heq : σ (b i) = b.repr (σ (b i)) i • b i := by
    rw [b.ext_elem_iff]
    intro j
    by_cases hji : j = i
    · subst hji
      rw [map_smul, b.repr_self]
      simp
    · rw [hzero j hji, map_smul, b.repr_self]
      simp [Finsupp.smul_apply, Finsupp.single_eq_of_ne hji]
  refine ⟨b.repr (σ (b i)) i, ?_, heq⟩
  intro hx0
  have hwne : σ (b i) ≠ 0 := by
    intro h
    exact b.ne_zero i (σ.injective (by rw [h, map_zero]))
  apply hwne
  rw [heq, hx0, zero_smul]

theorem sec9t_multiplier_eq_one {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ}
    (hσ : IsSimilitude Q σ c) {w : V} {x : ZMod 3} (hx : x ≠ 0) (hw : σ w = x • w)
    (hQw : Q w ≠ 0) : c = 1 := by
  have h1 : Q (σ w) = (c : ZMod 3) * Q w := hσ w
  rw [hw] at h1
  rw [QuadraticMap.map_smul, zmod3_mul_self_eq_one x hx, one_smul] at h1
  refine Units.ext ?_
  refine mul_right_cancel₀ hQw ?_
  simpa using h1.symm

theorem sec9t_exists_signs {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    {σ : V ≃ₗ[ZMod 3] V} (hx : ∀ i, ∃ x : ZMod 3, x ≠ 0 ∧ σ (b i) = x • b i) :
    ∃ T : Finset (Fin n), ∀ i, σ (b i) = (if i ∈ T then (-1 : ZMod 3) else 1) • b i := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter (fun i => σ (b i) = (-1 : ZMod 3) • b i)
  refine ⟨T, fun i => ?_⟩
  by_cases hi : i ∈ T
  · rw [if_pos hi]
    exact (Finset.mem_filter.mp hi).2
  · rw [if_neg hi]
    obtain ⟨x, hx0, hxeq⟩ := hx i
    rcases zmod3_ne_zero_eq_one_or_neg_one x hx0 with hx1 | hxneg
    · rw [hxeq, hx1, one_smul]
    · exfalso
      apply hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, by rw [hxeq, hxneg]⟩

end CFSG.OddStandard.SmallF3.Omega

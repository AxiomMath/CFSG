module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelHighBase
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_KernelT
public import CFSG.GroupActions.SubgroupStabilizerOuterBound

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem displacement_central_of_conj_eq {P : Subgroup G} {F : G →* G} {y g : G}
    (hg : g ∈ P) (hFmem : ∀ x ∈ P, F x ∈ P)
    (hFsurj : ∀ x ∈ P, ∃ x' ∈ P, F x' = x)
    (hyF : F y = y)
    (hconj : ∀ x ∈ P, y * x * y⁻¹ = g * x * g⁻¹) :
    ∀ x ∈ P, x * (g⁻¹ * F g) = (g⁻¹ * F g) * x := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := hFsurj x hx
  have h1 := hconj x' hx'
  have h2 := hconj (F x') (hFmem x' hx')
  have h3 : y * F x' * y⁻¹ = F g * F x' * (F g)⁻¹ := by
    have h := congrArg F h1
    simpa [map_mul, map_inv, hyF] using h
  have h4 : g * F x' * g⁻¹ = F g * F x' * (F g)⁻¹ := by
    rw [← h2, h3]
  have h5 : (g⁻¹ * F g) * F x' * (g⁻¹ * F g)⁻¹ = F x' := by
    rw [show (g⁻¹ * F g) * F x' * (g⁻¹ * F g)⁻¹ =
      g⁻¹ * (F g * F x' * (F g)⁻¹) * g by group]
    rw [← h4]
    group
  calc F x' * (g⁻¹ * F g)
      = ((g⁻¹ * F g) * F x' * (g⁻¹ * F g)⁻¹) * (g⁻¹ * F g) := by rw [h5]
    _ = (g⁻¹ * F g) * F x' := by group

theorem pow_three_displacement_eq_one {P : Subgroup G} {F : G →* G} {g : G}
    (hExp : ∀ z : ↥P, z ∈ Subgroup.center P → ((z : G) ^ 3 = 1))
    (hcen : ∀ x ∈ P, x * (g⁻¹ * F g) = (g⁻¹ * F g) * x)
    (hmem : g⁻¹ * F g ∈ P) :
    (g⁻¹ * F g) ^ 3 = 1 := by
  have hcenter : (⟨g⁻¹ * F g, hmem⟩ : ↥P) ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (hcen x x.2)
  exact hExp _ hcenter

theorem mul_fixed_of_step_frob {F φ : G →* G} {g z : G}
    (hFg : F g = g * z) (hz3 : z ^ 3 = 1) (hφz : φ z = z ^ 2)
    (hcomm : z * φ g = φ g * z)
    (hFφ : F (φ g) = φ (F g)) :
    F (g * φ g) = g * φ g := by
  calc F (g * φ g) = F g * F (φ g) := by rw [map_mul]
    _ = (g * z) * (φ g * z ^ 2) := by rw [hFg, hFφ, hFg, map_mul, hφz]
    _ = g * φ g := by
      rw [show g * z * (φ g * z ^ 2) = g * (z * φ g) * z ^ 2 by group]
      rw [hcomm]
      rw [show g * (φ g * z) * z ^ 2 = g * φ g * z ^ 3 by group]
      rw [hz3, mul_one]

theorem mul_frob_conj_eq_on_fixed {P : Subgroup G} {f : G →* G} {g y : G}
    (hg : g ∈ P) (hconj : ∀ x ∈ P, y * x * y⁻¹ = g * x * g⁻¹)
    (hfmem : ∀ x ∈ P, f x ∈ P)
    (hfsurj : ∀ x ∈ P, ∃ x' ∈ P, f x' = x)
    {c : G} (hc : c ∈ P) :
    (g * f g) * c * (g * f g)⁻¹ = (y * f y) * c * (y * f y)⁻¹ := by
  set u : G := y⁻¹ * g with hu
  have hu_cent : ∀ x ∈ P, u * x * u⁻¹ = x := by
    intro x hx
    rw [hu]
    calc (y⁻¹ * g) * x * (y⁻¹ * g)⁻¹ = y⁻¹ * (g * x * g⁻¹) * y := by group
      _ = y⁻¹ * (y * x * y⁻¹) * y := by rw [← hconj x hx]
      _ = x := by group
  have hy_norm : ∀ x ∈ P, y * x * y⁻¹ ∈ P := by
    intro x hx
    rw [hconj x hx]
    exact P.mul_mem (P.mul_mem hg hx) (P.inv_mem hg)
  have hfy_norm : ∀ x ∈ P, f y * x * (f y)⁻¹ ∈ P := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hfsurj x hx
    have h := hfmem _ (hy_norm x' hx')
    simpa [map_mul, map_inv] using h
  have hfu_cent : ∀ x ∈ P, f u * x * (f u)⁻¹ = x := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hfsurj x hx
    have h := congrArg f (hu_cent x' hx')
    simpa [map_mul, map_inv] using h
  have hconj_fy_cent : ∀ x ∈ P, ((f y)⁻¹ * u * (f y)) * x * ((f y)⁻¹ * u * (f y))⁻¹ = x := by
    intro x hx
    have hx' : f y * x * (f y)⁻¹ ∈ P := hfy_norm x hx
    have h := hu_cent _ hx'
    calc ((f y)⁻¹ * u * (f y)) * x * ((f y)⁻¹ * u * (f y))⁻¹
        = (f y)⁻¹ * (u * (f y * x * (f y)⁻¹) * u⁻¹) * (f y) := by group
      _ = (f y)⁻¹ * (f y * x * (f y)⁻¹) * (f y) := by rw [h]
      _ = x := by group
  set v : G := (f y)⁻¹ * u * (f y) * f u with hv
  have hv_cent : ∀ x ∈ P, v * x * v⁻¹ = x := by
    intro x hx
    have h1 := hconj_fy_cent x hx
    have h2 := hfu_cent x hx
    calc v * x * v⁻¹
        = ((f y)⁻¹ * u * (f y)) * (f u * x * (f u)⁻¹) *
            ((f y)⁻¹ * u * (f y))⁻¹ := by rw [hv]; group
      _ = ((f y)⁻¹ * u * (f y)) * x * ((f y)⁻¹ * u * (f y))⁻¹ := by rw [h2]
      _ = x := h1
  have hg_eq : g = y * u := by rw [hu]; group
  have hprod : g * f g = (y * f y) * v := by
    rw [hv, hg_eq, map_mul, map_mul]
    group
  rw [hprod]
  rw [show ((y * f y) * v) * c * ((y * f y) * v)⁻¹ =
      (y * f y) * (v * c * v⁻¹) * (y * f y)⁻¹ by group]
  rw [hv_cent c hc]

theorem conj_pow_subtype_apply_eq {P C : Subgroup G} (hCP : C ≤ P) {y g : G}
    (hg : g ∈ P) (hconj : ∀ x ∈ P, y * x * y⁻¹ = g * x * g⁻¹)
    (k : ℕ) (hk : g ^ k ∈ C) (c : ↥C) :
    ((MulAut.conj (⟨g ^ k, hk⟩ : C)) c : G) = y ^ k * (c : G) * (y ^ k)⁻¹ :=
  (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116t_pow (Subgroup.le_normalizer hg)
    hconj k _ (hCP c.2)).symm

theorem subgroupStabRestrict_conj_aut {R : Subgroup G} {f : G →* G} {φ : MulAut R}
    (hφ : ∀ x : R, ((φ x : R) : G) = f (x : G))
    {y : G} (hy : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut R)
    (hfy : MulAut.conj (f y) ∈ CFSG.GroupActions.subgroupStabAut R) :
    φ * CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj y, hy⟩ * φ⁻¹ =
      CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj (f y), hfy⟩ := by
  have hφsymm : ∀ z : R, f ((φ.symm z : R) : G) = (z : G) := by
    intro z
    rw [← hφ (φ.symm z)]
    exact congrArg Subtype.val (φ.apply_symm_apply z)
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [show (φ * CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj y, hy⟩ * φ⁻¹) x =
      φ (CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj y, hy⟩ (φ⁻¹ x)) by
    rw [MulAut.mul_apply, MulAut.mul_apply]]
  rw [hφ]
  rw [show ((CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj y, hy⟩ (φ⁻¹ x) : R) : G) =
      y * ((φ⁻¹ x : R) : G) * y⁻¹ by
    rw [CFSG.GroupActions.subgroupStabRestrict_apply, MulAut.conj_apply]]
  rw [show ((φ⁻¹ x : R) : G) = ((φ.symm x : R) : G) by rw [MulAut.inv_apply]]
  rw [map_mul, map_mul, map_inv, hφsymm x]
  rw [CFSG.GroupActions.subgroupStabRestrict_apply, MulAut.conj_apply]


theorem centerQuotientHom_mem_innAutDerived_of_cube {R : Subgroup G} [Finite R]
    (f : G →* G) (hf : Function.Injective f) (hfR : R.map f ≤ R)
    {y : G} (hy : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut R)
    (hfy : MulAut.conj (f y) ∈ CFSG.GroupActions.subgroupStabAut R)
    (hy3 : MulAut.conj (y ^ 3) ∈ CFSG.GroupActions.subgroupStabAut R)
    (hyfy : MulAut.conj (y * f y) ∈ CFSG.GroupActions.subgroupStabAut R)
    (h3 : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
        (CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj (y ^ 3), hy3⟩) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (R ⧸ Subgroup.center R))
    (h2 : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
        (CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj (y * f y), hyfy⟩) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (R ⧸ Subgroup.center R)) :
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
        (CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj y, hy⟩) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (R ⧸ Subgroup.center R) := by
  classical
  let γ : CFSG.GroupActions.subgroupStabAut R := ⟨MulAut.conj y, hy⟩
  let γ3 : CFSG.GroupActions.subgroupStabAut R := ⟨MulAut.conj (y ^ 3), hy3⟩
  let γfy : CFSG.GroupActions.subgroupStabAut R := ⟨MulAut.conj (y * f y), hyfy⟩
  let γf : CFSG.GroupActions.subgroupStabAut R := ⟨MulAut.conj (f y), hfy⟩
  let fR : R →* R :=
    { toFun := fun x => ⟨f x, hfR ⟨x, x.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x z => Subtype.ext (map_mul f (x : G) (z : G)) }
  have hfR_inj : Function.Injective fR := by
    intro x z h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  let φR : MulAut R := MulEquiv.ofBijective fR (Finite.injective_iff_bijective.mp hfR_inj)
  have hφ : ∀ x : R, ((φR x : R) : G) = f x := fun x => rfl
  have hφconj : φR * CFSG.GroupActions.subgroupStabRestrict R γ * φR⁻¹ =
      CFSG.GroupActions.subgroupStabRestrict R γf := subgroupStabRestrict_conj_aut hφ hy hfy
  have hγ3 : γ ^ 3 = γ3 := by
    apply Subtype.ext
    change (MulAut.conj y) ^ 3 = MulAut.conj (y ^ 3)
    rw [map_pow]
  have hγfy : γ * γf = γfy := by
    apply Subtype.ext
    change MulAut.conj y * MulAut.conj (f y) = MulAut.conj (y * f y)
    rw [map_mul]
  let δ : MulAut (R ⧸ Subgroup.center R) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
      (CFSG.GroupActions.subgroupStabRestrict R γ)
  let φq : MulAut (R ⧸ Subgroup.center R) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R φR
  have hδ3 : δ ^ 3 ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      (R ⧸ Subgroup.center R) := by
    have h : δ ^ 3 = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
        (CFSG.GroupActions.subgroupStabRestrict R γ3) := by
      rw [show δ = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
          (CFSG.GroupActions.subgroupStabRestrict R γ) from rfl, ← map_pow, ← map_pow]
      rw [show γ ^ 3 = γ3 from hγ3]
    rwa [h]
  have hφqconj : φq * δ * φq⁻¹ =
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
        (CFSG.GroupActions.subgroupStabRestrict R γf) := by
    rw [show φq = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R φR
        from rfl,
      show δ = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
          (CFSG.GroupActions.subgroupStabRestrict R γ) from rfl]
    rw [show CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R φR *
        CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
          (CFSG.GroupActions.subgroupStabRestrict R γ) *
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R φR)⁻¹ =
        CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
          (φR * CFSG.GroupActions.subgroupStabRestrict R γ * φR⁻¹) by
      rw [map_mul, map_mul, map_inv]]
    rw [hφconj]
  have h2eq : δ * (φq * δ * φq⁻¹) =
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
        (CFSG.GroupActions.subgroupStabRestrict R γfy) := by
    rw [hφqconj]
    rw [show δ = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
      (CFSG.GroupActions.subgroupStabRestrict R γ) from rfl]
    rw [show CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
        (CFSG.GroupActions.subgroupStabRestrict R γ) *
        CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
          (CFSG.GroupActions.subgroupStabRestrict R γf) =
        CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom R
          (CFSG.GroupActions.subgroupStabRestrict R (γ * γf)) by
      rw [← map_mul, ← map_mul]]
    rw [hγfy]
  have h2' : δ * (φq * δ * φq⁻¹) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (R ⧸ Subgroup.center R) := h2eq.symm ▸ h2
  exact mem_of_pow_three_mul_conj
    (CFSG.ComponentClassification.OuterAutomorphisms.commutator_le_innAutDerived
      (R ⧸ Subgroup.center R)) hδ3 h2'

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

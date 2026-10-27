module

public import CFSG.GF2Type.Smith1979.CaseIIASp
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Transvection.Generation

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2.Sp

open Module
open scoped commutatorElement Pointwise

section GL3Perfect

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

theorem transvection_mul_self {φ : Module.Dual (ZMod 2) X} {c : X} (h : φ c = 0) :
    LinearEquiv.transvection h * LinearEquiv.transvection h = 1 := by
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, LinearEquiv.transvection.apply, map_add, map_smul, h,
    smul_zero, zero_smul, add_zero, LinearEquiv.coe_one, id_eq, smul_eq_mul, mul_zero]
  rw [add_assoc, ← smul_add, vec_add_self, smul_zero, add_zero]

theorem transvection_inv {φ : Module.Dual (ZMod 2) X} {c : X} (h : φ c = 0) :
    (LinearEquiv.transvection h)⁻¹ = LinearEquiv.transvection h :=
  inv_eq_of_mul_eq_one_right (transvection_mul_self h)

theorem commutator_transvection {φ ψ : Module.Dual (ZMod 2) X} {u w : X} (hφu : φ u = 0)
    (hψw : ψ w = 0) (hψu : ψ u = 0) (hφw : φ w = 1) :
    ⁅LinearEquiv.transvection hφu, LinearEquiv.transvection hψw⁆ =
      LinearEquiv.transvection hψu := by
  rw [commutatorElement_def, transvection_inv hφu, transvection_inv hψw]
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, LinearEquiv.transvection.apply, map_add, map_smul, hφu, hψw,
    hψu, hφw, smul_zero, zero_smul, add_zero, smul_eq_mul, mul_zero, mul_one]
  simp only [one_smul, smul_add]
  have h1 := vec_add_self (φ x • u)
  have h2 := vec_add_self (ψ x • w)
  have h3 := vec_add_self (ψ x • u)
  linear_combination (norm := module) h1 + h2 + h3

theorem transvection_mem_commutator (hX : finrank (ZMod 2) X = 3) {ψ : Module.Dual (ZMod 2) X}
    {u : X} (h : ψ u = 0) :
    LinearEquiv.transvection h ∈ commutator (X ≃ₗ[ZMod 2] X) := by
  by_cases hu : u = 0
  · subst hu
    have : LinearEquiv.transvection h = 1 :=
      LinearEquiv.ext fun x => by simp [LinearEquiv.transvection.apply]
    rw [this]
    exact one_mem _
  obtain ⟨φ', hφ'u, -⟩ := exists_dual_of_notMem (p := ⊥) (x := u) (by simpa using hu)
  obtain ⟨w, hw0, hψw, hφ'w⟩ := exists_ne_zero_mem_ker₂ hX ψ φ'
  have hwu : w ∉ Submodule.span (ZMod 2) {u} := by
    intro hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    rw [map_smul, hφ'u, smul_eq_mul, mul_one] at hφ'w
    exact hw0 (by rw [hφ'w, zero_smul])
  obtain ⟨φ, hφw, hφp⟩ := exists_dual_of_notMem hwu
  have hφu : φ u = 0 := hφp u (Submodule.mem_span_singleton_self u)
  have := commutator_transvection hφu hψw h hφw
  rw [← this]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem dilatransvection_mem_transvections (d : X ≃ₗ[ZMod 2] X)
    (hd : d ∈ LinearEquiv.dilatransvections (ZMod 2) X) :
    d ∈ LinearEquiv.transvections (ZMod 2) X := by
  obtain ⟨f, v, hfv⟩ := hd
  have hfv0 : f v = 0 := by
    rcases zmod2_cases (f v) with h | h
    · exact h
    · exfalso
      have h1 : d v = 0 := by
        have := congrArg (fun m : X →ₗ[ZMod 2] X => m v) hfv
        simp only [LinearEquiv.coe_coe, LinearMap.transvection.apply, h, one_smul] at this
        rw [this, vec_add_self]
      have h2 : v = 0 := d.injective (by rw [h1, map_zero])
      rw [h2, map_zero] at h
      exact zero_ne_one h
  refine ⟨f, v, hfv0, LinearEquiv.ext fun x => ?_⟩
  have := congrArg (fun m : X →ₗ[ZMod 2] X => m x) hfv
  simpa [LinearEquiv.transvection.apply, LinearMap.transvection.apply] using this

theorem not_isExceptional (e : X ≃ₗ[ZMod 2] X) : ¬ LinearEquiv.IsExceptional e := by
  rintro ⟨h1, h2, a, ha⟩
  rcases zmod2_cases a with rfl | rfl
  · have hz : ∀ x : X ⧸ e.fixedSubmodule, x = 0 := fun x => by
      have : e.fixedReduce x = e.fixedReduce 0 := by rw [ha, zero_smul, map_zero]
      exact e.fixedReduce.injective this
    haveI : Subsingleton (X ⧸ e.fixedSubmodule) := ⟨fun x y => by rw [hz x, hz y]⟩
    have := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := X ⧸ e.fixedSubmodule)
    omega
  · apply h2
    exact LinearEquiv.ext fun x => by simpa using ha x

theorem commutator_gl3_eq_top (hX : finrank (ZMod 2) X = 3) :
    commutator (X ≃ₗ[ZMod 2] X) = ⊤ := by
  refine eq_top_iff.mpr fun e _ => ?_
  have hmem := LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_not_isExceptional
    (not_isExceptional e)
  have htv : ∀ T ∈ LinearEquiv.transvections (ZMod 2) X, T ∈ commutator (X ≃ₗ[ZMod 2] X) := by
    rintro _ ⟨f, v, hfv, rfl⟩
    exact transvection_mem_commutator hX hfv
  have hT : ∀ n : ℕ, ∀ x ∈ (LinearEquiv.transvections (ZMod 2) X) ^ n,
      x ∈ commutator (X ≃ₗ[ZMod 2] X) := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [pow_zero, Set.mem_one] at hx
      rw [hx]
      exact one_mem _
    | succ n ih =>
      intro x hx
      rw [pow_succ, Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact mul_mem (ih a ha) (htv b hb)
  obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.mp hmem
  exact mul_mem (hT _ a ha) (htv d (dilatransvection_mem_transvections d hd))

end GL3Perfect

section Xac

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}

@[expose] def xacMap (ω : LinearMap.BilinForm (ZMod 2) W) (a c : W) : W →ₗ[ZMod 2] W :=
  LinearMap.id + (ω.flip a).smulRight c + (ω.flip c).smulRight a

theorem xacMap_apply (ω : LinearMap.BilinForm (ZMod 2) W) (a c u : W) :
    xacMap ω a c u = u + ω u a • c + ω u c • a := rfl

variable (D : SpData ω V)
include D

theorem omega_xacMap_left (a c : V) (u : W) :
    ω (ω u a • (c : W) + ω u c • (a : W)) a = 0 ∧ ω (ω u a • (c : W) + ω u c • (a : W)) c = 0 := by
  have h1 := D.iso (c : W) c.2 (a : W) a.2
  have h2 := D.iso (a : W) a.2 (a : W) a.2
  have h3 := D.iso (c : W) c.2 (c : W) c.2
  have h4 := D.iso (a : W) a.2 (c : W) c.2
  constructor
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
      mul_zero, add_zero]
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h3, h4,
      mul_zero, add_zero]

theorem xacMap_invol (a c : V) (u : W) : xacMap ω a c (xacMap ω a c u) = u := by
  obtain ⟨hpa, hpc⟩ := omega_xacMap_left D a c u
  rw [xacMap_apply ω a c u]
  rw [xacMap_apply ω a c (u + ω u a • (c : W) + ω u c • (a : W))]
  have e1 : ω (u + ω u a • (c : W) + ω u c • (a : W)) a = ω u a := by
    rw [add_assoc, map_add, LinearMap.add_apply, hpa, add_zero]
  have e2 : ω (u + ω u a • (c : W) + ω u c • (a : W)) c = ω u c := by
    rw [add_assoc, map_add, LinearMap.add_apply, hpc, add_zero]
  rw [e1, e2]
  have h := vec_add_self (ω u a • (c : W) + ω u c • (a : W))
  linear_combination (norm := module) h

@[expose] noncomputable def xac (a c : V) : W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofInvolutive (xacMap ω a c) (xacMap_invol D a c)

theorem xac_apply (a c : V) (u : W) :
    xac D a c u = u + ω u a • (c : W) + ω u c • (a : W) := rfl

theorem xac_isF (a c : V) : IsF ω V (xac D a c) where
  isom u v := by
    have hcc := D.iso (c : W) c.2 (c : W) c.2
    have hca := D.iso (c : W) c.2 (a : W) a.2
    have hac := D.iso (a : W) a.2 (c : W) c.2
    have haa := D.iso (a : W) a.2 (a : W) a.2
    simp only [xac_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hcc, hca, hac, haa, mul_zero, add_zero]
    rw [D.symm (c : W) v, D.symm (a : W) v]
    have h2 : (2 : ZMod 2) = 0 := by decide
    linear_combination (ω v a * ω u c + ω v c * ω u a) * h2
  triv v hv := by
    rw [xac_apply, D.iso v hv a a.2, D.iso v hv c c.2]
    simp

theorem xac_alt (a c : V) (u : W) : ω (xac D a c u - u) u = 0 := by
  have : xac D a c u - u = ω u a • (c : W) + ω u c • (a : W) := by
    rw [xac_apply]
    abel
  rw [this]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [D.symm (c : W) u, D.symm (a : W) u]
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination (ω u a * ω u c) * h2

theorem xac_mem_alt (a c : V) : xac D a c ∈ AltGrp ω V D := ⟨xac_isF D a c, xac_alt D a c⟩

theorem xac_sub_apply (a c : V) (u w : W) :
    ω (xac D a c u - u) w = ω u a * ω (c : W) w + ω u c * ω (a : W) w := by
  have : xac D a c u - u = ω u a • (c : W) + ω u c • (a : W) := by
    rw [xac_apply]
    abel
  rw [this]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

theorem conj_xac {γ : W ≃ₗ[ZMod 2] W} (hγ : ∀ u v, ω (γ u) (γ v) = ω u v)
    (hγV : ∀ v ∈ V, γ v ∈ V) (a c : V) :
    γ * xac D a c * γ⁻¹ = xac D ⟨γ a, hγV a a.2⟩ ⟨γ c, hγV c c.2⟩ := by
  refine LinearEquiv.ext fun u => ?_
  have h1 : ω (γ.symm u) a = ω u (γ a) := by
    have := hγ (γ.symm u) a
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have h2 : ω (γ.symm u) c = ω u (γ c) := by
    have := hγ (γ.symm u) c
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  show γ (xac D a c (γ.symm u)) = xac D _ _ u
  rw [xac_apply, xac_apply, map_add, map_add, map_smul, map_smul, h1, h2,
    LinearEquiv.apply_symm_apply]

theorem xac_mul (a c c' : V) : xac D a c * xac D a c' = xac D a (c + c') := by
  refine LinearEquiv.ext fun u => ?_
  have hp : ω u a • (c' : W) + ω u c' • (a : W) ∈ V :=
    V.add_mem (V.smul_mem _ c'.2) (V.smul_mem _ a.2)
  have e1 : ω (u + ω u a • (c' : W) + ω u c' • (a : W)) a = ω u a := by
    rw [add_assoc, map_add, LinearMap.add_apply, D.iso _ hp a a.2, add_zero]
  have e2 : ω (u + ω u a • (c' : W) + ω u c' • (a : W)) c = ω u c := by
    rw [add_assoc, map_add, LinearMap.add_apply, D.iso _ hp c c.2, add_zero]
  show xac D a c (xac D a c' u) = xac D a (c + c') u
  rw [xac_apply D a c (xac D a c' u), xac_apply D a c' u, e1, e2, xac_apply D a (c + c') u]
  simp only [Submodule.coe_add, map_add, smul_add, add_smul]
  module

end Xac

section Perfect

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}
  {Γ : Subgroup (W ≃ₗ[ZMod 2] W)}

theorem SpData.exists_pair (D : SpData ω V) (ξ : Module.Dual (ZMod 2) V) :
    ∃ e : W, ∀ v : V, ω (v : W) e = ξ v := by
  let Φ : W →ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
    (LinearMap.lcomp (ZMod 2) (ZMod 2) V.subtype) ∘ₗ ω.flip
  have hΦ : ∀ e v, Φ e v = ω (v : W) e := fun e v => rfl
  have hker : LinearMap.ker Φ = V := by
    ext e
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      refine D.mem_of_forall fun v hv => ?_
      have := LinearMap.congr_fun h ⟨v, hv⟩
      rw [hΦ] at this
      exact this
    · intro he
      refine LinearMap.ext fun v => ?_
      rw [hΦ, LinearMap.zero_apply]
      exact D.iso v v.2 e he
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hker, D.finrank_V, D.finrank_W] at h1
  have h2 : finrank (ZMod 2) (LinearMap.range Φ) = finrank (ZMod 2) (Module.Dual (ZMod 2) V) := by
    rw [Subspace.dual_finrank_eq, D.finrank_V]
    omega
  have h3 : LinearMap.range Φ = ⊤ := Submodule.eq_top_of_finrank_eq h2
  have : ξ ∈ LinearMap.range Φ := by rw [h3]; trivial
  obtain ⟨e, he⟩ := this
  exact ⟨e, fun v => by rw [← hΦ, he]⟩

variable (hΓ : IsGamma ω V Γ)

@[expose] noncomputable def IsGamma.resHom : ↥Γ →* (V ≃ₗ[ZMod 2] V) where
  toFun γ := hΓ.res γ.2
  map_one' := LinearEquiv.ext fun v => Subtype.ext rfl
  map_mul' γ δ := LinearEquiv.ext fun v => Subtype.ext rfl

theorem IsGamma.resHom_surjective : Function.Surjective hΓ.resHom := by
  intro h
  obtain ⟨γ, hγ, hγh⟩ := hΓ.onto h
  exact ⟨⟨γ, hγ⟩, LinearEquiv.ext fun v => Subtype.ext (hγh v)⟩

theorem xac_self (D : SpData ω V) (a c : V) : xac D a c * xac D a c = 1 :=
  LinearEquiv.ext fun u => xacMap_invol D a c u

theorem IsGamma.xac_mem_commutator (hΓ : IsGamma ω V Γ) (D : SpData ω V)
    (hAlt : AltGrp ω V D ≤ Γ)
    (a b : V) (hab : b ∉ Submodule.span (ZMod 2) {a}) :
    xac D a b ∈ (commutator ↥Γ).map Γ.subtype := by
  obtain ⟨c, hc⟩ := exists_notMem_span_pair D.finrank_V a b
  have hca : c ∉ Submodule.span (ZMod 2) {a} := fun h =>
    hc (Submodule.span_mono (by simp) h)
  have hcba : c + b ∉ Submodule.span (ZMod 2) {a} := by
    intro h
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
    apply hc
    refine Submodule.mem_span_pair.mpr ⟨r, 1, ?_⟩
    rw [one_smul, hr, add_assoc, vec_add_self, add_zero]
  obtain ⟨h, hha, hhc⟩ := exists_fix_apply_eq D.finrank_V hca hcba
  obtain ⟨γ, hγ, hγh⟩ := hΓ.onto h
  have hγa : γ (a : W) = (a : W) := by rw [hγh a, hha]
  have hγc : γ (c : W) = (c : W) + (b : W) := by rw [hγh c, hhc]; rfl
  have hconj := conj_xac D (hΓ.isom γ hγ) (hΓ.stabV γ hγ) a c
  have e1 : (⟨γ a, hΓ.stabV γ hγ a a.2⟩ : V) = a := Subtype.ext hγa
  have e2 : (⟨γ c, hΓ.stabV γ hγ c c.2⟩ : V) = c + b := Subtype.ext hγc
  rw [e1, e2] at hconj
  have hx : xac D a c ∈ AltGrp ω V D := xac_mem_alt D a c
  have hmem : ⁅(⟨γ, hγ⟩ : ↥Γ), (⟨xac D a c, hAlt hx⟩ : ↥Γ)⁆ ∈ commutator ↥Γ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  refine ⟨_, hmem, ?_⟩
  show γ * xac D a c * γ⁻¹ * (xac D a c)⁻¹ = xac D a b
  rw [hconj, inv_eq_of_mul_eq_one_right (xac_self D a c), ← xac_mul D a c b]
  have hcomm : xac D a c * xac D a b = xac D a b * xac D a c := by
    rw [xac_mul, xac_mul, add_comm]
  calc xac D a c * xac D a b * xac D a c = xac D a b * xac D a c * xac D a c := by rw [hcomm]
    _ = xac D a b := by rw [mul_assoc, xac_self, mul_one]

@[expose] def gram (ω : LinearMap.BilinForm (ZMod 2) W) (e : Fin 3 → W) (k l : Fin 3)
    (y : W ≃ₗ[ZMod 2] W) : ZMod 2 :=
  ω (y (e k) - e k) (e l)

theorem gram_mul (D : SpData ω V) (e : Fin 3 → W) (k l : Fin 3) {y z : W ≃ₗ[ZMod 2] W}
    (hy : IsF ω V y) (hz : IsF ω V z) :
    gram ω e k l (y * z) = gram ω e k l y + gram ω e k l z := by
  unfold gram
  rw [hy.mul_sub D hz, map_add, LinearMap.add_apply]

@[expose] def pw (x : W ≃ₗ[ZMod 2] W) (ε : ZMod 2) : W ≃ₗ[ZMod 2] W := if ε = 0 then 1 else x

theorem pw_isF {x : W ≃ₗ[ZMod 2] W} (hx : IsF ω V x) (ε : ZMod 2) : IsF ω V (pw x ε) := by
  unfold pw
  split_ifs
  · exact IsF.one
  · exact hx

theorem gram_pw (e : Fin 3 → W) (k l : Fin 3) (x : W ≃ₗ[ZMod 2] W) (ε : ZMod 2) :
    gram ω e k l (pw x ε) = ε * gram ω e k l x := by
  rcases zmod2_cases ε with rfl | rfl
  · simp [pw, gram]
  · simp [pw]

theorem pw_mem {Q : Subgroup (W ≃ₗ[ZMod 2] W)} {x : W ≃ₗ[ZMod 2] W} (hx : x ∈ Q) (ε : ZMod 2) :
    pw x ε ∈ Q := by
  unfold pw
  split_ifs
  · exact one_mem _
  · exact hx

theorem IsGamma.alt_le_commutator (hΓ : IsGamma ω V Γ) (D : SpData ω V)
    (hAlt : AltGrp ω V D ≤ Γ) :
    AltGrp ω V D ≤ (commutator ↥Γ).map Γ.subtype := by
  classical
  let a := Module.finBasisOfFinrankEq (ZMod 2) V D.finrank_V
  choose e he using fun j : Fin 3 => D.exists_pair (a.coord j)
  have hae : ∀ i j : Fin 3, ω (a i : W) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [he j (a i)]
    simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  have hind : ∀ i j : Fin 3, i ≠ j → a j ∉ Submodule.span (ZMod 2) {a i} := by
    intro i j hij hmem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrArg (a.coord j) hr
    simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, hij.symm, hij] at this
  have h01 := hΓ.xac_mem_commutator D hAlt (a 0) (a 1) (hind 0 1 (by decide))
  have h02 := hΓ.xac_mem_commutator D hAlt (a 0) (a 2) (hind 0 2 (by decide))
  have h12 := hΓ.xac_mem_commutator D hAlt (a 1) (a 2) (hind 1 2 (by decide))
  set x01 := xac D (a 0) (a 1) with hx01
  set x02 := xac D (a 0) (a 2) with hx02
  set x12 := xac D (a 1) (a 2) with hx12
  set Q : Subgroup (W ≃ₗ[ZMod 2] W) := Subgroup.closure {x01, x02, x12} with hQ
  have hQle : Q ≤ AltGrp ω V D := by
    rw [hQ, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact xac_mem_alt D _ _
  have hQH : Q ≤ (commutator ↥Γ).map Γ.subtype := by
    rw [hQ, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h01
    · exact h02
    · exact h12
  have hx01Q : x01 ∈ Q := Subgroup.subset_closure (by simp)
  have hx02Q : x02 ∈ Q := Subgroup.subset_closure (by simp)
  have hx12Q : x12 ∈ Q := Subgroup.subset_closure (by simp)
  let ι : (Fin 3 → ZMod 2) → (W ≃ₗ[ZMod 2] W) :=
    fun ε => pw x01 (ε 0) * pw x02 (ε 1) * pw x12 (ε 2)
  have hιQ : ∀ ε, ι ε ∈ Q := fun ε =>
    mul_mem (mul_mem (pw_mem hx01Q _) (pw_mem hx02Q _)) (pw_mem hx12Q _)
  have hιF : ∀ ε, IsF ω V (ι ε) := fun ε =>
    ((pw_isF (xac_isF D _ _) _).mul (pw_isF (xac_isF D _ _) _)).mul (pw_isF (xac_isF D _ _) _)
  have hg : ∀ (i j k l : Fin 3), gram ω e k l (xac D (a i) (a j)) =
      (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        (if j = k then 1 else 0) * (if i = l then 1 else 0) := by
    intro i j k l
    unfold gram
    rw [xac_sub_apply, D.symm (e k) (a i), D.symm (e k) (a j), hae, hae, hae, hae]
  have hgι : ∀ (k l : Fin 3) (ε : Fin 3 → ZMod 2), gram ω e k l (ι ε) =
      ε 0 * gram ω e k l x01 + ε 1 * gram ω e k l x02 + ε 2 * gram ω e k l x12 := by
    intro k l ε
    have hF01 := pw_isF (xac_isF D (a 0) (a 1)) (ε 0)
    have hF02 := pw_isF (xac_isF D (a 0) (a 2)) (ε 1)
    have hF12 := pw_isF (xac_isF D (a 1) (a 2)) (ε 2)
    show gram ω e k l (pw x01 (ε 0) * pw x02 (ε 1) * pw x12 (ε 2)) = _
    rw [gram_mul D e k l (hF01.mul hF02) hF12, gram_mul D e k l hF01 hF02, gram_pw, gram_pw,
      gram_pw]
  have hinj : Function.Injective ι := by
    intro ε ε' h
    have g01 := congrArg (gram ω e 0 1) h
    have g02 := congrArg (gram ω e 0 2) h
    have g12 := congrArg (gram ω e 1 2) h
    simp only [hgι, hx01, hx02, hx12, hg] at g01 g02 g12
    simp at g01 g02 g12
    funext i
    fin_cases i
    · simpa using g01
    · simpa using g02
    · simpa using g12
  have hcard : 8 ≤ Nat.card Q := by
    let ι' : (Fin 3 → ZMod 2) → Q := fun ε => ⟨ι ε, hιQ ε⟩
    have hι' : Function.Injective ι' := fun ε ε' h => hinj (congrArg Subtype.val h)
    have := Nat.card_le_card_of_injective ι' hι'
    have h8 : Nat.card (Fin 3 → ZMod 2) = 8 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
      simp
    omega
  have hQeq : Q = AltGrp ω V D := eq_alt_of_card D hQle hcard
  rw [← hQeq]
  exact hQH

theorem IsGamma.commutator_eq_top (hΓ : IsGamma ω V Γ) (D : SpData ω V)
    (hAlt : AltGrp ω V D ≤ Γ)
    (hF : ∀ γ ∈ Γ, (∀ v ∈ V, γ v = v) → γ ∈ AltGrp ω V D) : commutator ↥Γ = ⊤ := by
  refine eq_top_iff.mpr fun γ _ => ?_
  have hmap : (commutator ↥Γ).map hΓ.resHom = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective _ hΓ.resHom_surjective, ← commutator_def]
    exact commutator_gl3_eq_top D.finrank_V
  have hγ : hΓ.resHom γ ∈ (commutator ↥Γ).map hΓ.resHom := by
    rw [hmap]
    trivial
  obtain ⟨h, hh, hhγ⟩ := hγ
  set δ : ↥Γ := h⁻¹ * γ with hδ
  have hδ1 : hΓ.resHom δ = 1 := by
    rw [hδ, map_mul, map_inv, hhγ, inv_mul_cancel]
  have hδV : ∀ v ∈ V, (δ : W ≃ₗ[ZMod 2] W) v = v := by
    intro v hv
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => ((f ⟨v, hv⟩ : V) : W)) hδ1
    exact this
  have hδA := hF δ δ.2 hδV
  obtain ⟨h', hh', hh'δ⟩ := hΓ.alt_le_commutator D hAlt hδA
  have : h' = δ := Subtype.ext hh'δ
  rw [this] at hh'
  have e : γ = h * δ := by rw [hδ]; group
  rw [e]
  exact mul_mem hh hh'

end Perfect

end CFSG.GF2Type.Smith1979.Case2.Sp

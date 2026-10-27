module

public import CFSG.LieType.AlgebraicGroups.ExactRootGroupBaseChange
public import CFSG.LieType.Chevalley.LangPrimeFieldInvolutionTorus
public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import Mathlib.FieldTheory.AlgebraicClosure
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TensorProduct

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k]

theorem comp_convOne' {C D F : Type} [CommRing C] [Bialgebra k C] [CommRing D] [Algebra k D]
    [CommRing F] [Algebra k F] (z : D →ₐ[k] F) :
    toConv (z.comp (1 : WithConv (C →ₐ[k] D)).ofConv) = 1 := by
  rw [← TauCeti.AlgHom.mapValue_apply, map_one]

theorem antipode_comp_mul_self {A F : Type} [CommRing A] [HopfAlgebra k A] [CommRing F]
    [Algebra k F] (φ : A →ₐ[k] F) :
    toConv (φ.comp (HopfAlgebra.antipodeAlgHom k A)) * toConv φ = 1 := by
  rw [toConv_comp_antipodeAlgHom, inv_mul_cancel]

theorem convMul_apply_glEntry {F : Type} [CommRing F] [Algebra k F]
    (u v : WithConv (GLCoord k (Label τ) →ₐ[k] F)) (a b : Label τ) :
    (u * v).ofConv (glEntry k (Label τ) a b) =
      ∑ l, u.ofConv (glEntry k (Label τ) a l) * v.ofConv (glEntry k (Label τ) l b) := by
  rw [AlgHom.convMul_apply, comul_glEntry, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul]

theorem endMatrix_mul
    {F : Type} [CommRing F] (A B : Module.End F (RootModule τ F)) :
    endMatrix τ (A * B) = endMatrix τ A * endMatrix τ B := by
  unfold endMatrix
  rw [map_mul]

theorem endMatrix_one {F : Type} [CommRing F] :
    endMatrix τ (1 : Module.End F (RootModule τ F)) = 1 := by
  unfold endMatrix
  rw [map_one]

variable (k) in
@[expose] def unitCoHom (F : Type) [CommRing F] [Algebra k F] :
    (Module.End F (RootModule τ F))ˣ →* WithConv (GLCoord k (Label τ) →ₐ[k] F) where
  toFun g := toConv (unitCo k g)
  map_one' := by
    apply ofConv_injective
    refine GLCoord.algHom_ext_of_entries fun a b => ?_
    rw [ofConv_toConv, unitCo, GLCoord.lift_glEntry, Units.val_one, endMatrix_one,
      AlgHom.convOne_def, ofConv_toConv, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
      counit_glEntry]
    by_cases h : a = b <;> simp [h, Matrix.one_apply]
  map_mul' g h := by
    apply ofConv_injective
    refine GLCoord.algHom_ext_of_entries fun a b => ?_
    rw [ofConv_toConv, convMul_apply_glEntry, unitCo, GLCoord.lift_glEntry, Units.val_mul,
      endMatrix_mul, Matrix.mul_apply]
    simp only [unitCo, GLCoord.lift_glEntry]

theorem unitCoHom_apply {F : Type} [CommRing F] [Algebra k F]
    (g : (Module.End F (RootModule τ F))ˣ) : unitCoHom k F g = toConv (unitCo k g) :=
  rfl

theorem unitCo_comp_antipode {F : Type} [CommRing F] [Algebra k F]
    (g : (Module.End F (RootModule τ F))ˣ) :
    (unitCo k g).comp (HopfAlgebra.antipodeAlgHom k (GLCoord k (Label τ))) = unitCo k g⁻¹ := by
  have h : toConv (unitCo k g) * toConv (unitCo k g⁻¹) = 1 := by
    rw [← unitCoHom_apply, ← unitCoHom_apply, ← map_mul, mul_inv_cancel, map_one]
  exact toConv_injective <| (toConv_comp_antipodeAlgHom _).trans (inv_eq_of_mul_eq_one_right h)

theorem modGLPoint_ofConv_eq_unitCo (g : ModGL τ k) :
    (modGLPoint τ k g).ofConv = unitCo k (D := k) g :=
  GLCoord.algHom_ext_of_entries fun a b => by rw [modGLPoint_apply_glEntry, unitCo_glEntry]

variable (τ k) in
@[expose] def sqEqns : Set (GLCoord k (Label τ)) :=
  Set.range fun p : Label τ × Label τ =>
    (glEntryMatrix k (Label τ) * glEntryMatrix k (Label τ) - 1) p.1 p.2

theorem mapMatrix_glEntryMatrix_unitCo
    {F : Type} [CommRing F] [Algebra k F]
    (g : (Module.End F (RootModule τ F))ˣ) :
    (unitCo k g).mapMatrix (glEntryMatrix k (Label τ)) =
      endMatrix τ (g : Module.End F (RootModule τ F)) := by
  ext a b
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, glEntryMatrix_apply, unitCo,
    GLCoord.lift_glEntry]

theorem unitCo_kills_sqEqns_iff
    {F : Type} [Field F] [Algebra k F] (g : ModGL τ F) :
    (∀ f ∈ Ideal.span (sqEqns τ k), unitCo k (D := F) g f = 0) ↔ g ^ 2 = 1 := by
  have hentry : ∀ a b, unitCo k (D := F) g
      ((glEntryMatrix k (Label τ) * glEntryMatrix k (Label τ) - 1) a b) =
      (endMatrix τ ((g ^ 2 : ModGL τ F) : Module.End F (RootModule τ F)) - 1) a b := by
    intro a b
    have h := congrArg (fun M => M a b)
      (map_sub (unitCo k (D := F) g).mapMatrix
        (glEntryMatrix k (Label τ) * glEntryMatrix k (Label τ)) 1)
    simp only [map_mul, map_one, mapMatrix_glEntryMatrix_unitCo] at h
    rw [sq, Units.val_mul, endMatrix_mul]
    simpa only [AlgHom.mapMatrix_apply, Matrix.map_apply] using h
  constructor
  · intro h
    have hM : endMatrix τ ((g ^ 2 : ModGL τ F) : Module.End F (RootModule τ F)) = 1 := by
      refine sub_eq_zero.1 (Matrix.ext fun a b => ?_)
      rw [← hentry]
      exact h _ (Ideal.subset_span ⟨(a, b), rfl⟩)
    refine Units.ext ?_
    have hinj := (LinearMap.toMatrixAlgEquiv
      (Finsupp.basisSingleOne : Module.Basis (Label τ) F (Label τ →₀ F))).injective
    apply hinj
    change endMatrix τ _ = endMatrix τ _
    rw [hM, Units.val_one, endMatrix_one]
  · intro h f hf
    have hle : sqEqns τ k ⊆ RingHom.ker (unitCo k (D := F) g) := by
      rintro _ ⟨⟨a, b⟩, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, hentry, h, Units.val_one, endMatrix_one, sub_self]
      rfl
    exact (Ideal.span_le.2 hle) hf

theorem baseChange_rootDiag {K K' : Type} [Field K] [Field K'] (f : K →+* K')
    (a : Fin τ.rank → Kˣ) :
    BaseChange f (rootDiag a) (rootDiag fun i => Units.map f.toMonoidHom (a i)) := by
  rintro (i | α)
  · rw [rootDiag_single_inl, rootDiag_single_inl, Finsupp.mapRange_single, map_one]
  · rw [rootDiag_single_inr, rootDiag_single_inr, Finsupp.smul_single_one,
      Finsupp.smul_single_one, Finsupp.mapRange_single]
    congr 1
    simp [map_prod, map_zpow₀]

@[expose] def conjDiagCo {B : Type} [CommRing B] [Algebra k B]
    (mk : GLCoord k (Label τ) →ₐ[k] B) (d : GLCoord k (Label τ) →ₐ[k] k) :
    GLCoord k (Label τ) →ₐ[k] B :=
  (toConv (mk.comp (HopfAlgebra.antipodeAlgHom k (GLCoord k (Label τ)))) *
    toConv ((Algebra.ofId k B).comp d) * toConv mk).ofConv

theorem comp_conjDiagCo
    {B F : Type} [CommRing B] [Algebra k B] [Field F] [Algebra k F]
    (mk : GLCoord k (Label τ) →ₐ[k] B) (d : ModGL τ k) (z : B →ₐ[k] F) (g d' : ModGL τ F)
    (hg : z.comp mk = unitCo k (D := F) g)
    (hd : BaseChange (algebraMap k F) (d : Module.End k (RootModule τ k))
      (d' : Module.End F (RootModule τ F))) :
    z.comp (conjDiagCo mk (modGLPoint τ k d).ofConv) = unitCo k (D := F) (g⁻¹ * d' * g) := by
  have hc : z.comp ((Algebra.ofId k B).comp (modGLPoint τ k d).ofConv) = unitCo k (D := F) d' := by
    rw [← AlgHom.comp_assoc, show z.comp (Algebra.ofId k B) = Algebra.ofId k F from
      Subsingleton.elim _ _, modGLPoint_ofConv_eq_unitCo]
    exact comp_unitCo_of_baseChange' (Algebra.ofId k F) _ _ hd
  unfold conjDiagCo
  rw [AlgHom.comp_convMul_distrib, ofConv_toConv, AlgHom.comp_convMul_distrib, ofConv_toConv,
    ofConv_toConv, ofConv_toConv, ← AlgHom.comp_assoc, hg, hc, unitCo_comp_antipode]
  apply toConv_injective
  rw [toConv_ofConv, ← unitCoHom_apply, ← unitCoHom_apply, ← unitCoHom_apply, ← map_mul,
    ← map_mul]
  rfl


theorem exceptional_Lang_inner_involution_torus_conjugacy
    (τ : Tag) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (L : Type) [Field L] [IsAlgClosed L] [CharP L p] {x : ModGL τ L}
    (hx : x ∈ adjointGroup τ L) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ adjointGroup τ L, ∃ a : Fin τ.rank → Lˣ, (∀ i, a i = 1 ∨ a i = -1) ∧
      g * x * g⁻¹ = rootDiagUnit τ a := by
  classical
  let : Algebra (ZMod p) L := ZMod.algebra L p
  let k := algebraicClosure (ZMod p) L
  have : IsAlgClosed k := IsAlgClosure.isAlgClosed (ZMod p)
  have : CharP k p := ((algebraMap k L).charP_iff_charP p).2 inferInstance
  have hAlgEq : ZMod.algebra k p = (algebraicClosure (ZMod p) L).algebra' :=
    Algebra.algebra_ext _ _ fun r => congrArg (fun f : ZMod p →+* k => f r)
      (RingHom.ext_zmod _ _)
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k := by
    rw [hAlgEq]
    exact algebraicClosure.isAlgebraic (ZMod p) L
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  have hneg : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hk2 (by simpa using congrArg Units.val h)
  set I := subgroupIdeal (adjointPointSubgroup τ k) with hIdef
  have hc := (exceptional_Lang_exact_affine_group_realization k τ).1.2.1
  have : IsReduced (GLCoord k (Label τ) ⧸ I) := hc.isReduced
  have : Algebra.FiniteType k (GLCoord k (Label τ) ⧸ I) := hc.finiteType
  set Jy := I ⊔ Ideal.span (sqEqns τ k) with hJy
  let mkG := Ideal.Quotient.mkₐ k I
  have hptsG : ∀ y : GLCoord k (Label τ) →ₐ[k] k, (∀ f ∈ I, y f = 0) →
      (modGLPoint τ k).symm (toConv y) ∈ adjointGroup τ k := by
    intro y hy
    have h0 : y ∈ pointsZero k I := hy
    rw [hc.pointsZero_eq] at h0
    obtain ⟨g', hg', hgeq⟩ := h0
    rw [← hgeq]
    simpa using hg'
  let sgn : ∀ {F : Type} [Field F], (Fin τ.rank → Bool) → Fin τ.rank → Fˣ :=
    fun b i => if b i then 1 else -1
  have hsgn : ∀ b, (fun i => Units.map (algebraMap k L).toMonoidHom (sgn (F := k) b i)) =
      sgn (F := L) b := by
    intro b
    funext i
    by_cases h : b i <;> simp [sgn, h]
  let dk : (Fin τ.rank → Bool) → ModGL τ k := fun b => rootDiagUnit τ (sgn b)
  have hdk : ∀ b, dk b ∈ adjointGroup τ k := fun b =>
    (exceptional_Lang_adjoint_diagonal_lift τ k (sgn b)).1
  have hdk2 : ∀ b, dk b ^ 2 = 1 := fun b => by
    apply Units.ext
    rw [sq, Units.val_mul, Units.val_one]
    change rootDiag (sgn b) * rootDiag (sgn b) = 1
    rw [rootDiag_mul_rootDiag]
    convert rootDiag_one (τ := τ) (K := k)
    funext i
    by_cases h : b i <;> simp [sgn, h]
  have hdL : ∀ b, BaseChange (algebraMap k L) ((dk b : ModGL τ k) : Module.End k (RootModule τ k))
      ((rootDiagUnit τ (sgn (F := L) b) : ModGL τ L) : Module.End L (RootModule τ L)) := by
    intro b
    have h := baseChange_rootDiag (τ := τ) (algebraMap k L) (sgn (F := k) b)
    rw [hsgn] at h
    exact h
  have hdk' : ∀ b, BaseChange (algebraMap k k) ((dk b : ModGL τ k) :
      Module.End k (RootModule τ k)) ((dk b : ModGL τ k) : Module.End k (RootModule τ k)) := by
    intro b a
    exact Finsupp.ext fun c => by simp
  let ψ : (Fin τ.rank → Bool) → (GLCoord k (Label τ) →ₐ[k] (GLCoord k (Label τ) ⧸ I)) :=
    fun b => conjDiagCo mkG (modGLPoint τ k (dk b)).ofConv
  have hψk : ∀ b (z : (GLCoord k (Label τ) ⧸ I) →ₐ[k] k), ∃ h ∈ adjointGroup τ k,
      z.comp (ψ b) = unitCo k (D := k) (h⁻¹ * dk b * h) ∧
        z.comp mkG = unitCo k (D := k) h := by
    intro b z
    have hzI : ∀ f ∈ I, (z.comp mkG) f = 0 := fun f hf => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hf,
        map_zero]
    set h := (modGLPoint τ k).symm (toConv (z.comp mkG)) with hh
    have hhz : z.comp mkG = unitCo k (D := k) h := by
      rw [← modGLPoint_ofConv_eq_unitCo, hh, MulEquiv.apply_symm_apply, ofConv_toConv]
    exact ⟨h, hptsG _ hzI, comp_conjDiagCo mkG (dk b) z h (dk b) hhz (hdk' b), hhz⟩
  have hψJ : ∀ b, ∀ f ∈ Jy, ψ b f = 0 := by
    intro b f hf
    refine eq_zero_of_forall_algHom k _ _ fun z => ?_
    obtain ⟨h, hh, hz, -⟩ := hψk b z
    change (z.comp (ψ b)) f = 0
    rw [hz]
    have hmem : h⁻¹ * dk b * h ∈ adjointGroup τ k :=
      mul_mem (mul_mem (inv_mem hh) (hdk b)) hh
    have hsq : (h⁻¹ * dk b * h) ^ 2 = 1 := by
      rw [sq, show h⁻¹ * dk b * h * (h⁻¹ * dk b * h) = h⁻¹ * (dk b * dk b) * h by group,
        ← sq, hdk2, mul_one, inv_mul_cancel]
    have hI' : ∀ f ∈ I, unitCo k (D := k) (h⁻¹ * dk b * h) f = 0 := by
      intro f hf
      rw [← modGLPoint_ofConv_eq_unitCo]
      exact (mem_subgroupIdeal.1 hf) _ ⟨_, hmem, rfl⟩
    have hS' := (unitCo_kills_sqEqns_iff (k := k) (h⁻¹ * dk b * h)).2 hsq
    have hle : Jy ≤ RingHom.ker (unitCo k (D := k) (h⁻¹ * dk b * h)) :=
      sup_le (fun f hf => hI' f hf) (fun f hf => hS' f hf)
    exact hle hf
  let φ : (Fin τ.rank → Bool) → ((GLCoord k (Label τ) ⧸ Jy) →ₐ[k] (GLCoord k (Label τ) ⧸ I)) :=
    fun b => Ideal.Quotient.liftₐ Jy (ψ b) (hψJ b)
  have hφc : ∀ b, (φ b).comp (Ideal.Quotient.mkₐ k Jy) = ψ b := fun b =>
    Ideal.Quotient.liftₐ_comp _ _ _
  have hsurj : ∀ y : (GLCoord k (Label τ) ⧸ Jy) →ₐ[k] k,
      ∃ b, ∃ z : (GLCoord k (Label τ) ⧸ I) →ₐ[k] k, z.comp (φ b) = y := by
    intro y
    set y₀ := y.comp (Ideal.Quotient.mkₐ k Jy) with hy₀
    have hy₀J : ∀ f ∈ Jy, y₀ f = 0 := fun f hf => by
      rw [hy₀, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hf,
        map_zero]
    set x₀ := (modGLPoint τ k).symm (toConv y₀) with hx₀
    have hx₀y : unitCo k (D := k) x₀ = y₀ := by
      rw [← modGLPoint_ofConv_eq_unitCo, hx₀, MulEquiv.apply_symm_apply, ofConv_toConv]
    have hx₀C : x₀ ∈ adjointGroup τ k :=
      hptsG _ fun f hf => hy₀J f (Ideal.mem_sup_left hf)
    have hx₀2 : x₀ ^ 2 = 1 := (unitCo_kills_sqEqns_iff x₀).1 fun f hf => by
      rw [hx₀y]
      exact hy₀J f (Ideal.mem_sup_right hf)
    obtain ⟨h, hh, a, ha, hconj⟩ :=
      exceptional_Lang_algebraic_prime_field_involution_torus hp2 k halg τ hx₀C hx₀2
    let b : Fin τ.rank → Bool := fun i => decide (a i = 1)
    have hab : sgn (F := k) b = a := by
      funext i
      rcases ha i with h1 | h1 <;> simp [sgn, b, h1, hneg]
    have hhI : ∀ f ∈ I, (modGLPoint τ k h).ofConv f = 0 := fun f hf =>
      (mem_subgroupIdeal.1 hf) _ ⟨_, hh, rfl⟩
    let z : (GLCoord k (Label τ) ⧸ I) →ₐ[k] k := Ideal.Quotient.liftₐ I _ hhI
    refine ⟨b, z, Ideal.Quotient.algHom_ext k ?_⟩
    rw [AlgHom.comp_assoc, hφc]
    have hzmk : z.comp mkG = unitCo k (D := k) h := by
      rw [← modGLPoint_ofConv_eq_unitCo]
      exact Ideal.Quotient.liftₐ_comp _ _ _
    rw [comp_conjDiagCo mkG (dk b) z h (dk b) hzmk (hdk' b), ← hy₀, ← hx₀y]
    congr 1
    have hdb : dk b = rootDiagUnit τ a := by
      change rootDiagUnit τ (sgn b) = _
      rw [hab]
    rw [hdb, ← hconj]
    group
  have hbc := exceptional_Lang_exact_root_group_base_change k L τ
  have hxI : ∀ f ∈ I, unitCo k (D := L) x f = 0 := (hbc.2.2.1 x).1 hx
  have hxS := (unitCo_kills_sqEqns_iff (k := k) x).2 hx2
  have hxJ : ∀ f ∈ Jy, unitCo k (D := L) x f = 0 := fun f hf =>
    (sup_le (fun f hf => hxI f hf) (fun f hf => hxS f hf) :
      Jy ≤ RingHom.ker (unitCo k (D := L) x)) hf
  obtain ⟨b, z, hz⟩ := exceptional_Lang_constructible_point_surjectivity_field_extension
    (fun _ : Fin τ.rank → Bool => GLCoord k (Label τ) ⧸ I) φ hsurj
    (Ideal.Quotient.liftₐ Jy (unitCo k (D := L) x) hxJ)
  obtain ⟨g, hg0⟩ := (hbc.1.2 (z.comp mkG))
  have hg : unitCo k (D := L) g = z.comp mkG := hg0
  have hgC : g ∈ adjointGroup τ L := by
    refine (hbc.2.2.1 g).2 fun f hf => ?_
    rw [hg, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hf,
      map_zero]
  have hxg : unitCo k (D := L) x =
      unitCo k (D := L) (g⁻¹ * rootDiagUnit τ (sgn (F := L) b) * g) := by
    rw [← comp_conjDiagCo mkG (dk b) z g _ hg.symm (hdL b)]
    calc unitCo k (D := L) x = (Ideal.Quotient.liftₐ Jy (unitCo k (D := L) x) hxJ).comp
          (Ideal.Quotient.mkₐ k Jy) := (Ideal.Quotient.liftₐ_comp _ _ _).symm
      _ = (z.comp (φ b)).comp (Ideal.Quotient.mkₐ k Jy) := by rw [hz]
      _ = z.comp (ψ b) := by rw [AlgHom.comp_assoc, hφc]
  have hxeq := hbc.1.1 hxg
  refine ⟨g, hgC, sgn (F := L) b, fun i => ?_, ?_⟩
  · by_cases h : b i <;> simp [sgn, h]
  · have hxeq' : x = g⁻¹ * rootDiagUnit τ (sgn (F := L) b) * g := hxeq
    rw [hxeq']
    group

end CFSG.LieType.AlgebraicGroups

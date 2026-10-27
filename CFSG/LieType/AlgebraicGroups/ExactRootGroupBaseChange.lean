module

public import CFSG.LieType.AlgebraicGroups.ExactAffineRealization
public import CFSG.LieType.AlgebraicGroups.PointSurjectivityExtension
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv
open TensorProduct

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k]

theorem comp_unitCo_of_baseChange'
    {D D' : Type} [CommRing D] [Algebra k D] [CommRing D']
    [Algebra k D'] (z : D →ₐ[k] D') (g : (Module.End D (RootModule τ D))ˣ)
    (g' : (Module.End D' (RootModule τ D'))ˣ)
    (h : BaseChange (z : D →+* D') (g : Module.End D (RootModule τ D))
      (g' : Module.End D' (RootModule τ D'))) :
    z.comp (unitCo k g) = unitCo k g' := by
  refine GLCoord.algHom_ext_of_entries fun a b => ?_
  rw [AlgHom.comp_apply, unitCo, GLCoord.lift_glEntry, unitCo, GLCoord.lift_glEntry,
    endMatrix_apply, endMatrix_apply, ← h b, Finsupp.mapRange_apply]
  rfl

theorem unitCo_glEntry
    {L : Type} [Field L] [Algebra k L] (g : ModGL τ L) (a b : Label τ) :
    unitCo k (D := L) g (glEntry k (Label τ) a b) =
      (g : Module.End L (RootModule τ L)) (Finsupp.single b 1) a := by
  rw [unitCo, GLCoord.lift_glEntry, endMatrix_apply]

theorem unitCo_injective {L : Type} [Field L] [Algebra k L] :
    Function.Injective (fun g : ModGL τ L => unitCo k (D := L) g) := by
  intro g g' h
  have h' : ∀ a b, (g : Module.End L (RootModule τ L)) (Finsupp.single b 1) a =
      (g' : Module.End L (RootModule τ L)) (Finsupp.single b 1) a := by
    intro a b
    have := congrArg (fun y : GLCoord k (Label τ) →ₐ[k] L => y (glEntry k (Label τ) a b)) h
    simpa only [unitCo_glEntry] using this
  refine Units.ext (Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  exact Finsupp.ext fun a => h' a b

theorem exists_unitCo_eq
    {L : Type} [Field L] [Algebra k L] (y : GLCoord k (Label τ) →ₐ[k] L) :
    ∃ g : ModGL τ L, unitCo k (D := L) g = y := by
  let M : Matrix (Label τ) (Label τ) L := Matrix.of fun a b => y (glEntry k (Label τ) a b)
  have hdet : M.det * y (glDetInv k (Label τ)) = 1 := by
    have := congrArg y (det_glEntryMatrix_mul_glDetInv k (Label τ))
    rw [map_mul, map_one, GLCoord.map_det] at this
    exact this
  let G : Matrix.GeneralLinearGroup (Label τ) L :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M (left_ne_zero_of_mul_eq_one hdet)
  refine ⟨(modGLEquivGL τ L).symm G, GLCoord.algHom_ext_of_entries fun a b => ?_⟩
  rw [unitCo_glEntry, ← modGLEquivGL_apply, MulEquiv.apply_symm_apply]
  rfl

theorem comp_eq_zero_of_points
    [IsAlgClosed k] {D : Type} [CommRing D] [Algebra k D]
    [Algebra.FiniteType k D] [IsReduced D] (φ : GLCoord k (Label τ) →ₐ[k] D)
    (hφ : ∀ z : D →ₐ[k] k, (modGLPoint τ k).symm (toConv (z.comp φ)) ∈ adjointGroup τ k) :
    ∀ f ∈ subgroupIdeal (adjointPointSubgroup τ k), φ f = 0 := by
  intro f hf
  refine eq_zero_of_forall_algHom k D (φ f) fun z => ?_
  have hmem : toConv (z.comp φ) ∈ adjointPointSubgroup τ k :=
    ⟨_, hφ z, MulEquiv.apply_symm_apply _ _⟩
  exact (mem_subgroupIdeal.1 hf) _ hmem

theorem mapWord_freeWord' {L : Type} [CommRing L] [Algebra k L] {n : ℕ} (ℓ : Fin n → Letter τ)
    (z : MvPolynomial (Fin n) k →ₐ[k] L) :
    mapWord (z : MvPolynomial (Fin n) k →+* L) (freeWord (k := k) ℓ) =
      List.ofFn fun j => (ℓ j, z (MvPolynomial.X j)) := by
  simp [freeWord, mapWord, List.map_ofFn, Function.comp_def]

theorem exceptional_Lang_exact_root_group_base_change
    (k L : Type) [Field k] [IsAlgClosed k]
    [Field L] [IsAlgClosed L] [Algebra k L] (τ : Tag) :
    Function.Bijective (fun g : ModGL τ L => unitCo k (D := L) g) ∧
    (∀ (g : ModGL τ L) (a b : Label τ), unitCo k (D := L) g (glEntry k (Label τ) a b) =
      (g : Module.End L (RootModule τ L)) (Finsupp.single b 1) a) ∧
    (∀ g : ModGL τ L, g ∈ adjointGroup τ L ↔
      ∀ f ∈ subgroupIdeal (adjointPointSubgroup τ k), unitCo k (D := L) g f = 0) ∧
    ∀ g : ModGL τ L, g ∈ adjointGroup τ L ↔
      ∃ y : L ⊗[k] (GLCoord k (Label τ) ⧸ subgroupIdeal (adjointPointSubgroup τ k)) →ₐ[L] L,
        ((AlgHom.liftEquiv k L _ L).symm y).comp (Ideal.Quotient.mkₐ k _) =
          unitCo k (D := L) g := by
  set I := subgroupIdeal (adjointPointSubgroup τ k) with hIdef
  have hmain : ∀ g : ModGL τ L, g ∈ adjointGroup τ L ↔ ∀ f ∈ I, unitCo k (D := L) g f = 0 := by
    intro g
    constructor
    · intro hg
      obtain ⟨w, hw⟩ := exists_wordElt_eq (⟨g, hg⟩ : adjointGroup τ L)
      let ℓ : Fin w.length → Letter τ := fun j => (w.get j).1
      let c : Fin w.length → L := fun j => (w.get j).2
      let φ := unitCo k (wordUnit τ (MvPolynomial (Fin w.length) k) (freeWord ℓ))
      have hφ : ∀ f ∈ I, φ f = 0 := comp_eq_zero_of_points φ fun z => by
        rw [comp_unitCo_wordUnit, toConv_ofConv, MulEquiv.symm_apply_apply, ← coe_wordElt]
        exact (wordElt τ _).2
      have hz : (MvPolynomial.aeval c).comp φ = unitCo k (D := L) g := by
        rw [comp_unitCo_of_baseChange' _ _ _ (baseChange_wordUnit _ _), mapWord_freeWord']
        congr 1
        simp only [MvPolynomial.aeval_X]
        rw [show (List.ofFn fun j => (ℓ j, c j)) = w from List.ofFn_get w, ← coe_wordElt, hw]
      intro f hf
      rw [← hz, AlgHom.comp_apply, hφ f hf, map_zero]
    · intro hkill
      let y : (GLCoord k (Label τ) ⧸ I) →ₐ[k] L := Ideal.Quotient.liftₐ I (unitCo k g) hkill
      obtain ⟨N, α, hα, hαr⟩ := exists_enum (finite_posRoots τ)
      choose m β hβ hβr using fun w : WeylGroup τ => exists_enum (inversionSet_finite w)
      have hμ : ∀ w, ∀ f ∈ I, bruhatCo τ k w α (β w) f = 0 := fun w =>
        comp_eq_zero_of_points _ fun z => by
          rw [bruhatCo, comp_unitCo_wordUnit, toConv_ofConv, MulEquiv.symm_apply_apply,
            ← coe_wordElt]
          exact (wordElt τ _).2
      let μ : ∀ w, (GLCoord k (Label τ) ⧸ I) →ₐ[k] TorusAffine k τ.rank (N + m w) := fun w =>
        Ideal.Quotient.liftₐ I (bruhatCo τ k w α (β w)) (hμ w)
      have hμc : ∀ w, (μ w).comp (Ideal.Quotient.mkₐ k I) = bruhatCo τ k w α (β w) := fun w =>
        Ideal.Quotient.liftₐ_comp _ _ _
      have hc := (exceptional_Lang_exact_affine_group_realization k τ).1.2.1
      have hcov := (exceptional_Lang_rootword_Bruhat_regular_cover τ k).2.2.1 α hα hαr m β hβ hβr
      have hsurj : ∀ y' : (GLCoord k (Label τ) ⧸ I) →ₐ[k] k,
          ∃ w, ∃ z : TorusAffine k τ.rank (N + m w) →ₐ[k] k, z.comp (μ w) = y' := by
        intro y'
        have h0 : y'.comp (Ideal.Quotient.mkₐ k I) ∈ pointsZero k I := fun a ha => by
          rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 ha,
            map_zero]
        rw [hc.pointsZero_eq] at h0
        obtain ⟨g', hg', hgeq⟩ := h0
        have hpts : y'.comp (Ideal.Quotient.mkₐ k I) ∈ groupPoints τ k := by
          show (modGLPoint τ k).symm (toConv _) ∈ adjointGroup τ k
          rw [← hgeq]
          simpa using hg'
        rw [← hcov] at hpts
        obtain ⟨w, z, hz⟩ := Set.mem_iUnion.1 hpts
        refine ⟨w, z, Ideal.Quotient.algHom_ext k ?_⟩
        rw [AlgHom.comp_assoc, hμc]
        exact hz
      obtain ⟨w, z, hz⟩ := exceptional_Lang_constructible_point_surjectivity_field_extension
        (fun w : WeylGroup τ => TorusAffine k τ.rank (N + m w)) μ hsurj y
      have hg' : unitCo k (D := L) g = unitCo k (D := L) (wordUnit τ L
          (mapWord (z : TorusAffine k τ.rank (N + m w) →+* L)
            (bruhatParamWord τ k w α (β w)))) := by
        rw [← comp_unitCo_of_baseChange' z _ _ (baseChange_wordUnit _ _)]
        calc unitCo k (D := L) g = y.comp (Ideal.Quotient.mkₐ k I) :=
              (Ideal.Quotient.liftₐ_comp _ _ _).symm
          _ = (z.comp (μ w)).comp (Ideal.Quotient.mkₐ k I) := by rw [hz]
          _ = z.comp (bruhatCo τ k w α (β w)) := by rw [AlgHom.comp_assoc, hμc]
      rw [unitCo_injective hg', ← coe_wordElt]
      exact (wordElt τ _).2
  refine ⟨⟨unitCo_injective, fun y => exists_unitCo_eq y⟩, unitCo_glEntry, hmain, fun g => ?_⟩
  rw [hmain]
  constructor
  · intro hkill
    refine ⟨AlgHom.liftEquiv k L _ L (Ideal.Quotient.liftₐ I (unitCo k g) hkill), ?_⟩
    rw [Equiv.symm_apply_apply]
    exact Ideal.Quotient.liftₐ_comp _ _ _
  · rintro ⟨y, hy⟩ f hf
    rw [← hy, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hf,
      map_zero]

end CFSG.LieType.AlgebraicGroups

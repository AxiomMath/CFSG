module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamModels
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerCent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof.OddInner
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG Subgroup Module CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBSymplecticB
open LinearMap (BilinForm)
open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude)

theorem cl24_oddLie_similitudeCentralizer {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {r : ℕ} (hr : 2 ≤ r) (hdim : finrank K V = 2 * r)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w)
    {L : Subgroup (similitudeCentralizer B A)} (hL : IsComponent L)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = f ∨ f' = 2 * f → Rel f' := by cl24_rel) :
    Cl24Q ℓ Rel L := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2
    hf hK (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    rcases hε with h1 | h1
    ·
      obtain ⟨-, haltP, haltM, hndP, hndM, e, -⟩ := hpos h1
      have hP' := Submodule.one_le_finrank_iff.mpr hP
      have hM' := Submodule.one_le_finrank_iff.mpr hM
      exact cl24_of_component_equiv
        (e.trans (MulEquiv.prodCongr (sesqUnitaryIsometryEquiv _) (sesqUnitaryIsometryEquiv _)))
        (fun M hMc => cl24_prod
          (fun M₁ hM₁ => cl24_oddLie_isometryGroup hℓ hℓ2 hf hK _ haltP hndP (by omega) hM₁)
          (fun M₂ hM₂ => cl24_oddLie_isometryGroup hℓ hℓ2 hf hK _ haltM hndM (by omega) hM₂) hMc) hL
    ·
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
      let bP : Basis (Fin r) K (eigenPlus l (A : Module.End K V)) :=
        Module.finBasisOfFinrankEq K _ hdP
      exact cl24_of_component_equiv
        (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv))
        (fun M hMc => cl24_oddLie_GL hℓ hf hK (by omega) hMc) hL
  · push Not at hsq
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, hpow, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
    have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
      rw [hcard]
      exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
    have := finite_of_odd_card hEodd
    have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
      CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (A : Module.End K V)
    rcases hε with h1 | h1
    ·
      obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos h1
      exact cl24_of_component_equiv
        ((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBAlternatingIsometry.isometryGroup BE)
            (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
            (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff))
        (fun M hMc => cl24_oddLie_isometryGroup (j := 2 * f) hℓ hℓ2 (by omega)
          (by rw [hcard, ← pow_mul, mul_comm]) BE hBEalt hBEnd (by omega) hMc) hL
    ·
      obtain ⟨h, -, hsymm, hsep, hiff⟩ := hneg h1
      let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
      let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (A : Module.End K V)]
        scalarSquareField (A : Module.End K V) := h
      have hnd' : h'.Nondegenerate :=
        ⟨hsep, fun y hy => hsep y fun x => by
          rw [← hsymm.eq x y]
          exact (congrArg bar (hy x)).trans (map_zero bar)⟩
      have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
      have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
      have hne : sigma ≠ 1 := by
        intro heq
        let x : scalarSquareField (A : Module.End K V) :=
          ⟨A, Algebra.self_mem_adjoin_singleton K _⟩
        have hx := hbar x 0 1 (by simp only [zero_smul, zero_add, one_smul, x])
        have hfix : bar x = x := DFunLike.congr_fun heq x
        rw [hfix] at hx
        simp only [zero_smul, zero_sub, one_smul, x] at hx
        have hA2 : (2 : K) • (A : Module.End K V) = 0 := by
          rw [two_smul]
          nth_rewrite 2 [hx]
          exact add_neg_cancel _
        apply hAns 0
        rw [zero_smul]
        calc (A : Module.End K V) = (2 : K)⁻¹ • ((2 : K) • (A : Module.End K V)) := by
              rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
          _ = 0 := by rw [hA2, smul_zero]
      exact cl24_of_component_equiv
        ((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
            (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
            (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff))
        (fun M hMc => cl24_oddLie_unitary hℓ hℓ2 hf hcard (by omega) h' hsymm hnd' hsigma hne hpow
          hMc) hL

theorem cl24_oddLie_inner_psp {r : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .PSp r p f)
    (A : gsp r K) (hA : orderOf (conjAut r K A) = 2)
    {L : Subgroup (fixedSubgroup (conjAut r K A))} (hL : IsComponent L)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = f ∨ f' = 2 * f → Rel f' := by cl24_rel) :
    Cl24Q p Rel L := by
  have hf : 1 ≤ f := hadm.2.1
  have hr : 2 ≤ r := hadm.2.2.1
  have hA1 : conjAut r K A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : conjAut r K A * conjAut r K A = 1 := by
    rw [← pow_two, ← hA, pow_orderOf_eq_one]
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c :=
    fun c hc => hA1 ((Burgoyne.Sp.conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := (Burgoyne.Sp.conjAut_eq_one_iff (by omega) (A * A)).1
    (by rw [map_mul, hA2])
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAA : M * M = (c : K) • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  have hcen : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ center (GL (Fin r ⊕ Fin r) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have ha : ∀ x, conjSp r K A (conjSp r K A x) = x := by
    intro x
    apply Subtype.ext
    rw [← MulAut.mul_apply, ← map_mul, coe_conjSp, hc,
      ← Subgroup.mem_center_iff.mp hcen (x : GL (Fin r ⊕ Fin r) K), mul_inv_cancel_right]
  have hα : ∀ s, conjAut r K A (conjAut r K A s) = s := fun s => by
    rw [← MulAut.mul_apply, hA2, MulAut.one_apply]
  have hK' : (proj r K).ker ≤ center (StatedSp r K) := by
    rw [ker_proj]
    intro z hz
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← GeneralLinearGroup.center_eq_range_scalar] at hz
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hz g)
  obtain ⟨-, -, -, hlift, -⟩ := full_central_kernel_involution_fixed_component_correspondence
    proj_surjective hK' ha hα (fun x => (conjAut_proj A x).symm)
  set R := L.map (fixedSubgroup (conjAut r K A)).subtype with hRdef
  have hR : Assembly.IsComponentOf R (fixedSubgroup (conjAut r K A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup (conjAut r K A)) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, -, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  have hQo : Cl24Q p Rel _ := cl24_of_component_equiv
    ((MulEquiv.subgroupCongr (show fixedSubgroup (conjSp r K A) = spCent r K A from rfl)).trans
      (spCentEquiv A))
    (fun N hN => cl24_oddLie_similitudeCentralizer hp hp2 hf hK hr finrank_standard
      pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA)
      hAμ hN) hQ'
  exact cl24_of_mulEquiv
    (L.equivMapOfInjective (fixedSubgroup (conjAut r K A)).subtype (subtype_injective _))
    (cl24_of_centerQuotient_equiv eQR.symm
      (cl24_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm hQo))

end CFSG.OddStandard.SmallF3.HypA2Leaves

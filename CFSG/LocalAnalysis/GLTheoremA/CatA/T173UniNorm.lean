module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniCore
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusPlane
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.RankThree.PartOne.S11d.OrthCaseH

import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankInv
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFour
import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.HyperLinear
public import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.RankThree.PartOne.FOC.CompCommutator
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173U

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow
  CFSG.RankThree.PartOne.FieldFix CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.OrthogonalInvolutions
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.GroupTheory.WeirSylow
  CFSG.LieType.Universal.Spin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem apply_mem_iSup_of_mem_normalizer_aux1 {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb)
    {b : ↥(orthDerived Q)} (hb : b ∈ Bb) {w : V} (hw : w ∈ (⨆ j, U j : Submodule F V)) :
    (b : V ≃ₗ[F] V) w ∈ (⨆ j, U j : Submodule F V) := by
  refine Submodule.iSup_induction U
    (motive := fun w => (b : V ≃ₗ[F] V) w ∈ (⨆ j, U j : Submodule F V)) hw ?_ ?_ ?_
  · intro j y hy
    obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq hb j
    have hpow : ∀ n : ℕ, ∀ z ∈ U j, ((e j : V ≃ₗ[F] V) ^ n) z ∈ U j := by
      intro n
      induction n with
      | zero => intro z hz; simpa using hz
      | succ n ih =>
        intro z hz
        rw [pow_succ, LinearEquiv.mul_apply]
        exact ih _ (hF.maps_to j z hz)
    rw [hk y hy]
    exact Submodule.mem_iSup_of_mem j (hpow k y hy)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

private theorem apply_mem_iSup_of_mem_normalizer_aux2 {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb)
    {b : ↥(orthDerived Q)} (hb : b ∈ Bb) (v : V) :
    (b : V ≃ₗ[F] V) v - v ∈ (⨆ j, U j : Submodule F V) := by
  have hv : v ∈ (⨆ j, U j) ⊔ polarPerp Q (⨆ j, U j) := by
    rw [(hF.toIsPlaneSystem.isCompl_iSup).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  have h2 : (b : V ≃ₗ[F] V) (w + z) - (w + z) = (b : V ≃ₗ[F] V) w - w := by
    rw [map_add, hF.apply_eq_of_mem_polarPerp_iSup hb hz]
    abel
  rw [h2]
  exact Submodule.sub_mem _ (apply_mem_iSup_of_mem_normalizer_aux1 hF hb hw) hw

theorem apply_mem_iSup_of_mem_normalizer {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb)
    {g : ↥(orthDerived Q)} (hg : g ∈ Subgroup.normalizer (Bb : Set ↥(orthDerived Q))) {x : V}
    (hx : x ∈ (⨆ j, U j : Submodule F V)) : (g : V ≃ₗ[F] V) x ∈ (⨆ j, U j : Submodule F V) := by
  refine Submodule.iSup_induction U
    (motive := fun x => (g : V ≃ₗ[F] V) x ∈ (⨆ j, U j : Submodule F V)) hx ?_ ?_ ?_
  · intro j y hy
    have hej : e j ∈ Bb := by
      rw [← hF.closure_eq]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    have hb : g * e j * g⁻¹ ∈ Bb := (Subgroup.mem_set_normalizer_iff.mp hg (e j)).1 hej
    let φ : U j →ₗ[F] U j :=
      ((e j : V ≃ₗ[F] V).toLinearMap).restrict (fun z hz => hF.maps_to j z hz)
    have hψinj : Function.Injective (φ - (LinearMap.id : U j →ₗ[F] U j)) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      have hz1 : φ z = z := sub_eq_zero.mp (by simpa [LinearMap.sub_apply] using hz)
      have hze : (e j : V ≃ₗ[F] V) (z : V) = (z : V) := by
        simpa [φ, LinearMap.restrict_apply] using congrArg Subtype.val hz1
      exact Subtype.ext (hF.eq_zero_of_apply_eq j (z : V) z.2 hze)
    obtain ⟨y', hy'⟩ := LinearMap.surjective_of_injective hψinj (⟨y, hy⟩ : U j)
    have hxy : y = (e j : V ≃ₗ[F] V) (y' : V) - (y' : V) := by
      have h : ((φ - (LinearMap.id : U j →ₗ[F] U j)) y' : V) = (e j : V ≃ₗ[F] V) (y' : V) - (y' : V) := by
        simp [φ, LinearMap.sub_apply]
      rw [hy'] at h
      exact h
    have hbgy : ((g * e j * g⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) (y' : V)) =
        (g : V ≃ₗ[F] V) ((e j : V ≃ₗ[F] V) (y' : V)) := by
      simp [LinearEquiv.mul_apply]
    rw [hxy, map_sub]
    simpa [hbgy] using apply_mem_iSup_of_mem_normalizer_aux2 hF hb ((g : V ≃ₗ[F] V) (y' : V))
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux1 {W : Type} [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] {R : QuadraticForm F W}
    (hdim : Module.finrank F W = 2)
    (hQ : (QuadraticMap.polarBilin R).Nondegenerate) (han : ∀ x : W, R x = 0 → x = 0)
    {g : W ≃ₗ[F] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup R)
    (hgf : ∀ x : W, g x = x → x = 0) {v : W} (hv : R v ≠ 0) :
    reflect R v * g * (reflect R v)⁻¹ = g⁻¹ := by
  have hgv : g v ≠ v := fun h => hv (by rw [hgf v h, map_zero])
  have hw : g v - v ≠ 0 := sub_ne_zero.2 hgv
  have hQw : R (g v - v) ≠ 0 := fun h => hw (han _ h)
  have hRw : R (g v - v) = -polar R (g v) v := by
    rw [sub_eq_add_neg, QuadraticMap.map_add R, QuadraticMap.map_neg R, polar_neg_right,
      map_of_mem hg]
    rw [CharTwo.add_self_eq_zero, zero_add]
  have hpol : polar R (g v - v) (g v) = R (g v - v) := by
    rw [hRw, polar_sub_left, polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul, zero_sub,
      polar_comm]
  have hEq : reflect R (g v - v) (g v) = v := by
    rw [reflect_apply hQw, hpol, div_self hQw, one_smul]
    abel
  have hkO : reflect R (g v - v) * g ∈ TauCeti.QuadraticMap.orthogonalGroup R :=
    mul_mem (reflect_mem_orthogonalGroup R _) hg
  have hkv : (reflect R (g v - v) * g) v = v := by
    rw [LinearEquiv.mul_apply]; exact hEq
  rcases orthogonal_char_two_plane_vector_stabilizer hdim hQ hv hkO hkv with h1 | h1
  · exfalso
    have hgr : g = reflect R (g v - v) := by
      have h2 : g = (reflect R (g v - v))⁻¹ := eq_inv_of_mul_eq_one_right h1
      exact h2.trans (reflect_inv R (g v - v))
    have hgw : g (g v - v) = g v - v := by
      nth_rewrite 1 [hgr]
      rw [reflect_apply hQw, polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul, zero_div,
        zero_smul, sub_zero]
    exact hw (hgf (g v - v) hgw)
  · have hgt : g = reflect R (g v - v) * reflect R v := by
      have h2 : reflect R (g v - v) * g = reflect R v := h1
      rw [← h2, ← mul_assoc, reflect_mul_self, one_mul]
    rw [hgt, mul_inv_rev, reflect_inv, reflect_inv]
    simp only [mul_assoc, reflect_mul_self, mul_one]

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux2 {U : Submodule F V}
    (x u : U) :
    ((reflect (Q.comp U.subtype) x u : U) : V) = reflect Q (x : V) (u : V) := by
  by_cases hx : Q (x : V) = 0
  · have hx' : (Q.comp U.subtype) x = 0 := hx
    rw [reflect_of_map_eq_zero hx, reflect_of_map_eq_zero hx']
    rfl
  · have hx' : (Q.comp U.subtype) x ≠ 0 := hx
    rw [reflect_apply hx, reflect_apply hx']
    simp only [Submodule.coe_sub, Submodule.coe_smul]
    rfl

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux3 {n : ℕ}
    {U : Fin n → Submodule F V} (hU : IsPlaneSystem Q U)
    (i : Fin n) {v : V} (hvU : v ∈ U i) (hvQ : Q v ≠ 0) :
    ∀ y ∈ U i, reflect Q v y ∈ U i := by
  intro y hy
  rw [reflect_apply hvQ]
  exact Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hvU)

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux4 {n : ℕ}
    {U : Fin n → Submodule F V} (hU : IsPlaneSystem Q U) (i : Fin n) {v : V}
    (hvU : v ∈ U i) (hvQ : Q v ≠ 0) {E : V ≃ₗ[F] V}
    (hE : E ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hE1 : ∀ u ∈ U i, E u ∈ U i) (hE2 : ∀ u ∈ U i, E⁻¹ u ∈ U i)
    (hgf : ∀ u ∈ U i, E u = u → u = 0) :
    ∀ x ∈ U i, (reflect Q v * E * (reflect Q v)⁻¹) x = E⁻¹ x := by
  let Uj := U i
  let Qw : QuadraticForm F Uj := Q.comp Uj.subtype
  let gU : Uj ≃ₗ[F] Uj := restrictEquiv Uj E hE1 hE2
  have hcoe : ∀ y : Uj, ((gU y : Uj) : V) = E (y : V) := fun y =>
    coe_restrictEquiv Uj E hE1 hE2 y
  have hgU : gU ∈ TauCeti.QuadraticMap.orthogonalGroup Qw := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]; intro u
    change Q ((gU u : Uj) : V) = Q ((u : Uj) : V)
    rw [hcoe u]; exact map_of_mem hE (u : V)
  have hgfU : ∀ x : Uj, gU x = x → x = 0 := by
    intro x hx
    have hx' : E (x : V) = (x : V) := by rw [← hcoe x]; exact congrArg Subtype.val hx
    exact Subtype.ext (hgf (x : V) x.2 hx')
  have hdim : Module.finrank F Uj = 2 := hU.finrank_eq i; have hQw : (QuadraticMap.polarBilin Qw).Nondegenerate := hU.nondeg i
  have han : ∀ x : Uj, Qw x = 0 → x = 0 := by
    intro x hx; by_contra hx0
    apply hU.not_isPlusType i; refine ⟨Submodule.span F {x}, ?_, ?_⟩
    · rw [finrank_span_singleton hx0, hU.finrank_eq i]
    · intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [QuadraticMap.map_smul, hx, smul_zero]
  have hvQw : Qw ⟨v, hvU⟩ ≠ 0 := hvQ; have key := exists_mem_normalizer_conj_eq_of_isEvenFlip_aux1 hdim hQw han hgU hgfU hvQw
  have hcoe_inv : ∀ y : Uj, ((gU⁻¹ y : Uj) : V) = E⁻¹ (y : V) := by
    intro y
    have h1' : E ((gU.symm y : Uj) : V) = (y : V) := by
      rw [← hcoe (gU.symm y), gU.apply_symm_apply]
    exact ((E.symm_apply_eq).2 h1'.symm).symm
  have hrefl : ∀ y : Uj, ((reflect Qw ⟨v, hvU⟩ y : Uj) : V) = reflect Q v (y : V) :=
    fun y => exists_mem_normalizer_conj_eq_of_isEvenFlip_aux2 ⟨v, hvU⟩ y
  intro x hx
  have hkey' : (reflect Qw ⟨v, hvU⟩)
      (gU ((reflect Qw ⟨v, hvU⟩) ⟨x, hx⟩)) = gU⁻¹ ⟨x, hx⟩ := by
    simpa only [LinearEquiv.mul_apply, reflect_inv] using
      congrArg (fun f : Uj ≃ₗ[F] Uj => f ⟨x, hx⟩) key
  have hk2 := congrArg (fun z : Uj => (z : V)) hkey'
  have hmid : ((gU ((reflect Qw ⟨v, hvU⟩) ⟨x, hx⟩) : Uj) : V) = E (reflect Q v x) := by
    rw [hcoe, hrefl]
  have hcoetop : (((reflect Qw ⟨v, hvU⟩)
      (gU ((reflect Qw ⟨v, hvU⟩) ⟨x, hx⟩)) : Uj) : V) =
      reflect Q v (E (reflect Q v x)) := by
    rw [exists_mem_normalizer_conj_eq_of_isEvenFlip_aux2, hmid]
  have hcoeright : ((gU⁻¹ ⟨x, hx⟩ : Uj) : V) = E⁻¹ x := hcoe_inv ⟨x, hx⟩
  rw [hcoetop, hcoeright] at hk2; simpa only [LinearEquiv.mul_apply, reflect_inv] using hk2

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux5 {n : ℕ}
    {U : Fin n → Submodule F V} (hU : IsPlaneSystem Q U) (j : Fin n)
    {w : ↥(U j)} (hw0 : w ≠ 0) : Q (w : V) ≠ 0 := by
  intro hQw
  apply hU.not_isPlusType j
  refine ⟨Submodule.span F {w}, ?_, ?_⟩
  · rw [finrank_span_singleton hw0, hU.finrank_eq j]
  · intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    show (Q.comp (U j).subtype) (c • w) = 0
    rw [QuadraticMap.map_smul, show (Q.comp (U j).subtype) w = 0 from hQw, smul_zero]

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux6 {n : ℕ}
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (i : Fin n) :
    ∀ y ∈ U i, (d : V ≃ₗ[F] V) y ∈ U i := by
  obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq hd i
  have hpow : ∀ t : ℕ, ∀ z ∈ U i, ((e i : V ≃ₗ[F] V) ^ t) z ∈ U i := by
    intro t
    induction t with
    | zero => intro z hz; simpa using hz
    | succ t ih =>
        intro z hz
        rw [pow_succ, LinearEquiv.mul_apply]
        exact ih _ (hF.maps_to i z hz)
  intro y hy
  rw [hk y hy]
  exact hpow k y hy

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux7 {n : ℕ}
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (i : Fin n) :
    ∀ y ∈ U i, (d : V ≃ₗ[F] V)⁻¹ y ∈ U i := by
  have hdp : (d : ↥(orthDerived Q)) ^ p = 1 := hF.isElemAbelian.2 d hd
  have hdinv : (d : V ≃ₗ[F] V)⁻¹ = ((d ^ (p - 1) : ↥(orthDerived Q)) : V ≃ₗ[F] V) := by
    have h1 : (d : ↥(orthDerived Q))⁻¹ = d ^ (p - 1) := by
      have h2 : d ^ (p - 1) * d = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
        exact hdp
      exact (mul_eq_one_iff_eq_inv.mp h2).symm
    rw [← Subgroup.coe_inv, h1]
  intro y hy
  rw [hdinv]
  exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux6 hF (Bb.pow_mem hd (p - 1)) i y hy

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux8 {n : ℕ}
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (i : Fin n) {v : V} (hvU : v ∈ U i)
    (hvQ : Q v ≠ 0) :
    ∀ x ∈ U i, (reflect Q v * (d : V ≃ₗ[F] V) * (reflect Q v)⁻¹) x =
      ((d : V ≃ₗ[F] V))⁻¹ x := by
  have hE : (d : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup d.2
  have hE1 : ∀ u ∈ U i, (d : V ≃ₗ[F] V) u ∈ U i :=
    exists_mem_normalizer_conj_eq_of_isEvenFlip_aux6 hF hd i
  have hE2 : ∀ u ∈ U i, (d : V ≃ₗ[F] V)⁻¹ u ∈ U i :=
    exists_mem_normalizer_conj_eq_of_isEvenFlip_aux7 hF hp hd i
  rcases hF.apply_eq_or_eq_zero hp hd i with hfix | hfree
  · intro x hx
    have htx : reflect Q v x ∈ U i :=
      exists_mem_normalizer_conj_eq_of_isEvenFlip_aux3 hF.toIsPlaneSystem i hvU hvQ x hx
    have h1 : (d : V ≃ₗ[F] V) (reflect Q v x) = reflect Q v x := hfix _ htx
    have h2 : ((d : V ≃ₗ[F] V))⁻¹ x = x := by
      refine (d : V ≃ₗ[F] V).injective ?_
      rw [show (d : V ≃ₗ[F] V) ((d : V ≃ₗ[F] V)⁻¹ x) = x from
        LinearEquiv.apply_symm_apply (d : V ≃ₗ[F] V) x]
      exact (hfix x hx).symm
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show (reflect Q v)⁻¹ = reflect Q v from reflect_inv Q v,
      h1, ← LinearEquiv.mul_apply, reflect_mul_self, h2]
    rfl
  · intro x hx
    exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux4 hF.toIsPlaneSystem i hvU hvQ hE
      hE1 hE2 hfree x hx

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux9 {n : ℕ}
    {U : Fin n → Submodule F V} (hU : IsPlaneSystem Q U) {v : Fin n → V}
    (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0) (J : Finset (Fin n))
    (comm : (J : Set (Fin n)).Pairwise
      (Function.onFun Commute (fun j => reflect Q (v j))))
    {i : Fin n} {x : V} (hx : x ∈ U i) :
    J.noncommProd (fun j => reflect Q (v j)) comm x =
      if i ∈ J then reflect Q (v i) x else x := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, LinearEquiv.mul_apply]
      rw [ih (comm.mono (fun x hx => Finset.mem_insert_of_mem hx))]
      by_cases hia : i = a
      · rw [hia]
        rw [if_neg ha, if_pos (Finset.mem_insert_self a s)]
      · simp only [Finset.mem_insert, hia, false_or]
        by_cases his : i ∈ s
        · rw [if_pos his]
          exact reflect_apply_of_polar_eq_zero
            (hU.perp a i (Ne.symm hia) (v a) (hvU a) _
              (exists_mem_normalizer_conj_eq_of_isEvenFlip_aux3 hU i (hvU i) (hvQ i) x hx))
        · rw [if_neg his]
          exact reflect_apply_of_polar_eq_zero
            (hU.perp a i (Ne.symm hia) (v a) (hvU a) x hx)

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux10 {n : ℕ}
    {U : Fin n → Submodule F V} (hU : IsPlaneSystem Q U) {v : Fin n → V}
    (hvU : ∀ i, v i ∈ U i) (J : Finset (Fin n))
    (comm : (J : Set (Fin n)).Pairwise
      (Function.onFun Commute (fun j => reflect Q (v j))))
    {x : V} (hx : x ∈ polarPerp Q (⨆ i, U i)) :
    J.noncommProd (fun j => reflect Q (v j)) comm x = x := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, LinearEquiv.mul_apply]
      rw [ih (comm.mono (fun x hx => Finset.mem_insert_of_mem hx))]
      exact reflect_apply_of_polar_eq_zero
        (mem_polarPerp_iff.1 hx (v a) (Submodule.mem_iSup_of_mem a (hvU a)))

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux11 {m : ℕ}
    {U : Fin m → Submodule F V} (hU : IsPlaneSystem Q U) {P R : V ≃ₗ[F] V}
    (hW : ∀ (i : Fin m) (x : V), x ∈ U i → P x = R x)
    (hperp : ∀ x ∈ polarPerp Q (⨆ i, U i), P x = R x) : P = R := by
  have hWsum : ∀ u ∈ (⨆ i, U i), P u = R u := by
    intro u hu
    refine Submodule.iSup_induction U (motive := fun u => P u = R u) hu ?_ ?_ ?_
    · exact hW
    · simp
    · intro a b ha hb
      rw [map_add, map_add, ha, hb]
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ (⨆ i, U i) ⊔ polarPerp Q (⨆ i, U i) := by
    rw [(hU.isCompl_iSup).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, map_add, hWsum u hu, hperp w hw]

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux12
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) :
    ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  by_cases hplus : IsPlusType Q
  · exact exists_threeSingular hQ hdim (Or.inl ⟨hplus, by omega⟩)
  · exact exists_threeSingular hQ hdim (Or.inr ⟨hplus, hn⟩)

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux13
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {N m : ℕ}
    (hdim : Module.finrank F V = 2 * N) (hN : 4 ≤ N)
    {U : Fin m → Submodule F V} {e : Fin m → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb)
    {v : Fin m → V} (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0)
    (J : Finset (Fin m)) (hJeven : Even J.card)
    (comm : (J : Set (Fin m)).Pairwise
      (Function.onFun Commute (fun j => reflect Q (v j)))) :
    ∃ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) =
      J.noncommProd (fun j => reflect Q (v j)) comm := by
  classical
  let tau : Fin m → ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
    fun j => ⟨reflect Q (v j), reflect_mem_orthogonalGroup Q (v j)⟩
  have hcommO : (J : Set (Fin m)).Pairwise (Function.onFun Commute tau) := by
    intro a _ b _ hab
    exact Subtype.ext (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero
      (hF.perp a b hab (v a) (hvU a) (v b) (hvU b))).eq
  let gO : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := J.noncommProd tau hcommO
  have hcoe : (gO : V ≃ₗ[F] V) =
      J.noncommProd (fun j => reflect Q (v j)) comm := by
    have h := Finset.map_noncommProd J tau hcommO
      (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup Q))
    simpa only [gO, Subgroup.coe_subtype] using h
  have hdick : dicksonHom Q hQ gO = 1 := by
    have h := Finset.map_noncommProd J tau hcommO (dicksonHom Q hQ)
    rw [show gO = J.noncommProd tau hcommO from rfl, h, Finset.noncommProd_eq_prod,
      Finset.prod_congr rfl (fun i _ => dicksonHom_reflect hQ (hvQ i)), Finset.prod_const,
      ← ofAdd_nsmul]
    rw [show (J.card • (1 : ZMod 2)) = (J.card : ZMod 2) by simp]
    have h0 : (J.card : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr hJeven
    rw [h0]
    rfl
  have hmem : (gO : V ≃ₗ[F] V) ∈ orthDerived Q := by
    have hker : gO ∈ (dicksonHom Q hQ).ker := by
      rw [MonoidHom.mem_ker]; exact hdick
    rw [dicksonHom_ker] at hker
    exact omegaGroup_le_orthDerived hQ
      (exists_mem_normalizer_conj_eq_of_isEvenFlip_aux12 hQ hdim hN)
      (Subgroup.mem_subgroupOf.mp hker)
  exact ⟨⟨(gO : V ≃ₗ[F] V), hmem⟩, hcoe⟩

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux22 {n : ℕ}
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime)
    {v : Fin n → V} (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0)
    (J : Finset (Fin n)) {P : V ≃ₗ[F] V} (hPeq : P = P⁻¹)
    (hPinv : ∀ (i : Fin n) {x : V}, x ∈ U i →
      P⁻¹ x = if i ∈ J then reflect Q (v i) x else x)
    (i : Fin n) {x : V} (hx : x ∈ U i) :
    (P * (e i : V ≃ₗ[F] V) * P⁻¹) x =
      (if i ∈ J then ((e i : V ≃ₗ[F] V))⁻¹ else (e i : V ≃ₗ[F] V)) x := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  by_cases hi : i ∈ J
  · rw [hPinv i hx, if_pos hi, if_pos hi]
    have hmem : (e i : V ≃ₗ[F] V) (reflect Q (v i) x) ∈ U i :=
      hF.maps_to i _ (exists_mem_normalizer_conj_eq_of_isEvenFlip_aux3
        hF.toIsPlaneSystem i (hvU i) (hvQ i) x hx)
    rw [show P ((e i : V ≃ₗ[F] V) (reflect Q (v i) x)) =
        reflect Q (v i) ((e i : V ≃ₗ[F] V) (reflect Q (v i) x)) from by
      rw [hPeq, hPinv i hmem, if_pos hi]]
    rw [show reflect Q (v i) ((e i : V ≃ₗ[F] V) (reflect Q (v i) x)) =
        (reflect Q (v i) * (e i : V ≃ₗ[F] V) * (reflect Q (v i))⁻¹) x from by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflect_inv]]
    exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux8 hF hp (hF.mem i) i
      (hvU i) (hvQ i) x hx
  · rw [hPinv i hx, if_neg hi, if_neg hi]
    have hmem : (e i : V ≃ₗ[F] V) x ∈ U i := hF.maps_to i x hx
    rw [show P ((e i : V ≃ₗ[F] V) x) = (e i : V ≃ₗ[F] V) x from by
      rw [hPeq, hPinv i hmem, if_neg hi]]

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux23 {n : ℕ}
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb)
    {v : Fin n → V} (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0)
    (J : Finset (Fin n)) {P : V ≃ₗ[F] V} (hPeq : P = P⁻¹)
    (hPinv : ∀ (i : Fin n) {x : V}, x ∈ U i →
      P⁻¹ x = if i ∈ J then reflect Q (v i) x else x)
    (j i : Fin n) (hij : i ≠ j) {x : V} (hx : x ∈ U i) :
    (P * (e j : V ≃ₗ[F] V) * P⁻¹) x =
      (if j ∈ J then ((e j : V ≃ₗ[F] V))⁻¹ else (e j : V ≃ₗ[F] V)) x := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hfix_i : ∀ y ∈ U i, (e j : V ≃ₗ[F] V) y = y := by
    intro y hy
    exact hF.apply_of_perp j y (mem_polarPerp_iff.2 fun a ha => by
      rw [QuadraticMap.polar_comm]
      exact hF.perp i j (fun h => hij h) y hy a ha)
  have hfix_i_inv : ∀ y ∈ U i, (e j : V ≃ₗ[F] V)⁻¹ y = y := by
    intro y hy
    refine (e j : V ≃ₗ[F] V).injective ?_
    rw [show (e j : V ≃ₗ[F] V) ((e j : V ≃ₗ[F] V)⁻¹ y) = y from
      LinearEquiv.apply_symm_apply (e j : V ≃ₗ[F] V) y, hfix_i y hy]
  rw [hPinv i hx]
  by_cases hi : i ∈ J
  · rw [if_pos hi]
    have htau : reflect Q (v i) x ∈ U i :=
      exists_mem_normalizer_conj_eq_of_isEvenFlip_aux3 hF.toIsPlaneSystem i (hvU i)
        (hvQ i) x hx
    rw [hfix_i _ htau]
    have hPtau : P (reflect Q (v i) x) = x := by
      rw [hPeq, hPinv i htau, if_pos hi]
      rw [← LinearEquiv.mul_apply, reflect_mul_self]
      rfl
    rw [hPtau]
    by_cases hj : j ∈ J
    · rw [if_pos hj, hfix_i_inv x hx]
    · rw [if_neg hj, hfix_i x hx]
  · rw [if_neg hi, hfix_i _ hx]
    have hPx : P x = x := by rw [hPeq, hPinv i hx, if_neg hi]
    rw [hPx]
    by_cases hj : j ∈ J
    · rw [if_pos hj, hfix_i_inv x hx]
    · rw [if_neg hj, hfix_i x hx]

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux14 {n : ℕ}
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime)
    {v : Fin n → V} (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0)
    (J : Finset (Fin n)) {P : V ≃ₗ[F] V} (hPeq : P = P⁻¹)
    (hPinv : ∀ (i : Fin n) {x : V}, x ∈ U i →
      P⁻¹ x = if i ∈ J then reflect Q (v i) x else x)
    (hPperp : ∀ {x : V}, x ∈ polarPerp Q (⨆ i, U i) → P⁻¹ x = x) (j : Fin n) :
    P * (e j : V ≃ₗ[F] V) * P⁻¹ =
      if j ∈ J then ((e j : V ≃ₗ[F] V))⁻¹ else (e j : V ≃ₗ[F] V) := by
  classical
  refine exists_mem_normalizer_conj_eq_of_isEvenFlip_aux11 hF.toIsPlaneSystem
    (P := P * (e j : V ≃ₗ[F] V) * P⁻¹)
    (R := if j ∈ J then ((e j : V ≃ₗ[F] V))⁻¹ else (e j : V ≃ₗ[F] V)) ?_ ?_
  · intro i x hx
    by_cases hij : i = j
    · subst hij
      exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux22 hF hp hvU hvQ J hPeq hPinv i hx
    · exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux23 hF hvU hvQ J hPeq hPinv j i hij hx
  · intro x hx
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hPperp hx,
      hF.apply_eq_of_mem_polarPerp_iSup (hF.mem j) hx]
    have hPx : P x = x := by rw [hPeq]; exact hPperp hx
    rw [hPx]
    by_cases hj : j ∈ J
    · rw [if_pos hj]
      have h1 : ((e j : V ≃ₗ[F] V))⁻¹ x = x := by
        refine (e j : V ≃ₗ[F] V).injective ?_
        rw [show (e j : V ≃ₗ[F] V) ((e j : V ≃ₗ[F] V)⁻¹ x) = x from
          LinearEquiv.apply_symm_apply (e j : V ≃ₗ[F] V) x]
        exact (hF.apply_eq_of_mem_polarPerp_iSup (hF.mem j) hx).symm
      rw [h1]
    · rw [if_neg hj]
      exact (hF.apply_eq_of_mem_polarPerp_iSup (hF.mem j) hx).symm

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux20 {n : ℕ}
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb)
    {J : Finset (Fin n)} {g : ↥(orthDerived Q)}
    (hgen' : ∀ j, MulAut.conj g (e j) = if j ∈ J then (e j)⁻¹ else e j) :
    ∀ h ∈ Bb, MulAut.conj g h ∈ Bb := by
  intro h hh
  rw [← hF.closure_eq] at hh
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [hgen' j]
      by_cases hj : j ∈ J
      · rw [if_pos hj]; exact Bb.inv_mem (hF.mem j)
      · rw [if_neg hj]; exact hF.mem j
  | one => simpa using Bb.one_mem
  | mul a b ha hb iha ihb =>
      rw [map_mul]
      exact Bb.mul_mem iha ihb
  | inv a ha iha =>
      rw [map_inv]
      exact Bb.inv_mem iha

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux21 {n : ℕ}
    {U : Fin n → Submodule F V} (hF : IsPlaneSystem Q U) {v : Fin n → V}
    (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0) (J : Finset (Fin n))
    {P : V ≃ₗ[F] V} (hPeq : P = P⁻¹)
    (hPinv : ∀ (i : Fin n) {x : V}, x ∈ U i →
      P⁻¹ x = if i ∈ J then reflect Q (v i) x else x)
    (hPperp : ∀ {x : V}, x ∈ polarPerp Q (⨆ i, U i) → P⁻¹ x = x)
    {g : ↥(orthDerived Q)} (hg : (g : V ≃ₗ[F] V) = P) :
    (g : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) = 1 := by
  refine exists_mem_normalizer_conj_eq_of_isEvenFlip_aux11 hF
    (P := (g : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V)) (R := 1) ?_ ?_
  · intro i x hx
    rw [LinearEquiv.mul_apply,
      show (g : V ≃ₗ[F] V) x = if i ∈ J then reflect Q (v i) x else x from by
        rw [hg, hPeq]; exact hPinv i hx]
    by_cases hi : i ∈ J
    · rw [if_pos hi]
      have htau : reflect Q (v i) x ∈ U i :=
        exists_mem_normalizer_conj_eq_of_isEvenFlip_aux3 hF i (hvU i) (hvQ i) x hx
      rw [show (g : V ≃ₗ[F] V) (reflect Q (v i) x) =
          if i ∈ J then reflect Q (v i) (reflect Q (v i) x) else reflect Q (v i) x from by
        rw [hg, hPeq]; exact hPinv i htau]
      rw [if_pos hi, ← LinearEquiv.mul_apply, reflect_mul_self]
    · rw [if_neg hi]
      rw [show (g : V ≃ₗ[F] V) x = x from by rw [hg, hPeq, hPinv i hx, if_neg hi]]
      simp
  · intro x hx
    rw [LinearEquiv.mul_apply,
      show (g : V ≃ₗ[F] V) x = x from by rw [hg, hPeq]; exact hPperp hx,
      show (g : V ≃ₗ[F] V) x = x from by rw [hg, hPeq]; exact hPperp hx]
    simp

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux16 {n : ℕ}
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime)
    {v : Fin n → V} (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0)
    (J : Finset (Fin n)) {P : V ≃ₗ[F] V} (hPeq : P = P⁻¹)
    (hPinv : ∀ (i : Fin n) {x : V}, x ∈ U i →
      P⁻¹ x = if i ∈ J then reflect Q (v i) x else x)
    (hPperp : ∀ {x : V}, x ∈ polarPerp Q (⨆ i, U i) → P⁻¹ x = x)
    {g : ↥(orthDerived Q)} (hg : (g : V ≃ₗ[F] V) = P) :
    g ∈ Subgroup.normalizer (Bb : Set ↥(orthDerived Q)) := by
  classical
  have hgenV : ∀ j, (g : V ≃ₗ[F] V) * (e j : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V)⁻¹ =
      if j ∈ J then ((e j : V ≃ₗ[F] V))⁻¹ else (e j : V ≃ₗ[F] V) := by
    intro j
    rw [hg]
    exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux14 hF hp hvU hvQ J hPeq hPinv
      hPperp j
  have hgen' : ∀ j, MulAut.conj g (e j) = if j ∈ J then (e j)⁻¹ else e j := by
    intro j
    apply Subtype.ext
    have h := hgenV j
    by_cases hj : j ∈ J
    · rw [if_pos hj] at h ⊢
      simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h
    · rw [if_neg hj] at h ⊢
      simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hfwd := exists_mem_normalizer_conj_eq_of_isEvenFlip_aux20 hF hgen'
  have hg_sq : g * g = 1 :=
    Subtype.ext (exists_mem_normalizer_conj_eq_of_isEvenFlip_aux21 hF.toIsPlaneSystem hvU hvQ J
      hPeq hPinv hPperp hg)
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨hfwd h, fun hh => ?_⟩
  have h1 := hfwd (g * h * g⁻¹) hh
  have h2 : MulAut.conj g (g * h * g⁻¹) = h := by
    rw [MulAut.conj_apply]
    have e1 : g * (g * h * g⁻¹) * g⁻¹ = (g * g) * h * (g * g)⁻¹ := by group
    rw [e1, hg_sq, inv_one, mul_one, one_mul]
  rwa [h2] at h1

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux17 {n : ℕ}
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime)
    {v : Fin n → V} (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0)
    (J : Finset (Fin n)) {P : V ≃ₗ[F] V} (hPeq : P = P⁻¹)
    (hPinv : ∀ (i : Fin n) {x : V}, x ∈ U i →
      P⁻¹ x = if i ∈ J then reflect Q (v i) x else x)
    (hPperp : ∀ {x : V}, x ∈ polarPerp Q (⨆ i, U i) → P⁻¹ x = x)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) {d' : V ≃ₗ[F] V}
    (hJflip : IsFlip Q U (d : V ≃ₗ[F] V) d' J) :
    P * (d : V ≃ₗ[F] V) * P⁻¹ = d' := by
  have hPperp' : ∀ {x : V}, x ∈ polarPerp Q (⨆ i, U i) → P x = x :=
    fun hx => by rw [hPeq]; exact hPperp hx
  have hd'p : ∀ (i : Fin n) {x : V}, x ∈ U i → d' x ∈ U i := by
    intro i x hx
    rw [hJflip.2.2 i x hx]
    by_cases hi : i ∈ J
    · rw [if_pos hi]; exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux7 hF hp hd i x hx
    · rw [if_neg hi]; exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux6 hF hd i x hx
  have hd'inv : ∀ {x : V}, x ∈ polarPerp Q (⨆ i, U i) → d'⁻¹ x = x :=
    fun {x} hx => (LinearEquiv.symm_apply_eq d').2 (hJflip.2.1 x hx).symm
  refine exists_mem_normalizer_conj_eq_of_isEvenFlip_aux11 hF.toIsPlaneSystem
    (P := P * (d : V ≃ₗ[F] V) * P⁻¹) (R := d') ?_ ?_
  · intro i x hx
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    by_cases hi : i ∈ J
    · rw [hPinv i hx, if_pos hi]
      have hmem : (d : V ≃ₗ[F] V) (reflect Q (v i) x) ∈ U i :=
        exists_mem_normalizer_conj_eq_of_isEvenFlip_aux6 hF hd i (reflect Q (v i) x)
          (exists_mem_normalizer_conj_eq_of_isEvenFlip_aux3 hF.toIsPlaneSystem i
            (hvU i) (hvQ i) x hx)
      rw [show P ((d : V ≃ₗ[F] V) (reflect Q (v i) x)) =
          reflect Q (v i) ((d : V ≃ₗ[F] V) (reflect Q (v i) x)) from by
        rw [hPeq, hPinv i hmem, if_pos hi]]
      rw [show reflect Q (v i) ((d : V ≃ₗ[F] V) (reflect Q (v i) x)) =
          (reflect Q (v i) * (d : V ≃ₗ[F] V) * (reflect Q (v i))⁻¹) x from by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflect_inv]]
      rw [exists_mem_normalizer_conj_eq_of_isEvenFlip_aux8 hF hp hd i (hvU i) (hvQ i) x hx]
      rw [hJflip.2.2 i x hx, if_pos hi]
    · rw [hPinv i hx, if_neg hi]
      have hmem : (d : V ≃ₗ[F] V) x ∈ U i :=
        exists_mem_normalizer_conj_eq_of_isEvenFlip_aux6 hF hd i x hx
      rw [show P ((d : V ≃ₗ[F] V) x) = (d : V ≃ₗ[F] V) x from by
        rw [hPeq, hPinv i hmem, if_neg hi]]
      rw [hJflip.2.2 i x hx, if_neg hi]
  · intro x hx
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hPperp hx,
      hF.apply_eq_of_mem_polarPerp_iSup hd hx]
    rw [show P x = x from hPperp' hx]
    exact (hJflip.2.1 x hx).symm

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux18 {n : ℕ}
    {U : Fin n → Submodule F V} (hF : IsPlaneSystem Q U) {v : Fin n → V}
    (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0) (J : Finset (Fin n))
    (comm : (J : Set (Fin n)).Pairwise
      (Function.onFun Commute (fun j => reflect Q (v j))))
    {g : ↥(orthDerived Q)} (hgcoe : (g : V ≃ₗ[F] V) =
      J.noncommProd (fun j => reflect Q (v j)) comm) :
    (∀ (i : Fin n) {x : V}, x ∈ U i → (g : V ≃ₗ[F] V)⁻¹ x =
      if i ∈ J then reflect Q (v i) x else x) ∧
    (∀ {x : V}, x ∈ polarPerp Q (⨆ i, U i) → (g : V ≃ₗ[F] V)⁻¹ x = x) := by
  constructor
  · intro i x hx
    by_cases hi : i ∈ J
    · rw [if_pos hi]
      have htau : reflect Q (v i) x ∈ U i :=
        exists_mem_normalizer_conj_eq_of_isEvenFlip_aux3 hF i (hvU i) (hvQ i) x hx
      have h1 : (g : V ≃ₗ[F] V) (reflect Q (v i) x) = x := by
        rw [hgcoe, exists_mem_normalizer_conj_eq_of_isEvenFlip_aux9 hF hvU hvQ J comm htau,
          if_pos hi, ← LinearEquiv.mul_apply, reflect_mul_self]
        rfl
      exact ((LinearEquiv.symm_apply_eq (g : V ≃ₗ[F] V)).2 h1.symm)
    · rw [if_neg hi]
      have h1 : (g : V ≃ₗ[F] V) x = x := by
        rw [hgcoe, exists_mem_normalizer_conj_eq_of_isEvenFlip_aux9 hF hvU hvQ J comm hx,
          if_neg hi]
      exact ((LinearEquiv.symm_apply_eq (g : V ≃ₗ[F] V)).2 h1.symm)
  · intro x hx
    have h1 : (g : V ≃ₗ[F] V) x = x := by
      rw [hgcoe, exists_mem_normalizer_conj_eq_of_isEvenFlip_aux10 hF hvU J comm hx]
    exact ((LinearEquiv.symm_apply_eq (g : V ≃ₗ[F] V)).2 h1.symm)

private theorem exists_mem_normalizer_conj_eq_of_isEvenFlip_aux19 {n : ℕ}
    {U : Fin n → Submodule F V} (hF : IsPlaneSystem Q U) {v : Fin n → V}
    (hvU : ∀ i, v i ∈ U i) (hvQ : ∀ i, Q (v i) ≠ 0) (J : Finset (Fin n))
    (comm : (J : Set (Fin n)).Pairwise
      (Function.onFun Commute (fun j => reflect Q (v j))))
    {g : ↥(orthDerived Q)} (hgcoe : (g : V ≃ₗ[F] V) =
      J.noncommProd (fun j => reflect Q (v j)) comm)
    (hPinv : ∀ (i : Fin n) {x : V}, x ∈ U i → (g : V ≃ₗ[F] V)⁻¹ x =
      if i ∈ J then reflect Q (v i) x else x)
    (hPperp : ∀ {x : V}, x ∈ polarPerp Q (⨆ i, U i) → (g : V ≃ₗ[F] V)⁻¹ x = x) :
    (g : V ≃ₗ[F] V) = ((g : V ≃ₗ[F] V))⁻¹ := by
  refine exists_mem_normalizer_conj_eq_of_isEvenFlip_aux11 hF
    (P := (g : V ≃ₗ[F] V)) (R := (g : V ≃ₗ[F] V)⁻¹) ?_ ?_
  · intro i x hx
    rw [hgcoe, exists_mem_normalizer_conj_eq_of_isEvenFlip_aux9 hF hvU hvQ J comm hx,
      ← hgcoe]
    exact (hPinv i hx).symm
  · intro x hx
    rw [hgcoe, exists_mem_normalizer_conj_eq_of_isEvenFlip_aux10 hF hvU J comm hx, ← hgcoe]
    exact (hPperp hx).symm

theorem exists_mem_normalizer_conj_eq_of_isEvenFlip (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) {d' : V ≃ₗ[F] V} (hd' : IsEvenFlip Q U (d : V ≃ₗ[F] V) d') :
    ∃ g ∈ Subgroup.normalizer (Bb : Set ↥(orthDerived Q)),
      (g : V ≃ₗ[F] V) * (d : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V)⁻¹ = d' := by
  classical
  obtain ⟨J, hJeven, hJflip⟩ := hd'
  have hex : ∀ j : Fin (n - 1), ∃ w : V, w ∈ U j ∧ Q w ≠ 0 := by
    intro j
    obtain ⟨w, hw, hw0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j) (hF.finrank_eq j)
    exact ⟨w, hw, exists_mem_normalizer_conj_eq_of_isEvenFlip_aux5 hF.toIsPlaneSystem j
      (w := ⟨w, hw⟩) (fun h => hw0 (congrArg Subtype.val h))⟩
  choose v hvU hvQ using hex
  have hpcomm : (J : Set (Fin (n - 1))).Pairwise
      (Function.onFun Commute (fun j => reflect Q (v j))) := by
    intro a _ b _ hab
    exact CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero
      (hF.perp a b hab (v a) (hvU a) (v b) (hvU b))
  obtain ⟨g, hgcoe⟩ := exists_mem_normalizer_conj_eq_of_isEvenFlip_aux13 hQ hdim hn hF
    hvU hvQ J hJeven hpcomm
  obtain ⟨hPinv, hPperp⟩ := exists_mem_normalizer_conj_eq_of_isEvenFlip_aux18
    hF.toIsPlaneSystem hvU hvQ J hpcomm hgcoe
  have hPeq := exists_mem_normalizer_conj_eq_of_isEvenFlip_aux19
    hF.toIsPlaneSystem hvU hvQ J hpcomm hgcoe hPinv hPperp
  refine ⟨g, ?_, ?_⟩
  · exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux16 hF hp hvU hvQ J hPeq hPinv hPperp
      (g := g) (P := (g : V ≃ₗ[F] V)) rfl
  · exact exists_mem_normalizer_conj_eq_of_isEvenFlip_aux17 hF hp hvU hvQ J hPeq hPinv hPperp
      hd hJflip

private theorem exists_mem_normalizer_map_eq_aux1 {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {h : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm F b c))
    (hodd : Odd (orderOf h)) : h ∈ omegaRotations b c := by
  have hb : b ≠ 0 := minusPlane_b_ne_zero hirr
  obtain ⟨l, hl, htw⟩ := isOmegaTwisted_of_mem_orthogonalGroup (b := b) (c := c) hb hh
  have hone : IsOmegaTwisted b c (1 : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) 0 := by
    unfold IsOmegaTwisted
    ext v
    simp
  have hpow : ∀ n : ℕ, IsOmegaTwisted b c (h ^ n) (n • l) := by
    intro n
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ]; simpa [succ_nsmul, Nat.cast_add, Nat.cast_one, add_mul] using ih.mul htw
  have htw1 : IsOmegaTwisted b c (1 : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (orderOf h • l) := by
    rw [← pow_orderOf_eq_one h]
    exact hpow (orderOf h)
  have hlz : (orderOf h : F) * l = 0 := by
    have h1 := htw1
    unfold IsOmegaTwisted at h1
    change (1 : Module.End F (Fin 2 → F)) * minusOmegaMul b c =
      (minusOmegaMul b c + (orderOf h • l) • 1) * 1 at h1
    rw [one_mul, mul_one] at h1
    have h2 : (orderOf h • l) • (1 : Module.End F (Fin 2 → F)) = 0 :=
      (add_left_cancel ((add_zero _).trans h1)).symm
    have h3 := congrFun (congrArg DFunLike.coe h2) (Pi.single 0 1)
    have h4 := congrFun h3 0
    simpa [nsmul_eq_mul] using h4
  have hl0 : l = 0 := by
    by_contra hlne
    have hlb : l = b := hl.resolve_left hlne
    have hcast : ((orderOf h : ℕ) : F) = 1 := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk]
      push_cast
      rw [CharTwo.two_eq_zero]
      ring
    rw [hlb] at hlz
    rw [hcast, one_mul] at hlz
    exact hb hlz
  rwa [hl0] at htw

private theorem exists_mem_normalizer_map_eq_aux2 {A : Type} [AddCommGroup A] [Module F A]
    {R : QuadraticForm F A} {b c : F} (Φ : R.IsometryEquiv (minusTailForm F b c))
    {h : A ≃ₗ[F] A} (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup R) :
    LinearEquiv.autCongr (Φ : A ≃ₗ[F] (Fin 2 → F)) h ∈
      TauCeti.QuadraticMap.orthogonalGroup (minusTailForm F b c) := by
  let Ψ : A ≃ₗ[F] (Fin 2 → F) := Φ.toLinearEquiv
  have hΨ : ∀ x, minusTailForm F b c (Ψ x) = R x := fun x => Φ.map_app x
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [show LinearEquiv.autCongr Ψ h v = Ψ (h (Ψ.symm v)) from by
    simp only [LinearEquiv.autCongr_apply_apply]]
  rw [hΨ, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hh (Ψ.symm v)]
  simpa using (hΨ (Ψ.symm v)).symm

private theorem exists_mem_normalizer_map_eq_aux3 {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ}
    {e' g' : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)}
    (he' : e' ∈ omegaRotations b c) (hg' : g' ∈ omegaRotations b c)
    (he'p : orderOf e' = p) (hg'p : orderOf g' = p) : ∃ m : ℕ, e' ^ m = g' := by
  haveI : Finite (Fin 2 → F) := inferInstance
  haveI : Finite ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) :=
    Finite.of_injective (fun e : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) =>
      (e : (Fin 2 → F) → (Fin 2 → F))) fun a b h => LinearEquiv.ext (congrFun h)
  let E' : ↥(omegaRotations b c) := ⟨e', he'⟩
  let G' : ↥(omegaRotations b c) := ⟨g', hg'⟩
  haveI : IsCyclic ↥(omegaRotations b c) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus.isCyclic_omegaRotations hirr
  have heq : Subgroup.zpowers E' = Subgroup.zpowers G' := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, he'p, hg'p]
  have hmem : G' ∈ Subgroup.zpowers E' := by rw [heq]; exact Subgroup.mem_zpowers G'
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff G' E').mp
    ((IsOfFinOrder.mem_powers_iff_mem_zpowers (isOfFinOrder_of_finite E')).mpr hmem)
  refine ⟨m, ?_⟩
  have := congrArg (fun x : ↥(omegaRotations b c) =>
    (x : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))) hm
  simpa [E', G'] using this

private theorem exists_mem_normalizer_map_eq_aux4 {A : Type} [AddCommGroup A] [Module F A]
    [FiniteDimensional F A] {R : QuadraticForm F A}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hA2 : finrank F A = 2)
    (hani : ∀ x, R x = 0 → x = 0) :
    ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (R.IsometryEquiv (minusTailForm F b c)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hnotplus : ¬ IsPlusType R := by
    rintro ⟨W, hW, hWs⟩
    have h1 : Module.finrank F W = 1 := by omega
    have hWne : W ≠ ⊥ := by
      intro hbot
      have h0 : Module.finrank F W = 0 := by rw [hbot]; exact finrank_bot F A
      omega
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    exact hw0 (hani w (hWs w hwW))
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR le_rfl
      (by simpa using hA2) with hplus | ⟨b, c, hirr, hminus⟩
  · obtain ⟨e1⟩ := hplus
    exact absurd ((CFSG.GroupTheory.WeirSylow.isPlusType_congr e1).2
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F 1)) hnotplus
  · obtain ⟨e1⟩ := hminus
    let e2 : (minusTailForm F b c).IsometryEquiv (quadMinus 1 F b c) :=
      (QuadraticMap.IsometryEquiv.uniqueProd (quadPlus 0 F) (minusTailForm F b c)).symm.trans
        (minusTailIsometry 1 F b c)
    exact ⟨b, c, hirr, ⟨e1.trans e2.symm⟩⟩

private theorem exists_mem_normalizer_map_eq_aux5 {A : Type} [AddCommGroup A] [Module F A]
    [FiniteDimensional F A] {R : QuadraticForm F A}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hA2 : finrank F A = 2)
    (hani : ∀ x, R x = 0 → x = 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {e g : A ≃ₗ[F] A}
    (he : e ∈ TauCeti.QuadraticMap.orthogonalGroup R) (heo : orderOf e = p)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup R) (hgo : orderOf g = p) :
    g ∈ Subgroup.zpowers e := by
  obtain ⟨b, c, hirr, ⟨Φ⟩⟩ := exists_mem_normalizer_map_eq_aux4 hR hA2 hani
  have hoddp : Odd p := hp.odd_of_ne_two hp2
  let conjEquiv : (A ≃ₗ[F] A) ≃* ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) :=
    LinearEquiv.autCongr (Φ : A ≃ₗ[F] (Fin 2 → F))
  have he'p : orderOf (conjEquiv e) = p := by rw [conjEquiv.orderOf_eq e, heo]
  have hg'p : orderOf (conjEquiv g) = p := by rw [conjEquiv.orderOf_eq g, hgo]
  have he'rot : conjEquiv e ∈ omegaRotations b c :=
    exists_mem_normalizer_map_eq_aux1 hirr (exists_mem_normalizer_map_eq_aux2 Φ he)
      (by rw [he'p]; exact hoddp)
  have hg'rot : conjEquiv g ∈ omegaRotations b c :=
    exists_mem_normalizer_map_eq_aux1 hirr (exists_mem_normalizer_map_eq_aux2 Φ hg)
      (by rw [hg'p]; exact hoddp)
  obtain ⟨m, hm⟩ := exists_mem_normalizer_map_eq_aux3 hirr he'rot hg'rot he'p hg'p
  refine Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast]
  have hconj : conjEquiv (e ^ m) = conjEquiv g := by rw [map_pow, hm]
  exact conjEquiv.injective hconj

private noncomputable def exists_mem_normalizer_map_eq_aux6 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) (j : Fin m) : V →ₗ[F] U j :=
  LinearMap.linearProjOfIsCompl (polarPerp Q (U j)) (U j).subtype Subtype.val_injective
    (by simpa using isCompl_polarPerp (Q := Q) (hU.nondeg j))

private theorem exists_mem_normalizer_map_eq_aux7 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) (j : Fin m) :
    (∀ x : U j, exists_mem_normalizer_map_eq_aux6 hU j (x : V) = x) ∧
    (∀ x ∈ polarPerp Q (U j), exists_mem_normalizer_map_eq_aux6 hU j x = 0) :=
  ⟨fun x => LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ x,
    fun x hx => LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ x hx⟩

private theorem exists_mem_normalizer_map_eq_aux8 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {i j : Fin m} (hij : i ≠ j) {x : V} (hx : x ∈ U j) :
    x ∈ polarPerp Q (U i) :=
  mem_polarPerp_iff.2 fun y hy => hU.perp i j hij y hy x hx

private noncomputable def exists_mem_normalizer_map_eq_aux9 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (φ : U a ≃ₗ[F] U b) : V →ₗ[F] V :=
  (LinearMap.id : V →ₗ[F] V)
    + ((U b).subtype.comp (φ.toLinearMap.comp (exists_mem_normalizer_map_eq_aux6 hU a))
        + (U a).subtype.comp (exists_mem_normalizer_map_eq_aux6 hU a))
    + ((U a).subtype.comp (φ.symm.toLinearMap.comp (exists_mem_normalizer_map_eq_aux6 hU b))
        + (U b).subtype.comp (exists_mem_normalizer_map_eq_aux6 hU b))

private theorem exists_mem_normalizer_map_eq_aux11 {M : Type*} [AddCommGroup M] [Module F M]
    (v : M) : v + v = 0 := by
  rw [← two_smul (R := F), CharTwo.two_eq_zero, zero_smul]

private theorem exists_mem_normalizer_map_eq_aux12 {M : Type*} [AddCommGroup M] [Module F M]
    (v : M) : (2 : ℤ) • v = 0 := by
  rw [two_zsmul, ← two_smul (R := F), CharTwo.two_eq_zero, zero_smul]

private theorem exists_mem_normalizer_map_eq_aux10a {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (φ : U a ≃ₗ[F] U b) (x : V) :
    exists_mem_normalizer_map_eq_aux9 hU φ x =
      x + (((U b).subtype (φ.toLinearMap (exists_mem_normalizer_map_eq_aux6 hU a x)) : V)
        + ((U a).subtype (exists_mem_normalizer_map_eq_aux6 hU a x) : V))
        + (((U a).subtype (φ.symm.toLinearMap (exists_mem_normalizer_map_eq_aux6 hU b x)) : V)
        + ((U b).subtype (exists_mem_normalizer_map_eq_aux6 hU b x) : V)) := rfl

private theorem exists_mem_normalizer_map_eq_aux10b {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) :
    (∀ y : U b, (y : V) ∈ polarPerp Q (U a)) ∧ (∀ x : U a, (x : V) ∈ polarPerp Q (U b)) :=
  ⟨fun y => exists_mem_normalizer_map_eq_aux8 hU hab y.2,
   fun x => exists_mem_normalizer_map_eq_aux8 hU (Ne.symm hab) x.2⟩

private theorem exists_mem_normalizer_map_eq_aux10 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) :
    Function.Involutive (exists_mem_normalizer_map_eq_aux9 hU φ) := by
  let πa := exists_mem_normalizer_map_eq_aux6 hU a
  let πb := exists_mem_normalizer_map_eq_aux6 hU b
  have hπa_id : ∀ x : U a, πa (x : V) = x := (exists_mem_normalizer_map_eq_aux7 hU a).1
  have hπa_perp : ∀ x ∈ polarPerp Q (U a), πa x = 0 := (exists_mem_normalizer_map_eq_aux7 hU a).2
  have hπb_id : ∀ x : U b, πb (x : V) = x := (exists_mem_normalizer_map_eq_aux7 hU b).1
  have hπb_perp : ∀ x ∈ polarPerp Q (U b), πb x = 0 := (exists_mem_normalizer_map_eq_aux7 hU b).2
  obtain ⟨hUb_perp, hUa_perp⟩ := exists_mem_normalizer_map_eq_aux10b hU hab
  have hπaf : ∀ x, πa (exists_mem_normalizer_map_eq_aux9 hU φ x) = φ.symm (πb x) := by
    intro x
    rw [exists_mem_normalizer_map_eq_aux10a hU φ x]
    simp only [map_add, Submodule.coe_subtype]
    rw [hπa_perp _ (hUb_perp (φ.toLinearMap (πa x))), hπa_id (πa x),
      hπa_id (φ.symm.toLinearMap (πb x)), hπa_perp _ (hUb_perp (πb x))]
    simp only [add_zero, zero_add]
    abel_nf
    simp only [exists_mem_normalizer_map_eq_aux12 (F := F), zero_add]
    rfl
  have hπbf : ∀ x, πb (exists_mem_normalizer_map_eq_aux9 hU φ x) = φ (πa x) := by
    intro x
    rw [exists_mem_normalizer_map_eq_aux10a hU φ x]
    simp only [map_add, Submodule.coe_subtype]
    rw [hπb_id (φ.toLinearMap (πa x)), hπb_perp _ (hUa_perp (πa x)),
      hπb_perp _ (hUa_perp (φ.symm.toLinearMap (πb x))), hπb_id (πb x)]
    simp only [add_zero, zero_add]
    abel_nf
    simp only [exists_mem_normalizer_map_eq_aux12 (F := F), zero_add]
    rfl
  intro x
  rw [exists_mem_normalizer_map_eq_aux10a hU φ (exists_mem_normalizer_map_eq_aux9 hU φ x)]
  rw [hπaf x, hπbf x]
  have h1 : (U b).subtype ((φ : U a → U b) (φ.symm (πb x))) = (U b).subtype (πb x) :=
    congrArg (U b).subtype (LinearEquiv.apply_symm_apply φ (πb x))
  have h2 : (U a).subtype ((φ.symm : U b → U a) (φ (πa x))) = (U a).subtype (πa x) :=
    congrArg (U a).subtype (LinearEquiv.symm_apply_apply φ (πa x))
  change (exists_mem_normalizer_map_eq_aux9 hU φ x)
      + ((U b).subtype (φ (φ.symm (πb x))) + (U a).subtype (φ.symm (πb x)))
      + ((U a).subtype (φ.symm (φ (πa x))) + (U b).subtype (φ (πa x))) = x
  rw [h1, h2, exists_mem_normalizer_map_eq_aux10a hU φ x]
  change x + ((U b).subtype (φ (πa x)) + (U a).subtype (πa x))
      + ((U a).subtype (φ.symm (πb x)) + (U b).subtype (πb x))
      + ((U b).subtype (πb x) + (U a).subtype (φ.symm (πb x)))
      + ((U a).subtype (πa x) + (U b).subtype (φ (πa x))) = x
  abel_nf
  simp only [exists_mem_normalizer_map_eq_aux12 (F := F), add_zero, zero_add]

private noncomputable def exists_mem_normalizer_map_eq_aux13 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) : V ≃ₗ[F] V :=
  LinearEquiv.ofInvolutive (exists_mem_normalizer_map_eq_aux9 hU φ)
    (exists_mem_normalizer_map_eq_aux10 hU hab φ)

private theorem exists_mem_normalizer_map_eq_aux14 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b)
    (x : V) : (exists_mem_normalizer_map_eq_aux13 hU hab φ) x =
      x + ((U b).subtype (φ.toLinearMap (exists_mem_normalizer_map_eq_aux6 hU a x))
            + (U a).subtype (exists_mem_normalizer_map_eq_aux6 hU a x))
        + ((U a).subtype (φ.symm.toLinearMap (exists_mem_normalizer_map_eq_aux6 hU b x))
            + (U b).subtype (exists_mem_normalizer_map_eq_aux6 hU b x)) := by
  rfl

private theorem exists_mem_normalizer_map_eq_aux15 {W : Submodule F V} {E : V ≃ₗ[F] V}
    (hE : ∀ x ∈ W, E x ∈ W) : ∀ x ∈ W, E.symm x ∈ W := by
  intro x hx
  have hinj : Function.Injective (E.toLinearMap.restrict hE) := fun y z h =>
    Subtype.ext (E.injective (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hinj ⟨x, hx⟩
  have h : E (y : V) = x := congrArg Subtype.val hy
  rw [← h, E.symm_apply_apply]
  exact y.2

private theorem exists_mem_normalizer_map_eq_aux16 {W : Submodule F V} {E : V ≃ₗ[F] V}
    (h1 : ∀ x ∈ W, E x ∈ W) (h2 : ∀ x ∈ W, E.symm x ∈ W) (n : ℕ) (u : W) :
    ((restrictEquiv W E h1 h2 ^ n) u : V) = (E ^ n) (u : V) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ (restrictEquiv W E h1 h2) n, LinearEquiv.mul_apply, ih, pow_succ E n,
      LinearEquiv.mul_apply]
    rfl

private theorem exists_mem_normalizer_map_eq_aux17 {W : Submodule F V} {E : V ≃ₗ[F] V}
    (hE : E ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : ∀ x ∈ W, E x ∈ W)
    (h2 : ∀ x ∈ W, E.symm x ∈ W) :
    restrictEquiv W E h1 h2 ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro u
  change Q ((restrictEquiv W E h1 h2 u : W) : V) = Q (u : V)
  rw [coe_restrictEquiv]
  exact map_of_mem hE (u : V)

private theorem exists_mem_normalizer_map_eq_aux18 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) (hp : p.Prime) {j : Fin m} {E : V ≃ₗ[F] V}
    (h1 : ∀ x ∈ U j, E x ∈ U j) (h2 : ∀ x ∈ U j, E.symm x ∈ U j) (hEp : E ^ p = 1)
    (hfix : ∀ x ∈ U j, E x = x → x = 0) : orderOf (restrictEquiv (U j) E h1 h2) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ fun h => ?_
  · refine LinearEquiv.ext fun u => Subtype.ext ?_
    rw [exists_mem_normalizer_map_eq_aux16 h1 h2, hEp]
    rfl
  · obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j) (hU.finrank_eq j)
    exact hv0 (hfix v hv (congrArg (fun ρ : U j ≃ₗ[F] U j => (ρ ⟨v, hv⟩ : V)) h))

private theorem exists_mem_normalizer_map_eq_aux19 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) (hp : p.Prime) (hp2 : p ≠ 2) (j : Fin m)
    {ρ : ↥(U j) ≃ₗ[F] ↥(U j)}
    (hρ : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U j).subtype))
    (hρp : orderOf ρ = p) : p ∣ Nat.card F + 1 := by
  have hdvd : (p : ℤ) ∣
      (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U j).subtype)) : ℤ) := by
    have h := orderOf_dvd_natCard
      (⟨ρ, hρ⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U j).subtype)))
    rw [Subgroup.orderOf_mk, hρp] at h
    exact Int.natCast_dvd_natCast.mpr h
  rw [natCard_orthogonalGroup_of_type (hU.nondeg j) (m := 0) (by rw [hU.finrank_eq j])
    (Or.inr ⟨rfl, hU.not_isPlusType j⟩)] at hdvd
  simp only [zero_mul, pow_zero, mul_one, zero_add, pow_one, Finset.Icc_eq_empty_of_lt
    zero_lt_one, Finset.prod_empty, sub_neg_eq_add] at hdvd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2' : ¬ (p : ℤ) ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (Int.natCast_dvd_natCast.mp h))
  exact_mod_cast (hpZ.dvd_mul.mp hdvd).resolve_left hp2'

private theorem exists_mem_normalizer_map_eq_aux20 {E : V ≃ₗ[F] V} {y : V} (hy : E y = y)
    (n : ℕ) : (E ^ n) y = y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hy, ih]

private theorem exists_mem_normalizer_map_eq_aux21 {W : Submodule F V}
    (hW : IsCompl W (polarPerp Q W)) {E₁ E₂ : V ≃ₗ[F] V}
    (hperp₁ : ∀ x ∈ polarPerp Q W, E₁ x = x) (hperp₂ : ∀ x ∈ polarPerp Q W, E₂ x = x)
    (hW' : ∀ x ∈ W, E₁ x = E₂ x) : E₁ = E₂ := by
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ W ⊔ polarPerp Q W := by rw [hW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, map_add, hW' w hw, hperp₁ y hy, hperp₂ y hy]

private theorem exists_mem_normalizer_map_eq_aux22 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) (hp : p.Prime) (hp2 : p ≠ 2) (j : Fin m) {E₁ E₂ : V ≃ₗ[F] V}
    (hO₁ : E₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hO₂ : E₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hp₁ : E₁ ^ p = 1) (hp₂ : E₂ ^ p = 1)
    (hfix₁ : ∀ x ∈ U j, E₁ x = x → x = 0) (hfix₂ : ∀ x ∈ U j, E₂ x = x → x = 0)
    (hmap₁ : ∀ x ∈ U j, E₁ x ∈ U j) (hmap₂ : ∀ x ∈ U j, E₂ x ∈ U j) :
    ∃ n : ℕ, restrictEquiv (U j) E₁ hmap₁ (exists_mem_normalizer_map_eq_aux15 hmap₁) ^ n =
      restrictEquiv (U j) E₂ hmap₂ (exists_mem_normalizer_map_eq_aux15 hmap₂) := by
  have ho₁ := exists_mem_normalizer_map_eq_aux18 hU hp hmap₁
    (exists_mem_normalizer_map_eq_aux15 hmap₁) hp₁ hfix₁
  have ho₂ := exists_mem_normalizer_map_eq_aux18 hU hp hmap₂
    (exists_mem_normalizer_map_eq_aux15 hmap₂) hp₂ hfix₂
  have hρ₁ := exists_mem_normalizer_map_eq_aux17 hO₁ hmap₁
    (exists_mem_normalizer_map_eq_aux15 hmap₁)
  have hρ₂ := exists_mem_normalizer_map_eq_aux17 hO₂ hmap₂
    (exists_mem_normalizer_map_eq_aux15 hmap₂)
  have han : ∀ x : ↥(U j), (Q.comp (U j).subtype) x = 0 → x = 0 := fun x hx =>
    by_contra fun hx0 => exists_mem_normalizer_conj_eq_of_isEvenFlip_aux5 hU j hx0 hx
  have hmem := exists_mem_normalizer_map_eq_aux5 (hU.nondeg j) (hU.finrank_eq j) han hp hp2
    (exists_mem_normalizer_map_eq_aux19 hU hp hp2 j hρ₁ ho₁) hρ₁ ho₁ hρ₂ ho₂
  have hfo := orderOf_pos_iff.1 (ho₁ ▸ hp.pos)
  exact (Submonoid.mem_powers_iff _ _).1 ((hfo.mem_powers_iff_mem_zpowers).2 hmem)

private theorem exists_mem_normalizer_map_eq_aux23 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) (hp : p.Prime) (hp2 : p ≠ 2) (j : Fin m) {E₁ E₂ : V ≃ₗ[F] V}
    (hO₁ : E₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hO₂ : E₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hp₁ : E₁ ^ p = 1) (hp₂ : E₂ ^ p = 1)
    (hperp₁ : ∀ x ∈ polarPerp Q (U j), E₁ x = x) (hperp₂ : ∀ x ∈ polarPerp Q (U j), E₂ x = x)
    (hfix₁ : ∀ x ∈ U j, E₁ x = x → x = 0) (hfix₂ : ∀ x ∈ U j, E₂ x = x → x = 0)
    (hmap₁ : ∀ x ∈ U j, E₁ x ∈ U j) (hmap₂ : ∀ x ∈ U j, E₂ x ∈ U j) :
    ∃ n : ℕ, E₁ ^ n = E₂ := by
  obtain ⟨n, hn⟩ := exists_mem_normalizer_map_eq_aux22 hU hp hp2 j hO₁ hO₂ hp₁ hp₂ hfix₁ hfix₂
    hmap₁ hmap₂
  refine ⟨n, exists_mem_normalizer_map_eq_aux21 (isCompl_polarPerp (hU.nondeg j))
    (fun y hy => exists_mem_normalizer_map_eq_aux20 (hperp₁ y hy) n) hperp₂ fun x hx => ?_⟩
  exact (exists_mem_normalizer_map_eq_aux16 hmap₁ (exists_mem_normalizer_map_eq_aux15 hmap₁) n
    ⟨x, hx⟩).symm.trans (congrArg (fun ρ : ↥(U j) ≃ₗ[F] ↥(U j) => (ρ ⟨x, hx⟩ : V)) hn)

private theorem exists_mem_normalizer_map_eq_aux24 {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {W W' : Submodule F V}
    (h1 : ∀ x ∈ W', σ x ∈ W) {x : V} (hx : x ∈ polarPerp Q W) : σ.symm x ∈ polarPerp Q W' := by
  refine mem_polarPerp_iff.2 fun y hy => ?_
  rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσ y (σ.symm x),
    σ.apply_symm_apply]
  exact mem_polarPerp_iff.1 hx (σ y) (h1 y hy)

private theorem exists_mem_normalizer_map_eq_aux25 {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime) (hp2 : p ≠ 2) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {i i' : Fin m}
    (h1 : ∀ x ∈ U i, σ x ∈ U i') (h2 : ∀ x ∈ U i', σ.symm x ∈ U i) :
    ∃ n : ℕ, (e i' : V ≃ₗ[F] V) ^ n = σ * (e i : V ≃ₗ[F] V) * σ⁻¹ := by
  have hEO : ∀ k, (e k : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun k => orthDerived_le_orthogonalGroup (e k).2
  have hEp : ∀ k, (e k : V ≃ₗ[F] V) ^ p = 1 := fun k => by
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hF.orderOf_eq k ▸ pow_orderOf_eq_one (e k))
    simpa using this
  refine exists_mem_normalizer_map_eq_aux23 hF.toIsPlaneSystem hp hp2 i' (hEO i')
    (mul_mem (mul_mem hσ (hEO i)) (inv_mem hσ)) (hEp i') ?_ (hF.apply_of_perp i') ?_
    (hF.eq_zero_of_apply_eq i') ?_ (hF.maps_to i') fun x hx => h1 _ (hF.maps_to i _ (h2 x hx))
  · rw [conj_pow, hEp i, mul_one, mul_inv_cancel]
  · intro x hx
    show σ ((e i : V ≃ₗ[F] V) (σ.symm x)) = x
    rw [hF.apply_of_perp i _ (exists_mem_normalizer_map_eq_aux24 hσ h1 hx), σ.apply_symm_apply]
  · intro x hx hfx
    have hy : (e i : V ≃ₗ[F] V) (σ.symm x) = σ.symm x := by
      apply σ.injective
      rw [σ.apply_symm_apply]
      exact hfx
    simpa using congrArg σ (hF.eq_zero_of_apply_eq i _ (h2 x hx) hy)

private theorem exists_mem_normalizer_map_eq_aux26 {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {c : ↥(orthDerived Q)} (hc : ∀ j, c * e j * c⁻¹ ∈ Bb) :
    ∀ h ∈ Bb, c * h * c⁻¹ ∈ Bb := by
  intro h hh
  rw [← hF.closure_eq] at hh
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hc j
  | one => simpa using Bb.one_mem
  | mul a b ha hb iha ihb =>
      rw [show c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) by group]
      exact Bb.mul_mem iha ihb
  | inv a ha iha =>
      rw [show c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ by group]
      exact Bb.inv_mem iha

private theorem exists_mem_normalizer_map_eq_aux27 {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {g : ↥(orthDerived Q)} (hg : ∀ j, g * e j * g⁻¹ ∈ Bb)
    (hg' : ∀ j, g⁻¹ * e j * g⁻¹⁻¹ ∈ Bb) : g ∈ Subgroup.normalizer (Bb : Set ↥(orthDerived Q)) := by
  have hfwd := exists_mem_normalizer_map_eq_aux26 hF hg
  have hbwd := exists_mem_normalizer_map_eq_aux26 hF hg'
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨hfwd h, fun hh => ?_⟩
  have h1 := hbwd _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h1

private theorem exists_mem_normalizer_map_eq_aux28 {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime) (hp2 : p ≠ 2) {c : ↥(orthDerived Q)}
    {i i' : Fin m} (h1 : ∀ x ∈ U i, (c : V ≃ₗ[F] V) x ∈ U i')
    (h2 : ∀ x ∈ U i', (c : V ≃ₗ[F] V).symm x ∈ U i) : c * e i * c⁻¹ ∈ Bb := by
  obtain ⟨n, hn⟩ := exists_mem_normalizer_map_eq_aux25 hF hp hp2
    (orthDerived_le_orthogonalGroup c.2) h1 h2
  rw [show c * e i * c⁻¹ = (e i') ^ n from Subtype.ext hn.symm]
  exact Bb.pow_mem (hF.mem i') n

private theorem exists_mem_normalizer_map_eq_aux29 {σ : V ≃ₗ[F] V} {W W' : Submodule F V}
    (h : Submodule.map σ.toLinearMap W = W') :
    (∀ x ∈ W, σ x ∈ W') ∧ ∀ x ∈ W', σ.symm x ∈ W := by
  subst h
  refine ⟨fun x hx => Submodule.mem_map_of_mem hx, fun x hx => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hx
  simpa using hw

private theorem exists_mem_normalizer_map_eq_aux30 {σ : V ≃ₗ[F] V} {W : Submodule F V}
    (h : ∀ x ∈ W, σ x = x) : (∀ x ∈ W, σ x ∈ W) ∧ ∀ x ∈ W, σ.symm x ∈ W :=
  ⟨fun x hx => by rw [h x hx]; exact hx,
    fun x hx => by rw [(LinearEquiv.symm_apply_eq σ).2 (h x hx).symm]; exact hx⟩

private theorem exists_mem_normalizer_map_eq_aux31 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b k : Fin m} (hka : k ≠ a) (hkb : k ≠ b) {x : V} (hx : x ∈ U k) :
    x ∈ polarPerp Q (U a ⊔ U b) := by
  refine mem_polarPerp_iff.2 fun y hy => ?_
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
  rw [polar_add_left, hU.perp a k (Ne.symm hka) y₁ hy₁ x hx,
    hU.perp b k (Ne.symm hkb) y₂ hy₂ x hx, add_zero]

private theorem exists_mem_normalizer_map_eq_aux32 {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime) (hp2 : p ≠ 2) {a b : Fin m}
    {g : ↥(orthDerived Q)} (hga : Submodule.map (g : V ≃ₗ[F] V).toLinearMap (U a) = U b)
    (hgb : Submodule.map (g : V ≃ₗ[F] V).toLinearMap (U b) = U a)
    (hgfix : ∀ x ∈ polarPerp Q (U a ⊔ U b), (g : V ≃ₗ[F] V) x = x) :
    g ∈ Subgroup.normalizer (Bb : Set ↥(orthDerived Q)) := by
  have hother : ∀ j, j ≠ a → j ≠ b → ∀ x ∈ U j, (g : V ≃ₗ[F] V) x = x := fun j hja hjb x hx =>
    hgfix x (exists_mem_normalizer_map_eq_aux31 hF.toIsPlaneSystem hja hjb hx)
  refine exists_mem_normalizer_map_eq_aux27 hF (fun j => ?_) fun j => ?_
  · by_cases hja : j = a
    · subst hja
      exact exists_mem_normalizer_map_eq_aux28 hF hp hp2 (exists_mem_normalizer_map_eq_aux29 hga).1
        (exists_mem_normalizer_map_eq_aux29 hga).2
    · by_cases hjb : j = b
      · subst hjb
        exact exists_mem_normalizer_map_eq_aux28 hF hp hp2
          (exists_mem_normalizer_map_eq_aux29 hgb).1 (exists_mem_normalizer_map_eq_aux29 hgb).2
      · exact exists_mem_normalizer_map_eq_aux28 hF hp hp2
          (exists_mem_normalizer_map_eq_aux30 (hother j hja hjb)).1
          (exists_mem_normalizer_map_eq_aux30 (hother j hja hjb)).2
  · by_cases hja : j = a
    · subst hja
      exact exists_mem_normalizer_map_eq_aux28 hF hp hp2 (c := g⁻¹)
        (exists_mem_normalizer_map_eq_aux29 hgb).2 (exists_mem_normalizer_map_eq_aux29 hgb).1
    · by_cases hjb : j = b
      · subst hjb
        exact exists_mem_normalizer_map_eq_aux28 hF hp hp2 (c := g⁻¹)
          (exists_mem_normalizer_map_eq_aux29 hga).2 (exists_mem_normalizer_map_eq_aux29 hga).1
      · exact exists_mem_normalizer_map_eq_aux28 hF hp hp2 (c := g⁻¹)
          (exists_mem_normalizer_map_eq_aux30 (hother j hja hjb)).2
          (exists_mem_normalizer_map_eq_aux30 (hother j hja hjb)).1

private theorem exists_swap_isometry_aux1 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) (a b : Fin m) :
    ∃ φ : U a ≃ₗ[F] U b, ∀ x : U a, Q ((φ x : U b) : V) = Q (x : V) := by
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff (hU.nondeg a) (hU.nondeg b) (n := 1)
    (by rw [hU.finrank_eq a]) (by rw [hU.finrank_eq b])
    ⟨fun h => absurd h (hU.not_isPlusType a), fun h => absurd h (hU.not_isPlusType b)⟩
  exact ⟨e.toLinearEquiv, fun x => e.map_app x⟩

private theorem exists_swap_isometry_aux2 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) (j : Fin m) (x : V) :
    x - ((exists_mem_normalizer_map_eq_aux6 hU j x : U j) : V) ∈ polarPerp Q (U j) := by
  have hker : LinearMap.ker (exists_mem_normalizer_map_eq_aux6 hU j) = polarPerp Q (U j) :=
    LinearMap.ker_linearProjOfIsCompl _ _ _ _
  rw [← hker, LinearMap.mem_ker, map_sub,
    (exists_mem_normalizer_map_eq_aux7 hU j).1 (exists_mem_normalizer_map_eq_aux6 hU j x), sub_self]

private theorem exists_swap_isometry_aux3 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (x : V) :
    x - ((exists_mem_normalizer_map_eq_aux6 hU a x : U a) : V)
        - ((exists_mem_normalizer_map_eq_aux6 hU b x : U b) : V) ∈ polarPerp Q (U a) ∧
    x - ((exists_mem_normalizer_map_eq_aux6 hU a x : U a) : V)
        - ((exists_mem_normalizer_map_eq_aux6 hU b x : U b) : V) ∈ polarPerp Q (U b) := by
  refine ⟨Submodule.sub_mem _ (exists_swap_isometry_aux2 hU a x)
      (exists_mem_normalizer_map_eq_aux8 hU hab (exists_mem_normalizer_map_eq_aux6 hU b x).2), ?_⟩
  rw [sub_right_comm]
  exact Submodule.sub_mem _ (exists_swap_isometry_aux2 hU b x)
    (exists_mem_normalizer_map_eq_aux8 hU (Ne.symm hab)
      (exists_mem_normalizer_map_eq_aux6 hU a x).2)

private theorem exists_swap_isometry_aux4 (s t r : V) (hst : polar Q s t = 0)
    (hsr : polar Q s r = 0) (htr : polar Q t r = 0) : Q (s + t + r) = Q s + Q t + Q r := by
  rw [QuadraticMap.map_add Q (s + t) r, QuadraticMap.map_add Q s t, polar_add_left, hsr, htr, hst]
  ring

private theorem exists_swap_isometry_aux5 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) (x : V) :
    exists_mem_normalizer_map_eq_aux13 hU hab φ x =
      ((φ (exists_mem_normalizer_map_eq_aux6 hU a x) : U b) : V) +
        ((φ.symm (exists_mem_normalizer_map_eq_aux6 hU b x) : U a) : V) +
        (x - ((exists_mem_normalizer_map_eq_aux6 hU a x : U a) : V) -
          ((exists_mem_normalizer_map_eq_aux6 hU b x : U b) : V)) := by
  rw [exists_mem_normalizer_map_eq_aux14]
  simp only [Submodule.coe_subtype, LinearEquiv.coe_coe]
  have key : ∀ A B C D y : V, B + B = 0 → D + D = 0 →
      y + (A + B) + (C + D) = A + C + (y - B - D) := by
    intro A B C D y hB hD
    calc y + (A + B) + (C + D) = A + C + (y - B - D) + (B + B) + (D + D) := by abel
      _ = A + C + (y - B - D) := by rw [hB, hD, add_zero, add_zero]
  exact key _ _ _ _ _ (exists_mem_normalizer_map_eq_aux11 (F := F) _)
    (exists_mem_normalizer_map_eq_aux11 (F := F) _)

private theorem exists_swap_isometry_aux6 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b)
    (hφ : ∀ x : U a, Q ((φ x : U b) : V) = Q (x : V)) (x : V) :
    Q (exists_mem_normalizer_map_eq_aux13 hU hab φ x) = Q x := by
  obtain ⟨hra, hrb⟩ := exists_swap_isometry_aux3 hU hab x
  rw [exists_swap_isometry_aux5 hU hab φ x]
  generalize exists_mem_normalizer_map_eq_aux6 hU a x = u at hra hrb ⊢
  generalize exists_mem_normalizer_map_eq_aux6 hU b x = w at hra hrb ⊢
  generalize hr : x - (u : V) - (w : V) = r at hra hrb ⊢
  have hx : x = (u : V) + (w : V) + r := by rw [← hr]; abel
  have hφw : Q ((φ.symm w : U a) : V) = Q (w : V) := by
    have h := hφ (φ.symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  rw [hx, exists_swap_isometry_aux4 _ _ _ (hU.perp b a (Ne.symm hab) _ (φ u).2 _ (φ.symm w).2)
      (mem_polarPerp_iff.1 hrb _ (φ u).2) (mem_polarPerp_iff.1 hra _ (φ.symm w).2),
    exists_swap_isometry_aux4 _ _ _ (hU.perp a b hab _ u.2 _ w.2)
      (mem_polarPerp_iff.1 hra _ u.2) (mem_polarPerp_iff.1 hrb _ w.2), hφ u, hφw]

private theorem exists_swap_isometry_aux7 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) (u : U a) :
    exists_mem_normalizer_map_eq_aux13 hU hab φ (u : V) = ((φ u : U b) : V) := by
  rw [exists_swap_isometry_aux5 hU hab φ, (exists_mem_normalizer_map_eq_aux7 hU a).1 u,
    (exists_mem_normalizer_map_eq_aux7 hU b).2 _
      (exists_mem_normalizer_map_eq_aux8 hU (Ne.symm hab) u.2)]
  simp

private theorem exists_swap_isometry_aux8 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) (w : U b) :
    exists_mem_normalizer_map_eq_aux13 hU hab φ (w : V) = ((φ.symm w : U a) : V) := by
  rw [exists_swap_isometry_aux5 hU hab φ, (exists_mem_normalizer_map_eq_aux7 hU b).1 w,
    (exists_mem_normalizer_map_eq_aux7 hU a).2 _ (exists_mem_normalizer_map_eq_aux8 hU hab w.2)]
  simp

private theorem exists_swap_isometry_aux9 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) {y : V}
    (hya : y ∈ polarPerp Q (U a)) (hyb : y ∈ polarPerp Q (U b)) :
    exists_mem_normalizer_map_eq_aux13 hU hab φ y = y := by
  rw [exists_swap_isometry_aux5 hU hab φ, (exists_mem_normalizer_map_eq_aux7 hU a).2 y hya,
    (exists_mem_normalizer_map_eq_aux7 hU b).2 y hyb]
  simp

private theorem exists_swap_isometry_aux10 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) :
    Submodule.map (exists_mem_normalizer_map_eq_aux13 hU hab φ).toLinearMap (U a) = U b := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [show (exists_mem_normalizer_map_eq_aux13 hU hab φ).toLinearMap x = ((φ ⟨x, hx⟩ : U b) : V)
      from exists_swap_isometry_aux7 hU hab φ ⟨x, hx⟩]
    exact (φ ⟨x, hx⟩).2
  · refine ⟨((φ.symm ⟨y, hy⟩ : U a) : V), (φ.symm ⟨y, hy⟩).2, ?_⟩
    rw [show (exists_mem_normalizer_map_eq_aux13 hU hab φ).toLinearMap ((φ.symm ⟨y, hy⟩ : U a) : V)
      = ((φ (φ.symm ⟨y, hy⟩) : U b) : V) from exists_swap_isometry_aux7 hU hab φ _,
      LinearEquiv.apply_symm_apply]

private theorem exists_swap_isometry_aux11 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) :
    Submodule.map (exists_mem_normalizer_map_eq_aux13 hU hab φ).toLinearMap (U b) = U a := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [show (exists_mem_normalizer_map_eq_aux13 hU hab φ).toLinearMap x =
        ((φ.symm ⟨x, hx⟩ : U a) : V) from exists_swap_isometry_aux8 hU hab φ ⟨x, hx⟩]
    exact (φ.symm ⟨x, hx⟩).2
  · refine ⟨((φ ⟨y, hy⟩ : U b) : V), (φ ⟨y, hy⟩).2, ?_⟩
    rw [show (exists_mem_normalizer_map_eq_aux13 hU hab φ).toLinearMap ((φ ⟨y, hy⟩ : U b) : V)
      = ((φ.symm (φ ⟨y, hy⟩) : U a) : V) from exists_swap_isometry_aux8 hU hab φ _,
      LinearEquiv.symm_apply_apply]

theorem exists_swap_isometry {m : ℕ} {U : Fin m → Submodule F V} (hU : IsPlaneSystem Q U)
    {a b : Fin m} (hab : a ≠ b) :
    ∃ σ : V ≃ₗ[F] V, σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      Submodule.map σ.toLinearMap (U a) = U b ∧ Submodule.map σ.toLinearMap (U b) = U a ∧
      ∀ k, k ≠ a → k ≠ b → ∀ x ∈ U k, σ x = x := by
  obtain ⟨φ, hφ⟩ := exists_swap_isometry_aux1 hU a b
  refine ⟨exists_mem_normalizer_map_eq_aux13 hU hab φ,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (exists_swap_isometry_aux6 hU hab φ hφ),
    exists_swap_isometry_aux10 hU hab φ, exists_swap_isometry_aux11 hU hab φ,
    fun k hka hkb x hx => ?_⟩
  exact exists_swap_isometry_aux9 hU hab φ (exists_mem_normalizer_map_eq_aux8 hU (Ne.symm hka) hx)
    (exists_mem_normalizer_map_eq_aux8 hU (Ne.symm hkb) hx)

private theorem exists_swap_mem_orthDerived_aux1 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) :
    exists_mem_normalizer_map_eq_aux13 hU hab φ * exists_mem_normalizer_map_eq_aux13 hU hab φ =
      1 :=
  LinearEquiv.ext fun x => exists_mem_normalizer_map_eq_aux10 hU hab φ x

private theorem exists_swap_mem_orthDerived_aux2 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b) (x : V) :
    exists_mem_normalizer_map_eq_aux13 hU hab φ x - x =
      ((φ (exists_mem_normalizer_map_eq_aux6 hU a x +
          φ.symm (exists_mem_normalizer_map_eq_aux6 hU b x)) : U b) : V) +
        ((exists_mem_normalizer_map_eq_aux6 hU a x +
          φ.symm (exists_mem_normalizer_map_eq_aux6 hU b x) : U a) : V) := by
  rw [exists_mem_normalizer_map_eq_aux14]
  simp only [Submodule.coe_subtype, LinearEquiv.coe_coe, map_add, LinearEquiv.apply_symm_apply,
    Submodule.coe_add]
  abel

private theorem exists_swap_mem_orthDerived_aux3 {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b)
    (hφ : ∀ x : U a, Q ((φ x : U b) : V) = Q (x : V)) (x : V) :
    Q (exists_mem_normalizer_map_eq_aux13 hU hab φ x - x) = 0 := by
  rw [exists_swap_mem_orthDerived_aux2 hU hab φ x]
  generalize (exists_mem_normalizer_map_eq_aux6 hU a x +
    φ.symm (exists_mem_normalizer_map_eq_aux6 hU b x) : U a) = z
  rw [QuadraticMap.map_add Q, hU.perp b a (Ne.symm hab) _ (φ z).2 _ z.2, hφ z, add_zero]
  exact CharTwo.add_self_eq_zero _

private theorem exists_swap_mem_orthDerived_aux4 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) (φ : U a ≃ₗ[F] U b)
    (hφ : ∀ x : U a, Q ((φ x : U b) : V) = Q (x : V)) :
    exists_mem_normalizer_map_eq_aux13 hU hab φ ∈ orthDerived Q := by
  have hO := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (exists_swap_isometry_aux6 hU hab φ hφ)
  refine omegaGroup_le_orthDerived hQ
    (exists_mem_normalizer_conj_eq_of_isEvenFlip_aux12 hQ hdim hn) (mem_omegaGroup.2 ⟨hO, ?_⟩)
  refine even_finrank_commSpace_of_forall_eq_zero hQ hO
    (exists_swap_mem_orthDerived_aux1 hU hab φ) fun y hy => ?_
  obtain ⟨x, rfl⟩ := mem_commSpace.1 hy
  exact exists_swap_mem_orthDerived_aux3 hU hab φ hφ x

theorem exists_swap_mem_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) {m : ℕ} {U : Fin m → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin m} (hab : a ≠ b) :
    ∃ σ : ↥(orthDerived Q), Submodule.map (σ : V ≃ₗ[F] V).toLinearMap (U a) = U b ∧
      Submodule.map (σ : V ≃ₗ[F] V).toLinearMap (U b) = U a ∧
      ∀ x ∈ polarPerp Q (U a ⊔ U b), (σ : V ≃ₗ[F] V) x = x := by
  obtain ⟨φ, hφ⟩ := exists_swap_isometry_aux1 hU a b
  refine ⟨⟨exists_mem_normalizer_map_eq_aux13 hU hab φ,
    exists_swap_mem_orthDerived_aux4 hQ hdim hn hU hab φ hφ⟩,
    exists_swap_isometry_aux10 hU hab φ, exists_swap_isometry_aux11 hU hab φ, fun x hx => ?_⟩
  exact exists_swap_isometry_aux9 hU hab φ
    (mem_polarPerp_iff.2 fun y hy => mem_polarPerp_iff.1 hx y (Submodule.mem_sup_left hy))
    (mem_polarPerp_iff.2 fun y hy => mem_polarPerp_iff.1 hx y (Submodule.mem_sup_right hy))

theorem exists_mem_normalizer_map_eq (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) (a b : Fin (n - 1)) :
    ∃ g ∈ Subgroup.normalizer (Bb : Set ↥(orthDerived Q)),
      Submodule.map (g : V ≃ₗ[F] V).toLinearMap (U a) = U b := by
  by_cases hab : a = b
  · subst hab
    exact ⟨1, one_mem _, by simp⟩
  · obtain ⟨σ, hσa, hσb, hσfix⟩ := exists_swap_mem_orthDerived hQ hdim hn hF.toIsPlaneSystem hab
    exact ⟨σ, exists_mem_normalizer_map_eq_aux32 hF hp hp2 hσa hσb hσfix, hσa⟩

private theorem specialBlock_conj_aux_aeval {x k : V ≃ₗ[F] V} (p : F[X]) :
    aeval ((k * x * k⁻¹).toLinearMap) p = (k.conjAlgEquiv F) (aeval x.toLinearMap p) := by
  have hconj : ((k * x * k⁻¹).toLinearMap) = (k.conjAlgEquiv F) x.toLinearMap := by
    ext v
    simp [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.mul_apply]
  rw [hconj]
  exact Polynomial.aeval_algHom_apply (k.conjAlgEquiv F) x.toLinearMap p

private theorem specialBlock_conj_aux_aeval_apply {x k : V ≃ₗ[F] V} (p : F[X]) (v : V) :
    aeval ((k * x * k⁻¹).toLinearMap) p ((k : V ≃ₗ[F] V) v) =
      (k : V ≃ₗ[F] V) (aeval x.toLinearMap p v) := by
  have h1 := LinearMap.congr_fun (specialBlock_conj_aux_aeval (x := x) (k := k) p) ((k : V ≃ₗ[F] V) v)
  simpa [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.mul_apply] using h1

private theorem specialBlock_conj_aux1 {x k : V ≃ₗ[F] V} (h : F[X]) :
    primaryComponent (k * x * k⁻¹).toLinearMap h =
      (primaryComponent x.toLinearMap h).map (k : V →ₗ[F] V) := by
  ext v
  simp only [Submodule.mem_map, mem_primaryComponent]
  constructor
  · intro hv
    refine ⟨(k : V ≃ₗ[F] V)⁻¹ v, ?_, by simp⟩
    have h1 := LinearMap.congr_fun (specialBlock_conj_aux_aeval (x := x) (k := k) h) v
    rw [hv] at h1
    have h3 := congrArg (fun w => (k : V ≃ₗ[F] V)⁻¹ w) h1.symm
    simpa [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.mul_apply] using h3
  · rintro ⟨w, hw, rfl⟩
    rw [specialBlock_conj_aux_aeval]
    simp [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.mul_apply, hw]

private theorem specialBlock_conj_aux2 {x k : V ≃ₗ[F] V} :
    primaryFactors (k * x * k⁻¹).toLinearMap = primaryFactors x.toLinearMap := by
  have hconj : ((k * x * k⁻¹).toLinearMap) = (k.conjAlgEquiv F) x.toLinearMap := by
    ext v
    simp [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.mul_apply]
  unfold primaryFactors
  rw [hconj, minpoly.algEquiv_eq]

private theorem specialBlock_conj_aux3 {x k : V ≃ₗ[F] V} (h : F[X]) :
    othersSpace (k * x * k⁻¹).toLinearMap h =
      (othersSpace x.toLinearMap h).map (k : V →ₗ[F] V) := by
  unfold othersSpace
  rw [specialBlock_conj_aux2 (x := x) (k := k), Submodule.map_iSup]
  refine iSup_congr fun a => ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ => ?_
  exact specialBlock_conj_aux1 (x := x) (k := k) a

private theorem specialBlock_conj_aux_supported {x k : V ≃ₗ[F] V}
    (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {h : F[X]} {s : V ≃ₗ[F] V}
    (hs : s ∈ supportedBlock Q x h) :
    k * s * k⁻¹ ∈ supportedBlock Q (k * x * k⁻¹) h := by
  obtain ⟨hsM, hsfix⟩ := mem_supportedBlock.mp hs
  obtain ⟨hsQ, hsc⟩ := mem_isometryCentralizer.mp hsM
  refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨?_, ?_⟩, ?_⟩
  · intro v
    rw [show (k * s * k⁻¹) v = (k : V ≃ₗ[F] V) (s ((k : V ≃ₗ[F] V)⁻¹ v)) by
      simp [LinearEquiv.mul_apply]]
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hk]
    rw [hsQ]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (Subgroup.inv_mem _ hk) v
  · intro v
    rw [show (k * s * k⁻¹) ((k * x * k⁻¹) v) =
        (k : V ≃ₗ[F] V) (s (x ((k : V ≃ₗ[F] V)⁻¹ v))) by simp [LinearEquiv.mul_apply]]
    rw [show (k * x * k⁻¹) ((k * s * k⁻¹) v) =
        (k : V ≃ₗ[F] V) (x (s ((k : V ≃ₗ[F] V)⁻¹ v))) by simp [LinearEquiv.mul_apply]]
    rw [hsc]
  · intro v hv
    rw [specialBlock_conj_aux3 (x := x) (k := k) h] at hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    show (k * s * k⁻¹) ((k : V ≃ₗ[F] V) w) = (k : V ≃ₗ[F] V) w
    rw [show (k * s * k⁻¹) ((k : V ≃ₗ[F] V) w) =
        (k : V ≃ₗ[F] V) (s ((k : V ≃ₗ[F] V)⁻¹ ((k : V ≃ₗ[F] V) w))) by
      simp [LinearEquiv.mul_apply]]
    have h1 : (k : V ≃ₗ[F] V)⁻¹ ((k : V ≃ₗ[F] V) w) = w := by simp
    rw [h1, hsfix w hw]

private theorem specialBlock_conj_aux_aeval_apply_inv {x k : V ≃ₗ[F] V} (p : F[X]) (v : V) :
    aeval x.toLinearMap p ((k : V ≃ₗ[F] V)⁻¹ v) =
      (k : V ≃ₗ[F] V)⁻¹ (aeval ((k * x * k⁻¹).toLinearMap) p v) := by
  have h := specialBlock_conj_aux_aeval_apply (x := k * x * k⁻¹) (k := (k : V ≃ₗ[F] V)⁻¹) p v
  simp only [inv_inv] at h
  have hx : ((k : V ≃ₗ[F] V)⁻¹ * (k * x * k⁻¹) * k) = x := by group
  rw [hx] at h
  exact h

private noncomputable def specialBlock_conj_aux_iso {x k : V ≃ₗ[F] V} (h : F[X]) :
    primaryComponent x.toLinearMap h ≃ₗ[AdjoinRoot h]
      primaryComponent (k * x * k⁻¹).toLinearMap h := by
  let E := AdjoinRoot h
  let M₁ := primaryComponent x.toLinearMap h
  let M₂ := primaryComponent (k * x * k⁻¹).toLinearMap h
  have hmem : ∀ v : M₁, (k : V ≃ₗ[F] V) v ∈ M₂ := by
    intro v
    change (k : V ≃ₗ[F] V) v ∈ primaryComponent (k * x * k⁻¹).toLinearMap h
    rw [specialBlock_conj_aux1 (x := x) (k := k) h]
    exact Submodule.mem_map_of_mem v.2
  have hmem' : ∀ w : M₂, (k : V ≃ₗ[F] V)⁻¹ w ∈ M₁ := by
    intro w
    change (k : V ≃ₗ[F] V)⁻¹ (w : V) ∈ primaryComponent x.toLinearMap h
    have hw : (w : V) ∈ primaryComponent (k * x * k⁻¹).toLinearMap h := w.2
    rw [specialBlock_conj_aux1 (x := x) (k := k) h] at hw
    obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.mp hw
    have : (k : V ≃ₗ[F] V)⁻¹ (w : V) = u := by rw [← hu']; simp
    rw [this]; exact hu
  let toFun : M₁ →ₗ[E] M₂ :=
    { toFun := fun v => ⟨(k : V ≃ₗ[F] V) v, hmem v⟩
      map_add' := by intro a b; ext; simp [map_add]
      map_smul' := by
        intro c v
        apply Subtype.ext
        induction c using AdjoinRoot.induction_on with
        | ih p =>
          change (k : V ≃ₗ[F] V) (((AdjoinRoot.mk h p) • v : M₁) : V) =
            (((AdjoinRoot.mk h p) • (⟨(k : V ≃ₗ[F] V) v, hmem v⟩ : M₂) : M₂) : V)
          rw [coe_mk_smul_primaryComponent, coe_mk_smul_primaryComponent]
          exact (specialBlock_conj_aux_aeval_apply (x := x) (k := k) p (v : V)).symm }
  let invFun : M₂ →ₗ[E] M₁ :=
    { toFun := fun w => ⟨(k : V ≃ₗ[F] V)⁻¹ w, hmem' w⟩
      map_add' := by intro a b; ext; simp [map_add]
      map_smul' := by
        intro c v
        apply Subtype.ext
        induction c using AdjoinRoot.induction_on with
        | ih p =>
          change (k : V ≃ₗ[F] V)⁻¹ (((AdjoinRoot.mk h p) • v : M₂) : V) =
            (((AdjoinRoot.mk h p) • (⟨(k : V ≃ₗ[F] V)⁻¹ v, hmem' v⟩ : M₁) : M₁) : V)
          rw [coe_mk_smul_primaryComponent, coe_mk_smul_primaryComponent]
          exact (specialBlock_conj_aux_aeval_apply_inv (x := x) (k := k) p (v : V)).symm }
  exact LinearEquiv.ofLinearMap toFun invFun
    (LinearMap.ext fun w => Subtype.ext (by
      change (k : V ≃ₗ[F] V) ((k : V ≃ₗ[F] V)⁻¹ (w : V)) = (w : V)
      simp))
    (LinearMap.ext fun v => Subtype.ext (by
      change (k : V ≃ₗ[F] V)⁻¹ ((k : V ≃ₗ[F] V) (v : V)) = (v : V)
      simp))

private theorem specialBlock_conj_aux_iso_apply {x k : V ≃ₗ[F] V} (h : F[X])
    (u : primaryComponent x.toLinearMap h) :
    (specialBlock_conj_aux_iso (x := x) (k := k) h u : V) = (k : V ≃ₗ[F] V) (u : V) := rfl

private theorem specialBlock_conj_aux_iso_symm_apply {x k : V ≃ₗ[F] V} (h : F[X])
    (w : primaryComponent (k * x * k⁻¹).toLinearMap h) :
    ((specialBlock_conj_aux_iso (x := x) (k := k) h).symm w : V) =
      (k : V ≃ₗ[F] V)⁻¹ (w : V) := rfl

private theorem specialBlock_conj_aux_blockDet {x k : V ≃ₗ[F] V}
    (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {h : F[X]} {b : V ≃ₗ[F] V}
    (hb : b ∈ supportedBlock Q x h)
    (hb' : k * b * k⁻¹ ∈ supportedBlock Q (k * x * k⁻¹) h) :
    blockDet Q (k * x * k⁻¹) h ⟨k * b * k⁻¹, hb'⟩ = blockDet Q x h ⟨b, hb⟩ := by
  let E := AdjoinRoot h
  let M₁ := primaryComponent x.toLinearMap h
  let M₂ := primaryComponent (k * x * k⁻¹).toLinearMap h
  let e : M₁ ≃ₗ[E] M₂ := specialBlock_conj_aux_iso (x := x) (k := k) h
  have he_apply : ∀ u : M₁, (e u : V) = (k : V ≃ₗ[F] V) (u : V) :=
    fun u => specialBlock_conj_aux_iso_apply (x := x) (k := k) h u
  have he_symm_apply : ∀ w : M₂, (e.symm w : V) = (k : V ≃ₗ[F] V)⁻¹ (w : V) :=
    fun w => specialBlock_conj_aux_iso_symm_apply (x := x) (k := k) h w
  have heq : (blockGL Q (k * x * k⁻¹) h ⟨k * b * k⁻¹, hb'⟩ : Module.End E M₂) =
      (e : M₁ →ₗ[E] M₂) ∘ₗ (blockGL Q x h ⟨b, hb⟩ : Module.End E M₁) ∘ₗ
        (e.symm : M₂ →ₗ[E] M₁) := by
    ext w
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change ((k * b * k⁻¹ : V ≃ₗ[F] V)) (w : V) =
      (e (((blockGL Q x h ⟨b, hb⟩ : BlockGL x h) : Module.End E M₁) (e.symm w)) : V)
    rw [he_apply, coe_blockGL, he_symm_apply]
    simp [LinearEquiv.mul_apply]
  rw [blockDet_apply, blockDet_apply, heq, LinearMap.det_conj]

private theorem specialBlock_conj_mem {x k : V ≃ₗ[F] V}
    (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {h : F[X]} {s : V ≃ₗ[F] V}
    (hs : s ∈ specialBlock Q x h) :
    k * s * k⁻¹ ∈ specialBlock Q (k * x * k⁻¹) h := by
  obtain ⟨hsS, hsd⟩ := mem_specialBlock.mp hs
  have hS' := specialBlock_conj_aux_supported hk hsS
  refine mem_specialBlock.mpr ⟨hS', ?_⟩
  rw [specialBlock_conj_aux_blockDet hk hsS hS']
  exact hsd

theorem specialBlock_conj {x g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : F[X]) :
    specialBlock Q (g * x * g⁻¹) h = (specialBlock Q x h).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · rintro y hy
    rw [Subgroup.mem_map]
    refine ⟨(g : V ≃ₗ[F] V)⁻¹ * y * g, ?_, ?_⟩
    · have hx : (g : V ≃ₗ[F] V)⁻¹ * (g * x * g⁻¹) * g = x := by group
      have h' := specialBlock_conj_mem (x := g * x * g⁻¹) (k := (g : V ≃ₗ[F] V)⁻¹)
        (Subgroup.inv_mem _ hg) hy
      simp only [inv_inv] at h'
      rw [hx] at h'
      simpa using h'
    · change (MulAut.conj g) ((g : V ≃ₗ[F] V)⁻¹ * y * g) = y
      rw [MulAut.conj_apply]
      group
  · rintro y ⟨s, hs, rfl⟩
    exact specialBlock_conj_mem hg hs

end CFSG.LocalAnalysis.GLTheoremA.T173U

end

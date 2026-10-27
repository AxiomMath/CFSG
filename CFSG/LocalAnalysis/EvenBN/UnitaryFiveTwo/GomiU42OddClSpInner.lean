module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClSpArith
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClSpBase

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatFC
open LinearMap (BilinForm)
open scoped MatrixGroups

theorem u42_inner_false {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {r : ℕ} (hr : 2 ≤ r) (h2f : r = 2 → 2 ≤ f) (hdim : finrank K V = 2 * r)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w)
    (h1 : 25920 ∣ Nat.card (similitudeCentralizer B A))
    (h2 : Nat.card (similitudeCentralizer B A) ∣ 103680) : False := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact Odd.pow (by decide)
  have h2' : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure
    Nat.prime_three (by norm_num) hf hK (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    have hl0 : l ≠ 0 := fun h0 => hd0 (by rw [← hl, h0]; ring)
    rcases hε with h1' | h1'
    ·
      obtain ⟨-, haltP, haltM, hndP, hndM, e, -⟩ := hpos h1'
      have hP' := Submodule.one_le_finrank_iff.mpr hP
      have hM' := Submodule.one_le_finrank_iff.mpr hM
      have hAA' : (A : Module.End K V) * (A : Module.End K V) = (l ^ 2) • 1 := by
        rw [hAA, hl]
      have hc : IsCompl (eigenPlus l (A : Module.End K V)) (eigenMinus l (A : Module.End K V)) :=
        isCompl_ker_sub_one_ker_add_one h2' (invSMulOp_mul_self hl0 hAA')
      have hsum := Submodule.finrank_add_eq_of_isCompl hc
      obtain ⟨a, hda, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic _ haltP hndP
      obtain ⟨b, hdb, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic _ haltM hndM
      obtain ⟨eP⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ haltP hndP hda
      obtain ⟨eM⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ haltM hndM hdb
      exact u42_not_classOne (a := a) (b := b) hf hK (by omega) (by omega)
        (fun ha hb => h2f (by omega))
        (e.trans (MulEquiv.prodCongr ((sesqUnitaryIsometryEquiv _).trans eP)
          ((sesqUnitaryIsometryEquiv _).trans eM))) h1 h2
    ·
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1'
      let bP : Module.Basis (Fin r) K (eigenPlus l (A : Module.End K V)) :=
        Module.finBasisOfFinrankEq K _ hdP
      exact u42_not_classTwo hf hK hr h2f
        (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)) h1 h2
  · push Not at hsq
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, hpow, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
    have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
      rw [hcard]
      exact Odd.pow (Odd.pow (by decide))
    have := finite_of_odd_card hEodd
    have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
      CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (A : Module.End K V)
    rcases hε with h1' | h1'
    ·
      obtain ⟨BE, -, hBEalt, hBEnd, hEven, hiff⟩ := hpos h1'
      have hE : Nat.card (scalarSquareField (A : Module.End K V)) = 3 ^ (2 * f) := by
        rw [hcard, ← pow_mul, mul_comm]
      obtain ⟨m, hm⟩ := hEven
      obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp BE hBEalt hBEnd
        (r := m) (by omega)
      exact u42_not_classThree hf hE (by omega) (fun hm1 => h2f (by omega))
        (((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBAlternatingIsometry.isometryGroup BE)
            (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
            (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff)).trans eSp) h1 h2
    ·
      obtain ⟨h, -, hsymm, hsep, hiff⟩ := hneg h1'
      let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
      let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (A : Module.End K V)]
        scalarSquareField (A : Module.End K V) := h
      have hnd' : h'.Nondegenerate :=
        ⟨hsep, fun y hy => hsep y fun x => by
          rw [← hsymm.eq x y]
          exact (congrArg bar (hy x)).trans (map_zero bar)⟩
      exact u42_not_classFour (sigma := sigma) hf hcard (hfinrank ▸ hr)
        (fun hr2 => h2f (by omega)) (hfinrank ▸ rfl) h' hsymm hnd' (fun z => hpow z)
        ((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
            (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
            (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff)) h1 h2

section SpInner

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude)
open Matrix

theorem u42_sp_inner_false {r f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f) (h2f : r = 2 → 2 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ f) (A : gsp r K)
    (hA : orderOf (conjAut r K A) = 2) {J : Subgroup ↥(fixedSubgroup (conjAut r K A))}
    (hJ : U42Hyp (conjAut r K A) J) : False := by
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
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  obtain ⟨h1, h2⟩ := hJ.spCent_constraints (by omega)
  have hcard := Nat.card_congr (spCentEquiv A).toEquiv
  exact u42_inner_false hf hK hr h2f finrank_standard pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA) hAμ
    (hcard ▸ h1) (hcard ▸ h2)

end SpInner

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

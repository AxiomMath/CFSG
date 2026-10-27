module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpSmallOrder

public section

namespace CFSG.ComponentClassification.CatFC.PSpSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBSymplecticB
open LinearMap (BilinForm)
open scoped MatrixGroups

theorem inner_classes {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hdim : finrank K V = 2 * 2) {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w) :
    InnerOut f d μ (similitudeCentralizer B A) := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact Odd.pow (by decide)
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure
    Nat.prime_three (by norm_num) hf hK (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    have hl0 : l ≠ 0 := fun h0 => hd0 (by rw [← hl, h0]; ring)
    rcases hε with h1 | h1
    ·
      obtain ⟨-, haltP, haltM, hndP, hndM, e, -⟩ := hpos h1
      have hP' := Submodule.one_le_finrank_iff.mpr hP
      have hM' := Submodule.one_le_finrank_iff.mpr hM
      have hAA' : (A : Module.End K V) * (A : Module.End K V) = (l ^ 2) • 1 := by
        rw [hAA, hl]
      have hc : IsCompl (eigenPlus l (A : Module.End K V)) (eigenMinus l (A : Module.End K V)) :=
        isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA')
      have hsum := Submodule.finrank_add_eq_of_isCompl hc
      obtain ⟨a, hda, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic _ haltP hndP
      obtain ⟨b, hdb, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic _ haltM hndM
      obtain ⟨eP⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ haltP hndP hda
      obtain ⟨eM⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ haltM hndM hdb
      have hμd : μ = d := by
        rw [div_eq_one_iff_eq hd0] at h1
        exact h1
      have hout := innerOut_one (f := f) hK (a := a) (b := b) (by omega) (by omega) (by omega)
        (e.trans (MulEquiv.prodCongr ((sesqUnitaryIsometryEquiv _).trans eP)
          ((sesqUnitaryIsometryEquiv _).trans eM)))
      exact Or.inl ⟨⟨l, hl⟩, hμd, hout.1, hout.2⟩
    ·
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
      let bP : Module.Basis (Fin 2) K (eigenPlus l (A : Module.End K V)) :=
        Module.finBasisOfFinrankEq K _ hdP
      have hμd : μ = -d := by
        rw [div_eq_iff hd0] at h1
        rw [h1]
        ring
      have hout := innerOut_two (f := f) hK
        (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv))
      exact Or.inr (Or.inl ⟨⟨l, hl⟩, hμd, hout.1, hout.2⟩)
  · push Not at hsq
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, hpow, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
    have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
      rw [hcard]
      exact Odd.pow (Odd.pow (by decide))
    have := finite_of_odd_card hEodd
    have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
      CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (A : Module.End K V)
    rcases hε with h1 | h1
    ·
      obtain ⟨BE, -, hBEalt, hBEnd, hEven, hiff⟩ := hpos h1
      have hE : Nat.card (scalarSquareField (A : Module.End K V)) = 3 ^ (2 * f) := by
        rw [hcard, ← pow_mul, mul_comm]
      obtain ⟨m, hm⟩ := hEven
      obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp BE hBEalt hBEnd
        (r := m) (by omega)
      have hm1 : m = 1 := by omega
      subst hm1
      have hμd : μ = d := by
        rw [div_eq_one_iff_eq hd0] at h1
        exact h1
      have hout := innerOut_three (f := f) hE (((centralizerSimilitudeEquiv B A).symm.trans
        (evaluationIsometryEquiv B A (CatalogueBAlternatingIsometry.isometryGroup BE)
          (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
          (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff)).trans eSp)
      exact Or.inr (Or.inr (Or.inl ⟨hsq, hμd, hout.1, hout.2⟩))
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
      have hμd : μ = -d := by
        rw [div_eq_iff hd0] at h1
        rw [h1]
        ring
      have hout := innerOut_four (f := f) hcard hfinrank h' hsymm hnd' hsigma hne
        (fun z => hpow z) ((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
            (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
            (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff))
      exact Or.inr (Or.inr (Or.inr ⟨hsq, hμd, hout.1, hout.2⟩))

section SpClasses

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude)
open scoped Matrix

theorem inner_classes_sp {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (A : gsp 2 K) (hA : orderOf (conjAut 2 K A) = 2) :
    ∃ c μ : K, c ≠ 0 ∧
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = c • 1 ∧
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = μ • formJ 2 K ∧
      InnerOut f c μ (spCent 2 K A) := by
  have hA1 : conjAut 2 K A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : conjAut 2 K A * conjAut 2 K A = 1 := by
    have h2 := pow_orderOf_eq_one (conjAut 2 K A)
    rw [hA] at h2
    rw [← pow_two]
    exact h2
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin 2 ⊕ Fin 2) K) ≠ Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c :=
    fun c hc => hA1 ((Burgoyne.Sp.conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := (Burgoyne.Sp.conjAut_eq_one_iff (by omega) (A * A)).1
    (by rw [map_mul, hA2])
  set M := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hAA : M * M = (c : K) • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  have hAμ : ∀ v w, pairedSympForm K 2 (((linA A : LinearMap.GeneralLinearGroup K
      (Fin 2 ⊕ Fin 2 → K)) : Module.End K (Fin 2 ⊕ Fin 2 → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)) :
        Module.End K (Fin 2 ⊕ Fin 2 → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K 2 v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  have hcl := inner_classes hf hK finrank_standard pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA) hAμ
  exact ⟨c, multiplierUnit A, c.ne_zero, hAA, multiplierUnit_spec A,
    hcl.of_mulEquiv (spCentEquiv A).symm⟩

end SpClasses

end CFSG.ComponentClassification.CatFC.PSpSmall

module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpInner
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpField

public section

namespace CFSG.ComponentClassification.CatFC.PSpSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBSymplecticB
open LinearMap (BilinForm)
open scoped MatrixGroups

@[expose] def NineOut (G : Type) [Group G] : Prop :=
  PerfectBig3 G ∨ 2 ^ 7 ∣ Nat.card G ∨ ∃ x : G, orderOf x = 16

theorem NineOut.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (h : NineOut G) :
    NineOut G' := by
  rcases h with h | h | ⟨x, hx⟩
  · exact Or.inl (h.of_mulEquiv e)
  · exact Or.inr (Or.inl (by rwa [← Nat.card_congr e.toEquiv]))
  · exact Or.inr (Or.inr ⟨e x, by rw [MulEquiv.orderOf_eq, hx]⟩)

theorem two_pow_seven_dvd_card_of_mulEquiv_GL_two {k : Type} [Field k] [Finite k]
    (hK : Nat.card k = 3 ^ 2) {G : Type} [Group G] (e : G ≃* GL (Fin 2) k) :
    2 ^ 7 ∣ Nat.card G := by
  haveI := Fintype.ofFinite k
  have h9 : Fintype.card k = 9 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, h9]
  simp [Fin.prod_univ_two]

theorem inner_classes_nine {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 2) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (hdim : finrank K V = 2 * 2)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w) :
    NineOut (similitudeCentralizer B A) := by
  have hf : 1 ≤ 2 := by norm_num
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
      obtain ⟨a, hda, -⟩ :=
        CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic _ haltP hndP
      obtain ⟨b, hdb, -⟩ :=
        CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic _ haltM hndM
      obtain ⟨eP⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ haltP hndP hda
      obtain ⟨eM⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ haltM hndM hdb
      have hres := classOne_dichotomy (a := a) (b := b) (r := 2) hf hK (by omega) (by omega)
        (by omega) (e.trans (MulEquiv.prodCongr ((sesqUnitaryIsometryEquiv _).trans eP)
          ((sesqUnitaryIsometryEquiv _).trans eM)))
      rcases hres with hres | ⟨-, hf1⟩
      · exact Or.inl hres
      · omega
    ·
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
      let bP : Module.Basis (Fin 2) K (eigenPlus l (A : Module.End K V)) :=
        Module.finBasisOfFinrankEq K _ hdP
      exact Or.inr (Or.inl (two_pow_seven_dvd_card_of_mulEquiv_GL_two hK
        (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv))))
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
      have hE : Nat.card (scalarSquareField (A : Module.End K V)) = 3 ^ (2 * 2) := by
        rw [hcard]
        norm_num
      obtain ⟨m, hm⟩ := hEven
      obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp BE hBEalt hBEnd
        (r := m) (by omega)
      have hm1 : m = 1 := by omega
      subst hm1
      have hres := classThree_dichotomy (f := 2) hf hE (by omega)
        (((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBAlternatingIsometry.isometryGroup BE)
            (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
            (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff)).trans eSp)
      rcases hres with hres | ⟨-, hf1⟩
      · exact Or.inl hres
      · omega
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
      exact Or.inr (Or.inr (exists_orderOf_eq_sixteen_of_mulEquiv hcard hfinrank h' hsymm hnd'
        hsigma hne ((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
            (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
            (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff))))

section SpClasses

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude)
open scoped Matrix

theorem inner_classes_sp_nine {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 2)
    (A : gsp 2 K) (hA : orderOf (conjAut 2 K A) = 2) : NineOut (spCent 2 K A) := by
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
  have hcl := inner_classes_nine hK finrank_standard pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA) hAμ
  exact hcl.of_mulEquiv (spCentEquiv A).symm

theorem psp_nine_exclusion_conjAut {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 2)
    (A : gsp 2 K) (hA : orderOf (conjAut 2 K A) = 2)
    {D : Subgroup ↥(fixedSubgroup (conjAut 2 K A))} (h : A6Hyp (conjAut 2 K A) D) :
    (∃ x : ↥(fixedSubgroup (conjAut 2 K A)), orderOf x = 8) ∨
      2 ^ 6 ∣ Nat.card ↥(fixedSubgroup (conjAut 2 K A)) := by
  have hker := card_ker_spCentFix_le (by norm_num : 1 ≤ 2) A
  rcases inner_classes_sp_nine hK A hA with hP | h7 | ⟨x, hx⟩
  · exact (h.false_of_perfectBig3 (by norm_num) hP).elim
  · exact Or.inr (two_pow_dvd_card_of_card_ker_le_two (spCentFix A) hker (k := 6) h7)
  · exact Or.inl (exists_orderOf_eq_eight_of_orderOf_eq_sixteen (spCentFix A) hker hx)

end SpClasses

theorem psp_nine_exclusion {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 2)
    {σ : MulAut (StatedProj (StatedSp 2 K))} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (h : A6Hyp σ D) :
    (∃ x : ↥(fixedSubgroup σ), orderOf x = 8) ∨ 2 ^ 6 ∣ Nat.card ↥(fixedSubgroup σ) := by
  have hf1 : 1 ≤ 2 := by norm_num
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf1 hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have hσ2 : σ * σ = 1 := by
    have h2 := pow_orderOf_eq_one σ
    rw [hσ] at h2
    rw [← pow_two]
    exact h2
  have hσ1 : σ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨A, τ, hAσ, hτ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar (le_refl 2)).2.2 σ hσ2 hσ1
  by_cases hτ : τ = 1
  · subst hτ
    rw [map_one, mul_one] at hAσ
    subst hAσ
    exact psp_nine_exclusion_conjAut hK A hσ h
  · exact (a6_field_false (le_refl 2) hf1 hK A τ hAσ hτ2 hτ d hd h).elim

end CFSG.ComponentClassification.CatFC.PSpSmall

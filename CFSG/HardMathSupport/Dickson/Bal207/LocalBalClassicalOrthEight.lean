module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalD4Eight
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThree
import CFSG.GF2Type.Smith1979.CaseIIRderFix
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Neg
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaPlus

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthRow

open Module CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.Classical.SteinbergBY CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross CFSG.GroupTheory.WeirSylow
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')

section Fixed

theorem exists_orderOf_three_fixed {P : Type*} [Group P] [Finite P] (h3 : 3 ∣ Nat.card P)
    {a : MulAut P} (ha : a ^ 3 = 1) : ∃ t : P, orderOf t = 3 ∧ a t = t := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hiter : ∀ t : P, a (a (a t)) = t := fun t => by
    have := congrArg (fun g : MulAut P => g t) ha
    simpa [pow_succ, MulAut.mul_apply] using this
  have hf : (a : P → P)^[3] = id := by
    funext t
    simpa using hiter t
  have hmod := CFSG.GF2Type.Smith1979.Case2.card_fixed_modEq (a : P → P) hf
  have hset : ((fixSub a : Subgroup P) : Set P) = Function.fixedPoints (a : P → P) := by
    ext t
    simp [mem_fixSub, Function.IsFixedPt]
  have hcard : Nat.card (fixSub a) = (Function.fixedPoints (a : P → P)).ncard := by
    rw [← hset]
    exact Nat.card_coe_set_eq _
  have h3' : 3 ∣ Nat.card (fixSub a) := by
    rw [hcard]
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3))
  haveI : Finite (fixSub a) := inferInstance
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := fixSub a) 3 h3'
  exact ⟨(t : P), by rw [Subgroup.orderOf_coe, ht], mem_fixSub.1 t.2⟩

end Fixed

section Order

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem three_dvd_natCard_projOrthDerived (hK : Nat.card K = 8)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {m : ℕ}
    (hdim : finrank K V = 2 * (m + 1)) (hm : 1 ≤ m ∨ ¬ IsPlusType Q) :
    3 ∣ Nat.card (ProjOrthDerived Q) := by
  classical
  have := Bal207.OrthEight.charP_two hK
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) := Subtype.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := Bal207.OrthEight.three_dvd_natCard_orthogonalGroup hK hQ hdim hm
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := TauCeti.QuadraticMap.orthogonalGroup Q)
    3 h3
  obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hgΩ : (g : V ≃ₗ[K] V) ∈ orthDerived Q :=
    hodd (g : V ≃ₗ[K] V) g.2 (by rw [Subgroup.orderOf_coe, hg]; decide)
  have hinj : Function.Injective (piOrth Q) := piOrth_injective hQ
  have hord : orderOf (piOrth Q ⟨(g : V ≃ₗ[K] V), hgΩ⟩) = 3 := by
    rw [orderOf_injective (piOrth Q) hinj, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hg]
  rw [← hord]
  exact orderOf_dvd_natCard _

end Order

section Assembly

variable {K : Type} [Field K] [Finite K]

theorem isLocallyBalancedAbs_three_one_matrix_eight (hK : Nat.card K = 8) {d : ℕ} (hd : 0 < d)
    {Q : QuadraticForm K (Fin d → K)} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K (Fin d → K) / 2))
    (h3 : 3 ∣ Nat.card (ProjOrthDerived Q)) (htop : matrixProjectiveImage Q = ⊤)
    (hout : ∀ x : MulAut (matrixProjectiveDerived Q), x ^ 3 = 1 →
      x ∉ innerAut (matrixProjectiveDerived Q) → ∀ y ∈ innerAut (matrixProjectiveDerived Q),
        y ≠ 1 → y ^ 3 = 1 → y * x = x * y → FieldCoreAt 3 x) :
    IsLocallyBalancedAbs 3 1 (matrixProjectiveDerived Q) := by
  classical
  have := Bal207.OrthEight.charP_two hK
  have hinj := KCOrthogonalD4.conj_injective_matrixProjectiveDerived Q hd hQ hT
  set φ := coordBridge Q hd with hφ
  haveI : Finite (ProjOrthDerived Q) := Finite.of_surjective
    (QuotientGroup.mk : orthDerived Q → ProjOrthDerived Q) QuotientGroup.mk_surjective
  haveI : Finite (matrixProjectiveDerived Q) := Finite.of_equiv _ φ.symm.toEquiv
  refine isLocallyBalancedAbs_one_of_good Nat.prime_three hinj fun x hx3 hx1 => ?_
  by_cases hxi : x ∈ innerAut (matrixProjectiveDerived Q)
  · right
    obtain ⟨y, rfl⟩ := hxi
    have hy : orderOf (φ y) = 3 := by
      rw [MulEquiv.orderOf_eq, ← orderOf_injective _ hinj y]
      exact orderOf_eq_prime hx3 hx1
    have hE : ∀ g : MulAut (ProjOrthDerived Q), Nat.Coprime 3 (orderOf g) →
        ∃ β : MulAut (ProjOrthDerived Q),
          MulAut.congr φ.symm (β⁻¹ * g * β) ∈ matrixProjectiveImage Q :=
      fun g _ => ⟨1, by rw [htop]; exact Subgroup.mem_top _⟩
    have h := coreFreeAt_congr φ.symm
      (Bal207.OrthEight.coreFreeAt_conj_projOrthDerived hK hd hQ hT hpar hE hy)
    have hc : MulAut.congr φ.symm (MulAut.conj (φ y)) = MulAut.conj y :=
      MulEquiv.ext fun t => by simp [MulAut.congr_apply, MulAut.conj_apply]
    rwa [hc] at h
  · left
    have h3' : 3 ∣ Nat.card (matrixProjectiveDerived Q) := by
      rw [Nat.card_congr φ.toEquiv]
      exact h3
    obtain ⟨t, ht3, htx⟩ := exists_orderOf_three_fixed h3' hx3
    refine hout x hx3 hxi (MulAut.conj t) ⟨t, rfl⟩ (fun h1 => ?_) ?_
      (conj_commute_of_mem_fixSub (mem_fixSub.2 htx)).symm
    · have := hinj (h1.trans (map_one _).symm)
      rw [this, orderOf_one] at ht3
      exact absurd ht3 (by norm_num)
    · rw [← map_pow, ← ht3, pow_orderOf_eq_one, map_one]

end Assembly

section Descent

theorem fieldCoreAt_three_of_outer_plus {G : Type} [Group G] {n ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n ℓ f) (hn5 : 5 ≤ n) (hpℓ : 3 ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    [Finite (matrixProjectiveDerived (coordinateQuadPlus n K))]
    (hinj : Function.Injective
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (ha3 : a ^ 3 = 1)
    (ha : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
    {y : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (hy : y ∈ innerAut (matrixProjectiveDerived (coordinateQuadPlus n K))) (hy1 : y ≠ 1)
    (hyp : y ^ 3 = 1) (hcomm : y * a = a * y) : FieldCoreAt 3 a := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f h K hK e
  have htop := matrixProjectiveImage_eq_top_plus K n hn5
  have haE : a ∈ matrixProjectiveImage (coordinateQuadPlus n K) := htop ▸ Subgroup.mem_top a
  have haD : a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range :=
    fun hD => ha (mem_inner_of_mem_D_three hg hD ha3)
  have hap : orderOf a = 3 := orderOf_eq_prime ha3 fun h1 => ha (h1 ▸ one_mem _)
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f 3 h hp hp2 K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  refine fieldCoreAt_of_descent hp hp2 hinj Θ (a := a)
    (δ := matrixProjectiveConjugationHom _ g') ?_
    (fixedData_plus_three hCM.1 hpℓ hpf K hK U.val.right hord' hcard' g' hg'l hg'r) hy hy1 hyp
    hcomm
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem fieldCoreAt_three_of_outer_minus {G : Type} [Group G] {n ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n ℓ f) (hn5 : 5 ≤ n) (hpℓ : 3 ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) (hn : 1 ≤ n)
    [Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))]
    (hinj : Function.Injective
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus n K hn b c) →*
        MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))} (ha3 : a ^ 3 = 1)
    (ha : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)))
    {y : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))}
    (hy : y ∈ innerAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) (hy1 : y ≠ 1)
    (hyp : y ^ 3 = 1) (hcomm : y * a = a * y) : FieldCoreAt 3 a := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f h hn K hK b c hirr e
  have htop := matrixProjectiveImage_eq_top_minus K n (by omega) b c hirr
  have haE : a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c) :=
    htop ▸ Subgroup.mem_top a
  have haD : a ∉ (linearConjugationHom (coordinateQuadMinus n K hn b c)).range :=
    fun hD => ha (mem_inner_of_mem_D_three hg hD ha3)
  have hap : orderOf a = 3 := orderOf_eq_prime ha3 fun h1 => ha (h1 ▸ one_mem _)
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f 3 h hp hp2 hn K hK b c hirr e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  refine fieldCoreAt_of_descent hp hp2 hinj Θ (a := a)
    (δ := matrixProjectiveConjugationHom _ g') ?_
    (fixedData_minus_three hCM.1 hpℓ hpf hn K hK U.val.right hord' hcard' b' c' hirr' g' hg'l
      hg'r) hy hy1 hyp hcomm
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

end Descent

section Models

theorem isLocallyBalancedAbs_three_one_plus_eight {G : Type} [Group G] {n : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n 2 3) (hn : 6 ≤ n) (he : Even n) :
    IsLocallyBalancedAbs 3 1 G := by
  classical
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  refine IsLocallyBalancedAbs.of_mulEquiv (coordinatePlusWitnessEquiv K e) ?_
  have hd : 0 < 2 * n := by omega
  have hinj := KCOrthogonalD4.conj_injective_matrixProjectiveDerived _ hd hnd hT
  have hpar : IsPlusType (coordinateQuadPlus n K) ↔ Even (finrank K (Fin (2 * n) → K) / 2) :=
    iff_of_true (CFSG.ComponentClassification.CatFC.omegaPlus_isPlusType n K)
      (by rw [Module.finrank_fin_fun, Nat.mul_div_cancel_left n (by norm_num)]; exact he)
  have h3 : 3 ∣ Nat.card (ProjOrthDerived (coordinateQuadPlus n K)) :=
    three_dvd_natCard_projOrthDerived hK8 hnd hT (m := n - 1)
      (by rw [Module.finrank_fin_fun]; omega) (Or.inl (by omega))
  refine isLocallyBalancedAbs_three_one_matrix_eight hK8 hd hnd hT hpar h3
    (matrixProjectiveImage_eq_top_plus K n (by omega))
    fun x hx3 hxi y hy hy1 hyp hcomm => ?_
  exact fieldCoreAt_three_of_outer_plus h (by omega) (by norm_num) K hK e hinj hx3 hxi hy hy1
    hyp hcomm

theorem isLocallyBalancedAbs_three_one_minus_eight {G : Type} [Group G] {n : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n 2 3) (hn : 5 ≤ n) (ho : ¬ Even n) :
    IsLocallyBalancedAbs 3 1 G := by
  classical
  have h0 := h
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  refine IsLocallyBalancedAbs.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e) ?_
  have hd : 0 < 2 * n := by omega
  have hinj := KCOrthogonalD4.conj_injective_matrixProjectiveDerived _ hd hnd hT
  have hminus :=
    CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus
      (K := K) n hn1 hirr
  have hpar : IsPlusType (coordinateQuadMinus n K hn1 b c) ↔
      Even (finrank K (Fin (2 * n) → K) / 2) :=
    iff_of_false hminus
      (by rw [Module.finrank_fin_fun, Nat.mul_div_cancel_left n (by norm_num)]; exact ho)
  have h3 : 3 ∣ Nat.card (ProjOrthDerived (coordinateQuadMinus n K hn1 b c)) :=
    three_dvd_natCard_projOrthDerived hK8 hnd hT (m := n - 1)
      (by rw [Module.finrank_fin_fun]; omega) (Or.inl (by omega))
  refine isLocallyBalancedAbs_three_one_matrix_eight hK8 hd hnd hT hpar h3
    (matrixProjectiveImage_eq_top_minus K n (by omega) b c hirr)
    fun x hx3 hxi y hy hy1 hyp hcomm => ?_
  exact fieldCoreAt_three_of_outer_minus h (by omega) (by norm_num) K hK b c hirr e hn1 hinj hx3
    hxi hy hy1 hyp hcomm

theorem isLocallyBalancedAbs_three_one_catD_eight (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D n q).Valid) (hn : 6 ≤ n) (he : Even n) (hp : q.p = 2)
    (hq : q.exponent = 3) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD n q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group)
  rw [hp, hq] at hm
  exact isLocallyBalancedAbs_three_one_plus_eight hm hn he

theorem isLocallyBalancedAbs_three_one_cattwistedD_eight (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD n q).Valid) (hn : 5 ≤ n) (ho : ¬ Even n)
    (hp : q.p = 2) (hq : q.exponent = 3) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD n q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group)
  rw [hp, hq] at hm
  exact isLocallyBalancedAbs_three_one_minus_eight hm hn ho

end Models

end CFSG.HardMathSupport.Dickson.Bal207.OrthRow

end

module

public import CFSG.GH74.GLS.IVK.Lifted.FAutBasic
public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_toGL toGL_field_map)
open CFSG.GH74.GLS.Stage1.Thm2.Recip (isPComponent_top innOf)
open CFSG.GH74.GLS.Stage1.Thm3.Sec5 (fixedSubgroup_congr hasSolvableTwoComponentSL23_congr)
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Mat

variable {F : Type} [Field F]

theorem matrix_two_eq_smul_add (x y a b c d g1 g2 g3 g4 : F) (ha : a = x + y * g1) (hb : b = y * g2)
    (hc : c = y * g3) (hd : d = x + y * g4) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) =
      x • (1 : Matrix (Fin 2) (Fin 2) F) + y • (!![g1, g2; g3, g4] : Matrix (Fin 2) (Fin 2) F) := by
  subst ha hb hc hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_eq_smul_add_of_commute (G : Matrix (Fin 2) (Fin 2) F)
    (hG : ∀ c : F, G ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M * G = G * M) :
    ∃ x y : F, M = x • (1 : Matrix (Fin 2) (Fin 2) F) + y • G := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : F, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  obtain ⟨g1, g2, g3, g4, rfl⟩ : ∃ g1 g2 g3 g4 : F, G = !![g1, g2; g3, g4] :=
    ⟨G 0 0, G 0 1, G 1 0, G 1 1, Matrix.eta_fin_two G⟩
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases h2 : g2 = 0
  · by_cases h3 : g3 = 0
    · by_cases h14 : g1 = g4
      · exfalso
        apply hG g1
        subst h2 h3 h14
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      · have hd : g1 - g4 ≠ 0 := sub_ne_zero.2 h14
        subst h2 h3
        have hb : b = 0 := by
          have : b * (g4 - g1) = 0 := by linear_combination e01
          exact (mul_eq_zero.1 this).resolve_right (by intro h; apply hd; linear_combination -h)
        have hc : c = 0 := by
          have : c * (g1 - g4) = 0 := by linear_combination e10
          exact (mul_eq_zero.1 this).resolve_right hd
        subst hb hc
        refine ⟨a - (a - d) / (g1 - g4) * g1, (a - d) / (g1 - g4), ?_⟩
        apply matrix_two_eq_smul_add
        · ring
        · simp
        · simp
        · field_simp
          ring
    · subst h2
      have hb : b = 0 := by
        have : b * g3 = 0 := by linear_combination e00
        exact (mul_eq_zero.1 this).resolve_right h3
      subst hb
      refine ⟨a - c / g3 * g1, c / g3, ?_⟩
      apply matrix_two_eq_smul_add
      · ring
      · simp
      · field_simp
      · field_simp
        linear_combination e10
  · refine ⟨a - b / g2 * g1, b / g2, ?_⟩
    apply matrix_two_eq_smul_add
    · ring
    · field_simp
    · field_simp
      linear_combination -e00
    · field_simp
      linear_combination -e01

theorem commute_of_commute_nonscalar (G : Matrix (Fin 2) (Fin 2) F)
    (hG : ∀ c : F, G ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    {M N : Matrix (Fin 2) (Fin 2) F} (hM : M * G = G * M) (hN : N * G = G * N) : M * N = N * M := by
  obtain ⟨x₁, y₁, rfl⟩ := exists_eq_smul_add_of_commute G hG M hM
  obtain ⟨x₂, y₂, rfl⟩ := exists_eq_smul_add_of_commute G hG N hN
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
  rw [mul_comm x₂ x₁, mul_comm y₂ x₁, mul_comm x₂ y₁, mul_comm y₂ y₁]
  abel

end Mat

section Gamma

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def gammaOf (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    MulAut (SpecialLinearGroup (Fin 2) F) →* PGammaL2 F :=
  (thetaEquiv hodd h3).symm.toMonoidHom.comp psl2AutHom

theorem thetaEquiv_gammaOf (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    thetaEquiv hodd h3 (gammaOf hodd h3 α) = psl2MulAutOf α :=
  (thetaEquiv hodd h3).apply_symm_apply _

theorem exists_rep (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    ∃ G : GL (Fin 2) F, ∀ b : SpecialLinearGroup (Fin 2) F, SpecialLinearGroup.toGL (α b) =
      G * GeneralLinearGroup.map ((gammaOf hodd h3 α).right : F →+* F) (SpecialLinearGroup.toGL b) * G⁻¹ := by
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective (gammaOf hodd h3 α).left
  exact ⟨G, semilinear_of_pGammaL2 hodd h3 α (gammaOf hodd h3 α) (thetaEquiv_gammaOf hodd h3 α) G hG⟩

theorem gammaOf_conj_right (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (s : SpecialLinearGroup (Fin 2) F) : (gammaOf hodd h3 (MulAut.conj s)).right = 1 := by
  have h : gammaOf hodd h3 (MulAut.conj s) = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk' _ s)) := by
    apply (thetaEquiv hodd h3).injective
    rw [thetaEquiv_gammaOf, psl2MulAutOf_conj hodd h3, thetaEquiv_inl]
  rw [h]
  rfl

theorem gammaOf_mul_right (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α β : MulAut (SpecialLinearGroup (Fin 2) F)) :
    (gammaOf hodd h3 (α * β)).right = (gammaOf hodd h3 α).right * (gammaOf hodd h3 β).right := by
  rw [map_mul]
  rfl

theorem eq_slConjugation_of_right_eq_one (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (h1 : (gammaOf hodd h3 α).right = 1) :
    ∃ G : GL (Fin 2) F, α = slConjugation F G := by
  obtain ⟨G, hG⟩ := exists_rep hodd h3 α
  refine ⟨G, ?_⟩
  apply MulEquiv.ext
  intro b
  apply SpecialLinearGroup.toGL_injective
  rw [hG b, slConjugation_toGL, h1]
  have : GeneralLinearGroup.map (((1 : F ≃+* F)) : F →+* F) (SpecialLinearGroup.toGL b) =
      SpecialLinearGroup.toGL b := glMap_one _
  rw [this]

end Gamma

section FieldAut

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def slFieldAut (σ : F ≃+* F) : MulAut (SpecialLinearGroup (Fin 2) F) where
  toFun := SpecialLinearGroup.map σ.toRingHom
  invFun := SpecialLinearGroup.map σ.symm.toRingHom
  left_inv X := by
    apply SpecialLinearGroup.toGL_injective
    rw [toGL_field_map, toGL_field_map]
    apply GeneralLinearGroup.ext
    intro i j
    simp [GeneralLinearGroup.map_apply]
  right_inv X := by
    apply SpecialLinearGroup.toGL_injective
    rw [toGL_field_map, toGL_field_map]
    apply GeneralLinearGroup.ext
    intro i j
    simp [GeneralLinearGroup.map_apply]
  map_mul' := map_mul _

omit [Finite F] in
theorem slFieldAut_apply (σ : F ≃+* F) (b : SpecialLinearGroup (Fin 2) F) :
    slFieldAut σ b = SpecialLinearGroup.map σ.toRingHom b := rfl

omit [Finite F] in
theorem mem_fixedSubgroup_slFieldAut (σ : F ≃+* F) (b : SpecialLinearGroup (Fin 2) F) :
    b ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slFieldAut σ) ↔ ∀ i j, σ (b i j) = b i j := by
  show slFieldAut σ b = b ↔ _
  constructor
  · intro h i j
    have := congrArg (fun S : SpecialLinearGroup (Fin 2) F => (S : Matrix (Fin 2) (Fin 2) F) i j) h
    exact this
  · intro h
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact h i j

omit [Finite F] in
theorem map_subtype_injective (σ : F ≃+* F) :
    Function.Injective (SpecialLinearGroup.map (fixedField σ).subtype :
      SpecialLinearGroup (Fin 2) (fixedField σ) →* SpecialLinearGroup (Fin 2) F) := by
  intro M N h
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => Subtype.ext ?_
  exact congrArg (fun S : SpecialLinearGroup (Fin 2) F => (S : Matrix (Fin 2) (Fin 2) F) i j) h

omit [Finite F] in
theorem range_map_subtype (σ : F ≃+* F) :
    (SpecialLinearGroup.map (fixedField σ).subtype :
      SpecialLinearGroup (Fin 2) (fixedField σ) →* SpecialLinearGroup (Fin 2) F).range =
      fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slFieldAut σ) := by
  ext X
  constructor
  · rintro ⟨M, rfl⟩
    rw [mem_fixedSubgroup_slFieldAut]
    intro i j
    exact fixedField_apply σ (M i j)
  · intro hX
    rw [mem_fixedSubgroup_slFieldAut] at hX
    exact exists_specialLinear_map_eq σ X hX

@[expose] noncomputable def fixedEquivSL (σ : F ≃+* F) :
    ↥(fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slFieldAut σ)) ≃*
      SpecialLinearGroup (Fin 2) (fixedField σ) :=
  (MulEquiv.subgroupCongr (range_map_subtype σ).symm).trans
    (MonoidHom.ofInjective (map_subtype_injective σ)).symm

end FieldAut

section PCoreSL

theorem isQuasisimple_sl2' {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) K) := by
  have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4
  have hsimple : IsSimpleGroup (SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (SpecialLinearGroup (Fin 2) K)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator (SpecialLinearGroup (Fin 2) K) ≤
      Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hab ((QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K))) x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne
    (SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) K))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem even_card_sl2 {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    Even (Nat.card (SpecialLinearGroup (Fin 2) K)) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  apply Even.mul_left
  have h1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Finite.card_pos
  rw [Nat.even_sub h1]
  simp [Nat.even_pow, Nat.not_even_iff_odd.2 hodd]

theorem sq_eq_one_of_mem_center_sl2 {K : Type} [Field K] {n : SpecialLinearGroup (Fin 2) K}
    (hn : n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K)) : n * n = 1 := by
  obtain ⟨r, hr, hnr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hn
  simp only [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hnr, ← map_mul, ← sq, hr, map_one]
  rfl

end PCoreSL

section PCoreSL2

theorem pPrimeCore_two_sl2_five {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) : pPrimeCore 2 (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have : N.Normal := hN
  obtain ⟨hperf, hsimple, -⟩ := isQuasisimple_sl2' (K := K) (by omega)
  set Z := Subgroup.center (SpecialLinearGroup (Fin 2) K) with hZ
  have hN' : (N.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective Z)
  rcases (have := hN'; hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z))) with h0 | h1
  · rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have hnZ : n ∈ Z := by
      have : QuotientGroup.mk' Z n ∈ N.map (QuotientGroup.mk' Z) := ⟨n, hn, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff n).1 this
    have hsq := sq_eq_one_of_mem_center_sl2 hnZ
    have h2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have h3 : orderOf n ∣ Nat.card N := by
      have := Subgroup.orderOf_dvd_natCard N hn
      exact this
    have h4 : orderOf n ∣ Nat.gcd 2 (Nat.card N) := Nat.dvd_gcd h2 h3
    rw [hcop] at h4
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  · exfalso
    have hcomm : commutator (SpecialLinearGroup (Fin 2) K) ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      have hx : QuotientGroup.mk' Z x ∈ N.map (QuotientGroup.mk' Z) := by rw [h1]; trivial
      obtain ⟨n₁, hn₁, hxn⟩ := hx
      have hz₁ : n₁⁻¹ * x ∈ Z := by
        rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv, hxn, inv_mul_cancel]
      have hcm := Subgroup.mem_center_iff.1 hz₁ y
      have hy : (n₁⁻¹ * x) * y * (n₁⁻¹ * x)⁻¹ = y := by
        rw [← hcm, mul_inv_cancel_right]
      have e : ⁅x, y⁆ = n₁ * (y * n₁⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]
        calc x * y * x⁻¹ * y⁻¹ = n₁ * ((n₁⁻¹ * x) * y * (n₁⁻¹ * x)⁻¹) * n₁⁻¹ * y⁻¹ := by group
          _ = n₁ * y * n₁⁻¹ * y⁻¹ := by rw [hy]
          _ = n₁ * (y * n₁⁻¹ * y⁻¹) := by group
      rw [e]
      exact N.mul_mem hn₁ (hN.conj_mem _ (N.inv_mem hn₁) y)
    have hNtop : N = ⊤ := by
      rw [eq_top_iff]
      have := Group.isPerfect_def.mp hperf
      rw [← this]
      exact hcomm
    have h2 : 2 ∣ Nat.card N := by
      rw [hNtop, Subgroup.card_top]
      exact even_iff_two_dvd.1 (even_card_sl2 hodd)
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)

theorem exists_smul_one_of_commute_uv {F : Type} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hu : M * !![1, 1; 0, 1] = !![1, 1; 0, 1] * M) (hv : M * !![1, 0; 1, 1] = !![1, 0; 1, 1] * M) :
    ∃ μ : F, M = μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.eta_fin_two M] at hu hv
  simp only [Matrix.mul_fin_two] at hu hv
  have a1 := congrFun (congrFun hu 0) 0
  have a2 := congrFun (congrFun hu 0) 1
  have a3 := congrFun (congrFun hv 0) 0
  simp at a1 a2 a3
  have c11 : M 1 1 = M 0 0 := by linear_combination -a2
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a1, a3, c11]

theorem pPrimeCore_two_sl2_three {K : Type} [Field K] [Finite K] (h3 : Nat.card K = 3) :
    pPrimeCore 2 (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have h30 : (3 : K) = 0 := by
    have := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, h3] at this
    exact_mod_cast this
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have : N.Normal := hN
  by_contra hNne
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) K) = 24 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h3]
    norm_num
  have hdvd : Nat.card N ∣ 24 := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have hN3 : Nat.card N = 3 := by
    have h8 : Nat.Coprime (Nat.card N) 8 := by
      have h' : Nat.Coprime (Nat.card N) (2 ^ 3) := Nat.Coprime.pow_right 3 hcop.symm
      simpa using h'
    have : Nat.card N ∣ 3 := h8.dvd_of_dvd_mul_right (by simpa using hdvd : Nat.card N ∣ 3 * 8)
    rcases (Nat.dvd_prime Nat.prime_three).1 this with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hNne
    · exact h
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hNne (Subgroup.eq_bot_iff_forall N |>.2 hcon)
  have hordn : orderOf n = 3 := by
    have hd : orderOf n ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard N hnN
      rwa [hN3] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hn1
    · exact h
  have hn3 : n * n * n = 1 := by
    have := pow_orderOf_eq_one n
    rw [hordn] at this
    simpa [pow_succ, mul_assoc] using this
  have hNz : Subgroup.zpowers n = N := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hnN)
    rw [Nat.card_zpowers, hordn, hN3]
  have hform : ∀ m ∈ N, m = 1 ∨ m = n ∨ m = n * n := by
    intro m hm
    rw [← hNz] at hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    have hk' : n ^ (k % 3) = m := by
      rw [← hk]
      have := zpow_mod_orderOf n k
      rw [hordn] at this
      simpa using this
    have h3le : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h3le with h | h | h
    · left
      rw [h] at hk'
      simpa using hk'.symm
    · right; left
      rw [h] at hk'
      simpa using hk'.symm
    · right; right
      rw [h] at hk'
      rw [← hk']
      simp [sq]
  have hcommx : ∀ x : SpecialLinearGroup (Fin 2) K, x * x * x = 1 → n * x = x * n := by
    intro x hx3
    have hm : x * n * x⁻¹ ∈ N := hN.conj_mem n hnN x
    rcases hform _ hm with h | h | h
    · exfalso
      apply hn1
      have : n = x⁻¹ * (x * n * x⁻¹) * x := by group
      rw [this, h]
      group
    · calc n * x = (x * n * x⁻¹) * x := by rw [h]
        _ = x * n := by group
    · exfalso
      apply hn1
      have e1 : x * (n * n) * x⁻¹ = n := by
        calc x * (n * n) * x⁻¹ = (x * n * x⁻¹) * (x * n * x⁻¹) := by group
          _ = n * n * (n * n) := by rw [h]
          _ = n := by
            calc n * n * (n * n) = n * (n * n * n) := by group
              _ = n := by rw [hn3, mul_one]
      have e2 : x * (x * n * x⁻¹) * x⁻¹ = n := by rw [h]; exact e1
      have e3 : n = n * n := by
        calc n = (x * x * x) * n * (x * x * x)⁻¹ := by rw [hx3]; group
          _ = x * (x * (x * n * x⁻¹) * x⁻¹) * x⁻¹ := by group
          _ = x * n * x⁻¹ := by rw [e2]
          _ = n * n := h
      exact mul_left_cancel (a := n) (show n * n = n * 1 by rw [← e3, mul_one])
  let u : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let v : SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have h30' : (1 : K) + 1 + 1 = 0 := by linear_combination h30
  have hu3 : u * u * u = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h30'
  have hv3 : v * v * v = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h30'
  have hnu := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
    (hcommx u hu3)
  have hnv := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
    (hcommx v hv3)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hnu hnv
  obtain ⟨μ, hμ⟩ := exists_smul_one_of_commute_uv (n : Matrix (Fin 2) (Fin 2) K) hnu hnv
  have hdet : μ * μ = 1 := by
    have := n.det_coe
    rw [hμ, Matrix.det_smul, Matrix.det_one] at this
    simpa [sq] using this
  have hnn : n * n = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hμ, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
      hdet, one_smul]
    rfl
  apply hn1
  calc n = n * (n * n) := by rw [hnn, mul_one]
    _ = 1 := by rw [← mul_assoc]; exact hn3

end PCoreSL2

section ClaimA

variable {F : Type} [Field F] [Finite F]

theorem fixedCond_slFieldAut (hodd : Odd (Nat.card F)) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    FixedCond (SpecialLinearGroup (Fin 2) F) (slFieldAut σ) := by
  have hq : Nat.card ↥(fixedField σ) ^ 2 = Nat.card F := by
    simpa [hσ] using fixedField_card_pow σ
  have hq₀odd : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hodd
  have hq₀gt : 1 < Nat.card ↥(fixedField σ) := one_lt_card_fixedField σ
  apply fixedCond_of_equiv (slFieldAut σ) (fixedEquivSL σ)
  by_cases h3 : Nat.card ↥(fixedField σ) = 3
  · right
    have hO := pPrimeCore_two_sl2_three (K := fixedField σ) h3
    refine ⟨⊤, Subgroup.IsSubnormal.top, ↥(fixedField σ), inferInstance, inferInstance, h3, ⟨?_⟩⟩
    exact Subgroup.topEquiv.trans
      (((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans
        (specialLinearGroupEquivStatedSL 2 ↥(fixedField σ)))
  · left
    have h5 : 5 ≤ Nat.card ↥(fixedField σ) := by
      obtain ⟨k, hk⟩ := hq₀odd
      omega
    exact ⟨⊤, isPComponent_top (isQuasisimple_sl2' (by omega))
      (pPrimeCore_two_sl2_five hq₀odd h5)⟩

theorem exists_conj_slFieldAut (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα2 : α * α = 1)
    (hσ : (gammaOf hodd h3 α).right ≠ 1) :
    ∃ β : MulAut (SpecialLinearGroup (Fin 2) F),
      β⁻¹ * α * β = slFieldAut (gammaOf hodd h3 α).right := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hγ2 : gammaOf hodd h3 α * gammaOf hodd h3 α = 1 := by
    rw [← map_mul, hα2, map_one]
  have hσσ : (gammaOf hodd h3 α).right * (gammaOf hodd h3 α).right = 1 := by
    have := congrArg SemidirectProduct.right hγ2
    simpa using this
  have hord : orderOf (gammaOf hodd h3 α) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hγ2) (by
    intro h; apply hσ; rw [h]; rfl)
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (gammaOf hodd h3 α) hord hσ
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_surjective C
  have hγ : thetaEquiv hodd h3 (gammaOf hodd h3 α) = psl2MulAutOf α := thetaEquiv_gammaOf hodd h3 α
  obtain ⟨σ, hσdef⟩ : ∃ σ : F ≃+* F, σ = (gammaOf hodd h3 α).right := ⟨_, rfl⟩
  rw [← hσdef] at hC hσ hσσ ⊢
  obtain ⟨α', hα'⟩ : ∃ α' : MulAut (SpecialLinearGroup (Fin 2) F),
      α' = (slConjugation F c)⁻¹ * α * slConjugation F c := ⟨_, rfl⟩
  have hΘ : thetaEquiv hodd h3 (SemidirectProduct.inr σ) = psl2MulAutOf α' := by
    rw [← hC, map_mul, map_mul, map_inv, hγ, hα']
    show _ = (psl2AutHom (F := F)) ((slConjugation F c)⁻¹ * α * slConjugation F c)
    rw [map_mul, map_mul, map_inv]
    change _ = (psl2MulAutOf (slConjugation F c))⁻¹ * psl2MulAutOf α * psl2MulAutOf (slConjugation F c)
    rw [psl2MulAutOf_slConjugation hodd h3 c, hc]
  have hsemi := semilinear_of_pGammaL2 hodd h3 α' (SemidirectProduct.inr σ) hΘ 1 (by simp)
  simp only [SemidirectProduct.right_inr] at hsemi
  refine ⟨slConjugation F c, ?_⟩
  rw [← hα']
  apply MulEquiv.ext
  intro b
  apply SpecialLinearGroup.toGL_injective
  rw [hsemi b]
  show _ = SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom b)
  rw [toGL_field_map]
  simp

theorem fixedCond_of_field_part (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα2 : α * α = 1)
    (hσ : (gammaOf hodd h3 α).right ≠ 1) : FixedCond (SpecialLinearGroup (Fin 2) F) α := by
  obtain ⟨β, hβ⟩ := exists_conj_slFieldAut hodd h3 α hα2 hσ
  have hγ2 : gammaOf hodd h3 α * gammaOf hodd h3 α = 1 := by
    rw [← map_mul, hα2, map_one]
  have hσσ : (gammaOf hodd h3 α).right * (gammaOf hodd h3 α).right = 1 := by
    have := congrArg SemidirectProduct.right hγ2
    simpa using this
  have hord : orderOf (gammaOf hodd h3 α).right = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ
  have hfc := fixedCond_slFieldAut hodd _ hord
  have hαeq : α = MulAut.congr β (slFieldAut (gammaOf hodd h3 α).right) := by
    rw [← hβ]
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  rw [hαeq]
  exact fixedCond_congr β hfc

end ClaimA

section ClaimB

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem comm_of_commute_matrix (G : Matrix (Fin 2) (Fin 2) F)
    (hG : ∀ c : F, G ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) (a b : SpecialLinearGroup (Fin 2) F)
    (ha : (a : Matrix (Fin 2) (Fin 2) F) * G = G * a) (hb : (b : Matrix (Fin 2) (Fin 2) F) * G = G * b) :
    a * b = b * a := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact commute_of_commute_nonscalar G hG ha hb

omit [Finite F] in
theorem fixed_comm_of_slConjugation (G : GL (Fin 2) F) (hne : slConjugation F G ≠ 1) :
    ∀ a ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slConjugation F G),
      ∀ b ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slConjugation F G), a * b = b * a := by
  have hG : ∀ c : F, (G : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro c hc
    apply hne
    apply MulEquiv.ext
    intro b
    apply SpecialLinearGroup.toGL_injective
    rw [slConjugation_toGL]
    have hcm : G * SpecialLinearGroup.toGL b = SpecialLinearGroup.toGL b * G := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hc]
      simp
    rw [hcm]
    group
    rfl
  have hfix : ∀ x ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slConjugation F G),
      (x : Matrix (Fin 2) (Fin 2) F) * G = G * x := by
    intro x hx
    have h1 : slConjugation F G x = x := hx
    have h2 := congrArg SpecialLinearGroup.toGL h1
    rw [slConjugation_toGL] at h2
    have h3 : G * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * G := by
      calc G * SpecialLinearGroup.toGL x = (G * SpecialLinearGroup.toGL x * G⁻¹) * G := by group
        _ = SpecialLinearGroup.toGL x * G := by rw [h2]
    have h4 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h3
    simpa using h4.symm
  intro a ha b hb
  exact comm_of_commute_matrix _ hG a b (hfix a ha) (hfix b hb)

end ClaimB

section QLevel

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q]

omit [Finite F] in
theorem comm_fixed_of_congr (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ : MulAut Q)
    (h : ∀ a ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (MulAut.congr e φ),
      ∀ b ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (MulAut.congr e φ), a * b = b * a) :
    ∀ a ∈ fixedSubgroup Q φ, ∀ b ∈ fixedSubgroup Q φ, a * b = b * a := by
  intro a ha b hb
  have hF := fixedSubgroup_congr e φ
  have ha' : e a ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (MulAut.congr e φ) := by
    rw [hF]; exact Subgroup.mem_map.2 ⟨a, ha, rfl⟩
  have hb' : e b ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (MulAut.congr e φ) := by
    rw [hF]; exact Subgroup.mem_map.2 ⟨b, hb, rfl⟩
  have := h (e a) ha' (e b) hb'
  rw [← map_mul, ← map_mul] at this
  exact e.injective this

omit [Finite F] in
theorem congr_conj (e : Q ≃* SpecialLinearGroup (Fin 2) F) (c : Q) :
    MulAut.congr e (MulAut.conj c) = MulAut.conj (e c) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

omit [Finite F] in
theorem nonscalar_of_not_mem_center (s : SpecialLinearGroup (Fin 2) F)
    (hs : s ∉ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    ∀ c : F, (s : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro c hc
  apply hs
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

omit [Finite F] in
theorem comm_fixed_conj (c : SpecialLinearGroup (Fin 2) F)
    (hc : c ∉ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    ∀ a ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (MulAut.conj c),
      ∀ b ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (MulAut.conj c), a * b = b * a := by
  have hfix : ∀ x ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (MulAut.conj c),
      (x : Matrix (Fin 2) (Fin 2) F) * c = c * x := by
    intro x hx
    have h1 : c * x * c⁻¹ = x := hx
    have h2 : c * x = x * c := by
      calc c * x = (c * x * c⁻¹) * c := by group
        _ = x * c := by rw [h1]
    have h3 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h2
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h3
    exact h3.symm
  intro a ha b hb
  exact comm_of_commute_matrix _ (nonscalar_of_not_mem_center c hc) a b (hfix a ha) (hfix b hb)

omit [Finite F] in
theorem not_fixedCond_conj (e : Q ≃* SpecialLinearGroup (Fin 2) F) (c : Q) (hc : c ∉ Subgroup.center Q) :
    ¬ FixedCond Q (MulAut.conj c) := by
  apply not_fixedCond_of_comm
  apply comm_fixed_of_congr e
  rw [congr_conj]
  apply comm_fixed_conj
  intro hmem
  apply hc
  rw [Subgroup.mem_center_iff] at hmem ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact hmem (e g)

omit [Finite F] in
theorem sq_eq_one_of_fixedCond_inner (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ : MulAut Q)
    (hf : FixedCond Q φ) (c : Q) (hc : φ * φ = MulAut.conj c) : φ * φ = 1 := by
  by_contra hne
  have hcz : c ∉ Subgroup.center Q := by
    intro hcz
    apply hne
    rw [hc]
    ext x
    have := Subgroup.mem_center_iff.1 hcz x
    simp [MulAut.conj_apply]
    rw [← this]
    group
  apply not_fixedCond_conj e c hcz
  have hsub : fixedSubgroup Q φ ≤ fixedSubgroup Q (MulAut.conj c) := by
    intro x hx
    have h1 : φ x = x := hx
    show (MulAut.conj c) x = x
    rw [← hc]
    show φ (φ x) = x
    rw [h1, h1]
  exfalso
  apply not_fixedCond_of_comm φ _ hf
  intro a ha b hb
  have hcomm := (comm_fixed_of_congr e (MulAut.conj c) (by
    rw [congr_conj]; exact comm_fixed_conj _ (by
      intro hmem; apply hcz
      rw [Subgroup.mem_center_iff] at hmem ⊢
      intro g; apply e.injective; rw [map_mul, map_mul]; exact hmem (e g)))) a (hsub ha) b (hsub hb)
  exact hcomm

end QLevel

section InnChar

open CFSG.GH74.GLS.Stage1.Thm2.Recip (innOf)

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q]

theorem psl2AutHom_injective (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    Function.Injective (psl2AutHom (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have hK := isOddPrimePower_card_of_odd hodd
  have hγ : pGammaL2ToMulAutPSL2 F hK h3 (1 : PGammaL2 F) = psl2MulAutOf α := by
    rw [map_one]
    exact hα.symm
  apply MulEquiv.ext
  intro b
  have h1 := semilinear_of_pGammaL2 hodd h3 α 1 hγ 1 (by simp) b
  simp only [inv_one, one_mul, mul_one] at h1
  have h2 : GeneralLinearGroup.map (((1 : PGammaL2 F).right : F ≃+* F) : F →+* F)
      (SpecialLinearGroup.toGL b) = SpecialLinearGroup.toGL b := glMap_one _
  rw [h2] at h1
  show α b = b
  exact SpecialLinearGroup.toGL_injective h1

theorem gammaOf_injective (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    Function.Injective (gammaOf (F := F) hodd h3) := by
  intro α β h
  apply psl2AutHom_injective hodd h3
  have := congrArg (thetaEquiv hodd h3) h
  rw [thetaEquiv_gammaOf, thetaEquiv_gammaOf] at this
  exact this

theorem gammaOf_conj (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (s : SpecialLinearGroup (Fin 2) F) :
    gammaOf hodd h3 (MulAut.conj s) = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk' _ s)) := by
  apply (thetaEquiv hodd h3).injective
  rw [thetaEquiv_gammaOf, psl2MulAutOf_conj hodd h3, thetaEquiv_inl]

theorem mem_inn_iff (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    α ∈ (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range ↔
      (gammaOf hodd h3 α).right = 1 ∧
        (gammaOf hodd h3 α).left ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [gammaOf_conj]
    exact ⟨rfl, ⟨_, rfl⟩⟩
  · rintro ⟨hr, x, hx⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup (Fin 2) F)) x
    refine ⟨s, ?_⟩
    apply gammaOf_injective hodd h3
    rw [gammaOf_conj]
    apply SemidirectProduct.ext
    · exact hx
    · exact hr.symm

theorem inn_of_outer_pair (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α β : MulAut (SpecialLinearGroup (Fin 2) F))
    (hα : α ∉ (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range)
    (hβ : β ∉ (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range)
    (hαr : (gammaOf hodd h3 α).right = 1) (hβr : (gammaOf hodd h3 β).right = 1) :
    α * β⁻¹ ∈ (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range := by
  set R₀ := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hR₀
  have hOPP := isOddPrimePower_card_of_odd hodd
  have hidx : R₀.index = 2 := pgl2_psl2Range_index_eq_two F hOPP
  have hαl : (gammaOf hodd h3 α).left ∉ R₀ := fun h => hα ((mem_inn_iff hodd h3 α).2 ⟨hαr, h⟩)
  have hβl : (gammaOf hodd h3 β).left ∉ R₀ := fun h => hβ ((mem_inn_iff hodd h3 β).2 ⟨hβr, h⟩)
  have hγα : gammaOf hodd h3 α = SemidirectProduct.inl (gammaOf hodd h3 α).left :=
    SemidirectProduct.ext rfl (by simpa using hαr)
  have hγβ : gammaOf hodd h3 β = SemidirectProduct.inl (gammaOf hodd h3 β).left :=
    SemidirectProduct.ext rfl (by simpa using hβr)
  have hprod : gammaOf hodd h3 (α * β⁻¹) = SemidirectProduct.inl
      ((gammaOf hodd h3 α).left * ((gammaOf hodd h3 β).left)⁻¹) := by
    rw [map_mul, map_inv, hγα, hγβ]
    simp
  rw [mem_inn_iff hodd h3, hprod]
  refine ⟨rfl, ?_⟩
  show (gammaOf hodd h3 α).left * ((gammaOf hodd h3 β).left)⁻¹ ∈ R₀
  rw [Subgroup.mul_mem_iff_of_index_two hidx]
  constructor
  · intro h; exact absurd h hαl
  · intro h; exact absurd (R₀.inv_mem_iff.1 h) hβl

end InnChar

section QLevel2

open CFSG.GH74.GLS.Stage1.Thm2.Recip (innOf)

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q]

theorem fixedCond_of_noncomm (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ : MulAut Q) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (hnc : ¬ ∀ a ∈ fixedSubgroup Q φ, ∀ b ∈ fixedSubgroup Q φ, a * b = b * a) : FixedCond Q φ := by
  have hα2 : MulAut.congr e φ * MulAut.congr e φ = 1 := by rw [← map_mul, hφ2, map_one]
  have hα1 : MulAut.congr e φ ≠ 1 := fun h =>
    hφ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  by_cases hσ : (gammaOf hodd h3 (MulAut.congr e φ)).right = 1
  · exfalso
    obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
    apply hnc
    apply comm_fixed_of_congr e φ
    rw [hG]
    exact fixed_comm_of_slConjugation G (hG ▸ hα1)
  · exact fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hα2 hσ)

theorem fixedCond_of_coset (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ ψ : MulAut Q) (hφ2 : φ * φ = 1) (hψ2 : ψ * ψ = 1)
    (hφ1 : φ ≠ 1) (hf : FixedCond Q φ) (hin : ψ * φ⁻¹ ∈ innOf Q) : FixedCond Q ψ := by
  obtain ⟨c, hc⟩ := hin
  have hψ : ψ = MulAut.conj c * φ := by rw [hc]; group
  have hα2 : MulAut.congr e φ * MulAut.congr e φ = 1 := by rw [← map_mul, hφ2, map_one]
  have hα1 : MulAut.congr e φ ≠ 1 := fun h =>
    hφ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hσ1 : (gammaOf hodd h3 (MulAut.congr e φ)).right ≠ 1 := by
    intro hσ
    obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
    apply not_fixedCond_of_comm φ _ hf
    apply comm_fixed_of_congr e φ
    rw [hG]
    exact fixed_comm_of_slConjugation G (hG ▸ hα1)
  have hβ2 : MulAut.congr e ψ * MulAut.congr e ψ = 1 := by rw [← map_mul, hψ2, map_one]
  have hβ : MulAut.congr e ψ = MulAut.conj (e c) * MulAut.congr e φ := by
    rw [hψ, map_mul, congr_conj]
  have hσ2 : (gammaOf hodd h3 (MulAut.congr e ψ)).right ≠ 1 := by
    rw [hβ, gammaOf_mul_right, gammaOf_conj_right, one_mul]
    exact hσ1
  exact fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hβ2 hσ2)

theorem sl_diag (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ ψ : MulAut Q) (hφ2 : φ * φ = 1) (hψ2 : ψ * ψ = 1)
    (hφ : φ ∉ innOf Q) (hψ : ψ ∉ innOf Q) (hφf : ¬ FixedCond Q φ) (hψf : ¬ FixedCond Q ψ) :
    φ * ψ⁻¹ ∈ innOf Q := by
  have hα2 : MulAut.congr e φ * MulAut.congr e φ = 1 := by rw [← map_mul, hφ2, map_one]
  have hβ2 : MulAut.congr e ψ * MulAut.congr e ψ = 1 := by rw [← map_mul, hψ2, map_one]
  have hαr : (gammaOf hodd h3 (MulAut.congr e φ)).right = 1 := by
    by_contra h
    exact hφf (fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hα2 h))
  have hβr : (gammaOf hodd h3 (MulAut.congr e ψ)).right = 1 := by
    by_contra h
    exact hψf (fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hβ2 h))
  have hαin : MulAut.congr e φ ∉
      (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range := by
    rintro ⟨s, hs⟩
    apply hφ
    refine ⟨e.symm s, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, MulEquiv.apply_symm_apply, hs]
  have hβin : MulAut.congr e ψ ∉
      (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range := by
    rintro ⟨s, hs⟩
    apply hψ
    refine ⟨e.symm s, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, MulEquiv.apply_symm_apply, hs]
  obtain ⟨s, hs⟩ := inn_of_outer_pair hodd h3 _ _ hαin hβin hαr hβr
  refine ⟨e.symm s, ?_⟩
  apply (MulAut.congr e).injective
  rw [congr_conj, MulEquiv.apply_symm_apply, hs, map_mul, map_inv]

end QLevel2

end CFSG.GH74.GLS.IVK.Lifted

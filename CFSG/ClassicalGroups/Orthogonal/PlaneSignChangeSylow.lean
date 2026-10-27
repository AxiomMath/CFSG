module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareSignChange
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant

public section

open Module Matrix QuadraticMap

namespace CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow

open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem signEquiv_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h2 : (2 : K) ≠ 0) (c : Basis ι K V) :
    Function.Injective (fun S : Finset ι => signEquiv c S) := by
  intro S T hST
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  have hneg' : (1 : K) ≠ -1 := fun h => hneg h.symm
  apply Finset.ext
  intro i
  have hmat : signDiag (K := K) S = signDiag (K := K) T := by
    apply (Matrix.toLin c c).injective
    have h := congrArg (fun f : V ≃ₗ[K] V => (f : V →ₗ[K] V)) hST
    simpa only [coe_signEquiv] using h
  have hii := congrFun₂ hmat i i
  rw [signDiag_apply, signDiag_apply] at hii
  simp only [if_true] at hii
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;>
    simp [hiS, hiT, hneg, hneg'] at hii ⊢

theorem card_signChangeSubgroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h2 : (2 : K) ≠ 0) (c : Basis ι K V) :
    Nat.card ↥(signChangeSubgroup c) = 2 ^ Fintype.card ι := by
  have hinj : Function.Injective (fun S : Finset ι => signEquiv c S) :=
    signEquiv_injective h2 c
  let e : Finset ι ≃ ↥(signChangeSubgroup c) :=
    { toFun := fun S => ⟨signEquiv c S, signEquiv_mem_signChangeSubgroup c S⟩
      invFun := fun g => Classical.choose g.2
      left_inv := fun S =>
        hinj (Classical.choose_spec (signEquiv_mem_signChangeSubgroup c S)).symm
      right_inv := fun g => by
        apply Subtype.ext
        exact (Classical.choose_spec g.2).symm }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_finset]

theorem signChangeSubgroup_le_orthogonalGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K V) (c : Basis ι K V)
    (hc : ∀ i j, i ≠ j → Q.IsOrtho (c i) (c j)) :
    signChangeSubgroup c ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  intro g hg
  obtain ⟨S, rfl⟩ := hg
  refine (TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar
    (IsSMulRegular.of_ne_zero h2)).2 ?_
  intro x y
  have hS : ∀ i j, Q.polarBilin (c i) (c j) ≠ 0 → (i ∈ S ↔ j ∈ S) := by
    intro i j hne
    have hij : i = j := by
      by_contra h
      exact hne (by
        rw [QuadraticMap.polarBilin_apply_apply]
        exact QuadraticMap.IsOrtho.polar_eq_zero (hc i j h))
    rw [hij]
  simpa only [QuadraticMap.polarBilin_apply_apply] using
    signEquiv_preserves Q.polarBilin c hS x y

theorem isPlusType_iff_isSquare_neg_mul [Invertible (2 : K)]
    (Q : QuadraticForm K V) (c : Basis (Fin 2) K V)
    (hc : ∀ i j, i ≠ j → Q.IsOrtho (c i) (c j))
    (ha : Q (c 0) ≠ 0) (hb : Q (c 1) ≠ 0) :
    CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ IsSquare (-(Q (c 0) * Q (c 1))) := by
  have hExp : ∀ x y : K, Q (x • c 0 + y • c 1) =
      x ^ 2 * Q (c 0) + y ^ 2 * Q (c 1) := by
    intro x y
    rw [QuadraticMap.map_add Q (x • c 0) (y • c 1),
      QuadraticMap.map_smul Q x (c 0), QuadraticMap.map_smul Q y (c 1),
      QuadraticMap.polar_smul_left Q x (c 0) (y • c 1),
      QuadraticMap.polar_smul_right Q y (c 0) (c 1),
      QuadraticMap.IsOrtho.polar_eq_zero (hc 0 1 (by decide))]
    simp only [smul_eq_mul, mul_zero]
    ring
  have hdimV : finrank K V = 2 := by
    rw [Module.finrank_eq_card_basis c, Fintype.card_fin]
  constructor
  · rintro ⟨W, hWdim, hWiso⟩
    have hW1 : finrank K W = 1 := by omega
    have hWne : W ≠ ⊥ := by
      intro hbot
      have : finrank K W = 0 := by rw [hbot, finrank_bot]
      omega
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hvQ : Q v = 0 := hWiso v hvW
    have hv : v = c.repr v 0 • c 0 + c.repr v 1 • c 1 := by
      simpa only [Fin.sum_univ_two] using (c.sum_repr v).symm
    have hzero : (c.repr v 0) ^ 2 * Q (c 0) + (c.repr v 1) ^ 2 * Q (c 1) = 0 := by
      rw [← hExp, ← hv]
      exact hvQ
    have hy : c.repr v 1 ≠ 0 := by
      intro hy
      have hx2 : (c.repr v 0) ^ 2 * Q (c 0) = 0 := by
        simpa [hy] using hzero
      have hx : c.repr v 0 = 0 := by
        exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hx2).resolve_right ha)
      apply hv0
      rw [hv, hx, hy]
      simp
    have hxya : (c.repr v 0) ^ 2 * Q (c 0) = -((c.repr v 1) ^ 2 * Q (c 1)) := by
      linear_combination hzero
    have hxy : (Q (c 0) * c.repr v 0) ^ 2 =
        -(Q (c 0) * Q (c 1)) * (c.repr v 1) ^ 2 := by
      calc (Q (c 0) * c.repr v 0) ^ 2
          = Q (c 0) * ((c.repr v 0) ^ 2 * Q (c 0)) := by ring
        _ = Q (c 0) * (-((c.repr v 1) ^ 2 * Q (c 1))) := by rw [hxya]
        _ = -(Q (c 0) * Q (c 1)) * (c.repr v 1) ^ 2 := by ring
    refine ⟨Q (c 0) * c.repr v 0 / c.repr v 1, ?_⟩
    field_simp [hy]
    linear_combination -hxya
  · rintro ⟨s, hs⟩
    have hs' : s * s = -(Q (c 0) * Q (c 1)) := hs.symm
    let v : V := Q (c 1) • c 0 + s • c 1
    have hvQ : Q v = 0 := by
      change Q (Q (c 1) • c 0 + s • c 1) = 0
      rw [hExp, pow_two, pow_two, hs']
      ring
    have hv0 : v ≠ 0 := by
      intro h
      have h0 := congrArg (fun w => c.repr w 0) h
      simp [v] at h0
      exact hb h0
    refine ⟨Submodule.span K {v}, ?_, ?_⟩
    · rw [finrank_span_singleton hv0, hdimV]
    · intro w hw
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [QuadraticMap.map_smul, hvQ, smul_zero]

private theorem quadraticForm_basis_ne_zero [Invertible (2 : K)]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (c : Basis (Fin 2) K V)
    (hc : ∀ i j, i ≠ j → Q.IsOrtho (c i) (c j)) :
    ∀ i, Q (c i) ≠ 0 := by
  have hPolar : (polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have horthB : LinearMap.BilinForm.iIsOrtho Q.polarBilin ⇑c := by
    intro i j hij
    change (Q.polarBilin (c i)) (c j) = 0
    exact QuadraticMap.isOrtho_polarBilin.mpr (hc i j hij)
  intro i hQi
  exact horthB.not_isOrtho_basis_self_of_nondegenerate hPolar i (by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hQi, smul_zero])

theorem discr_formClass_eq_squareClass_prod [FiniteDimensional K V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (c : Basis (Fin 2) K V)
    (hc : ∀ i j, i ≠ j → Q.IsOrtho (c i) (c j))
    (hne : ∀ i, Q (c i) ≠ 0) :
    TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ) =
      TauCeti.squareClass
        (Units.mk0 (Q (c 0)) (hne 0) * Units.mk0 (Q (c 1)) (hne 1)) := by
  let w : Fin 2 → Kˣ := fun i => Units.mk0 (Q (c i)) (hne i)
  let p : TauCeti.RegularFormPresentation K := ⟨2, w⟩
  have horth : LinearMap.IsOrthoᵢ (associated Q) ⇑c := by
    intro i j hij
    change QuadraticMap.associated Q (c i) (c j) = 0
    exact QuadraticMap.associated_isOrtho.mpr (hc i j hij)
  have e : Q.IsometryEquiv
      (QuadraticMap.weightedSumSquares K fun i => Q (c i)) := by
    have e0 := QuadraticMap.isometryEquivBasisRepr Q c
    rwa [QuadraticMap.basisRepr_eq_of_iIsOrtho Q c horth] at e0
  have hpres : TauCeti.presentedForm p =
      QuadraticMap.weightedSumSquares K (fun i => Q (c i)) := by
    rw [TauCeti.presentedForm_two w]
    congr 1
    funext i
    fin_cases i <;> simp [w]
  have hp : Q.Equivalent (TauCeti.presentedForm p) := by
    rw [hpres]
    exact ⟨e⟩
  have hd := TauCeti.discr_formClass Q hQ p hp
  rw [Fin.prod_univ_two] at hd
  exact hd

private theorem natCard_orthogonalGroup_of_isPlusType [Finite K] [Invertible (2 : K)]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hdim : finrank K V = 2) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
      2 * ((Nat.card K : ℤ) - 1) := by
  have hPolar : (polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hε : ((1 : ℤ) = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
      ((1 : ℤ) = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :=
    Or.inl ⟨rfl, hplus⟩
  have hOraw := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    hPolar (m := 0) (by simpa using hdim) hε
  simpa using hOraw

private theorem natCard_orthogonalGroup_of_not_isPlusType [Finite K] [Invertible (2 : K)]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hdim : finrank K V = 2) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
      2 * ((Nat.card K : ℤ) + 1) := by
  have hPolar : (polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hε : ((-1 : ℤ) = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
      ((-1 : ℤ) = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :=
    Or.inr ⟨rfl, hminus⟩
  have hOraw := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    hPolar (m := 0) (by simpa using hdim) hε
  simpa using hOraw

private theorem exists_sylow_of_card_four {G : Type*} [Group G]
    (S T : Subgroup G) (hST : S ≤ T) {t : ℕ}
    (hScard : Nat.card ↥S = 4) (hTcard : Nat.card ↥T = 4 * t) (ht : Odd t) :
    ∃ Q : Sylow 2 ↥T, (Q : Subgroup ↥T) = S.subgroupOf T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup ↥T := S.subgroupOf T
  have hPcard : Nat.card ↥P = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv, hScard]
  have hP : IsPGroup 2 ↥P := IsPGroup.of_card (n := 2) (by rw [hPcard]; norm_num)
  have hindex : P.index = t := by
    have hmul := Subgroup.index_mul_card (G := ↥T) (H := P)
    rw [hPcard, hTcard] at hmul
    rw [mul_comm 4 t] at hmul
    exact Nat.mul_right_cancel (by norm_num : 0 < 4) hmul
  have hodd : ¬ 2 ∣ P.index := by
    rw [hindex]
    exact ht.not_two_dvd_nat
  exact ⟨hP.toSylow hodd, IsPGroup.toSylow_coe hP hodd⟩

theorem isSylow_signChangeSubgroup_of_discr_ne_zero
    [Finite K] [Invertible (2 : K)]
    [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (c : Basis (Fin 2) K V)
    (hc : ∀ i j, i ≠ j → Q.IsOrtho (c i) (c j))
    (hdisc : TauCeti.RegularFormClass.discr
      (TauCeti.formClass Q hQ) ≠ 0) :
    signChangeSubgroup c ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
    Nat.card ↥(signChangeSubgroup c) = 4 ∧
    ∃ S : Sylow 2 ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      (S : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) =
        (signChangeSubgroup c).subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero (2 : K)
  have hPolar : (polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hdim2 : finrank K V = 2 := by
    rw [Module.finrank_eq_card_basis c, Fintype.card_fin]
  have hne : ∀ i, Q (c i) ≠ 0 := quadraticForm_basis_ne_zero Q hQ c hc
  let u : Kˣ := Units.mk0 (Q (c 0)) (hne 0) * Units.mk0 (Q (c 1)) (hne 1)
  have hdiscr_eq : TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ) =
      TauCeti.squareClass u :=
    discr_formClass_eq_squareClass_prod Q hQ c hc hne
  have hu_val : (u : K) = Q (c 0) * Q (c 1) := by
    simp [u]
  have hnsq_u : ¬ IsSquare u := by
    intro h
    apply hdisc
    rw [hdiscr_eq, (TauCeti.squareClass_eq_zero_iff u).mpr h]
  have hnsq_u_field : ¬ IsSquare (u : K) := by
    intro h
    obtain ⟨x, hx⟩ := h
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hx
      exact u.ne_zero hx
    exact hnsq_u ⟨Units.mk0 x hx0, Units.ext (by
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hx)⟩
  have hSle : signChangeSubgroup c ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    signChangeSubgroup_le_orthogonalGroup h2 Q c hc
  have hScard : Nat.card ↥(signChangeSubgroup c) = 4 := by
    rw [card_signChangeSubgroup h2 c, Fintype.card_fin]
    norm_num
  have hplus_iff : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔
      IsSquare (-(Q (c 0) * Q (c 1))) :=
    isPlusType_iff_isSquare_neg_mul Q c hc (hne 0) (hne 1)
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    haveI : CharP K 2 := by
      have h' := ringChar.charP K
      rwa [h] at h'
    simpa using CharP.cast_eq_zero K 2
  by_cases hsqneg : IsSquare (-1 : K)
  ·
    have hnotsq : ¬ IsSquare (-(Q (c 0) * Q (c 1))) := by
      rintro ⟨s, hs⟩
      obtain ⟨r, hr⟩ := hsqneg
      apply hnsq_u_field
      rw [hu_val]
      refine ⟨r * s, ?_⟩
      calc Q (c 0) * Q (c 1) = -(-(Q (c 0) * Q (c 1))) := by ring
        _ = -(s * s) := by rw [hs]
        _ = (r * r) * (s * s) := by rw [← hr]; ring
        _ = (r * s) * (r * s) := by ring
    have hnotplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
      fun hp => hnotsq (hplus_iff.mp hp)
    have hqmod : Nat.card K % 4 = 1 := by
      have hqodd : Fintype.card K % 2 = 1 :=
        FiniteField.odd_card_of_char_ne_two hchar
      have hne3 : Fintype.card K % 4 ≠ 3 :=
        FiniteField.isSquare_neg_one_iff.mp hsqneg
      rw [Nat.card_eq_fintype_card]
      omega
    have hO : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
        2 * ((Nat.card K : ℤ) + 1) :=
      natCard_orthogonalGroup_of_not_isPlusType Q hQ hdim2 hnotplus
    have hOnat : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
        2 * (Nat.card K + 1) := by
      have hcast : ((2 * (Nat.card K + 1) : ℕ) : ℤ) =
          2 * ((Nat.card K : ℤ) + 1) := by
        push_cast
        ring
      rw [← hcast] at hO
      exact_mod_cast hO
    have hdec1 : Nat.card K = 4 * (Nat.card K / 4) + 1 := by
      have := Nat.div_add_mod (Nat.card K) 4
      omega
    have hdiv1 : (Nat.card K + 1) / 2 = 2 * (Nat.card K / 4) + 1 := by
      nth_rewrite 1 [hdec1]
      have h : 4 * (Nat.card K / 4) + 1 + 1 =
          2 * (2 * (Nat.card K / 4) + 1) := by ring
      rw [h, Nat.mul_div_right _ (by norm_num : 0 < 2)]
    have hq1 : Nat.card K + 1 = 2 * ((Nat.card K + 1) / 2) := by
      rw [hdiv1]
      nth_rewrite 1 [hdec1]
      ring
    have hq1odd : Odd ((Nat.card K + 1) / 2) := by
      rw [Nat.odd_iff, hdiv1]
      omega
    have hOcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
        4 * ((Nat.card K + 1) / 2) := by
      rw [hOnat]
      nth_rewrite 1 [hq1]
      ring
    exact ⟨hSle, hScard,
      exists_sylow_of_card_four (signChangeSubgroup c)
        (TauCeti.QuadraticMap.orthogonalGroup Q) hSle hScard hOcard hq1odd⟩
  ·
    have hsquare : IsSquare (-(Q (c 0) * Q (c 1))) := by
      have hqneg : quadraticChar K (-1 : K) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hsqneg
      have hqu : quadraticChar K (u : K) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hnsq_u_field
      have hprod : IsSquare ((u : K) * (-1 : K)) := by
        refine (quadraticChar_one_iff_isSquare
          (mul_ne_zero u.ne_zero (by norm_num))).mp ?_
        rw [map_mul, hqu, hqneg]
        norm_num
      rw [← hu_val]
      simpa [mul_comm] using hprod
    have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q := hplus_iff.mpr hsquare
    have hqmod : Nat.card K % 4 = 3 := by
      have hne3 : ¬ (Fintype.card K % 4 ≠ 3) :=
        fun h => hsqneg (FiniteField.isSquare_neg_one_iff.mpr h)
      rw [Nat.card_eq_fintype_card]
      simpa using hne3
    have hO : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
        2 * ((Nat.card K : ℤ) - 1) :=
      natCard_orthogonalGroup_of_isPlusType Q hQ hdim2 hplus
    have hOnat : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
        2 * (Nat.card K - 1) := by
      have hq2 : 2 ≤ Nat.card K := by
        have hq1' : 1 < Nat.card K := Finite.one_lt_card (α := K)
        omega
      have hcast : ((2 * (Nat.card K - 1) : ℕ) : ℤ) =
          2 * ((Nat.card K : ℤ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Nat.card K), Nat.cast_ofNat,
          Nat.cast_one]
      rw [← hcast] at hO
      exact_mod_cast hO
    have hdec3 : Nat.card K = 4 * (Nat.card K / 4) + 3 := by
      have := Nat.div_add_mod (Nat.card K) 4
      omega
    have hqsub : Nat.card K - 1 = 4 * (Nat.card K / 4) + 2 := by omega
    have hdiv3 : (Nat.card K - 1) / 2 = 2 * (Nat.card K / 4) + 1 := by
      nth_rewrite 1 [hqsub]
      have h : 4 * (Nat.card K / 4) + 2 =
          2 * (2 * (Nat.card K / 4) + 1) := by ring
      rw [h, Nat.mul_div_right _ (by norm_num : 0 < 2)]
    have hqm1 : Nat.card K - 1 = 2 * ((Nat.card K - 1) / 2) := by
      rw [hdiv3]
      nth_rewrite 1 [hqsub]
      ring
    have hqm1odd : Odd ((Nat.card K - 1) / 2) := by
      rw [Nat.odd_iff, hdiv3]
      omega
    have hOcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =
        4 * ((Nat.card K - 1) / 2) := by
      rw [hOnat]
      nth_rewrite 1 [hqm1]
      ring
    exact ⟨hSle, hScard,
      exists_sylow_of_card_four (signChangeSubgroup c)
        (TauCeti.QuadraticMap.orthogonalGroup Q) hSle hScard hOcard hqm1odd⟩

end CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow

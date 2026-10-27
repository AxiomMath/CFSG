module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsBasic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeReduce

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

section Frame

open CFSG.ClassicalInvolution.ModelFacts

variable {p f : ℕ} [Fact p.Prime] {F V : Type} [Field F] [Finite F] [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem exists_frame_map_eq_of_isClassicalMember_cross [Finite (spinGroup Q)]
    (hodd : Odd (Nat.card (GaloisField p f))) (hFodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate)
    (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    (hker2 : ∀ c ∈ (spinAction Q).ker, c * c = 1)
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {L : Subgroup (spinGroup Q)} {z : spinGroup Q} (h : IsClassicalMember p f L z)
    (hz : spinAction Q z ≠ 1) :
    ∃ fr : Frame Q, L.map (spinAction Q) = fr.La.range := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hFodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have : Finite (V ≃ₗ[F] V) := finite_linearEquiv
  have hfacts := imageFacts_of_isClassicalMember (spinAction Q) h2 hker hker2 hrange hodd h hz
  set θ := spinAction Q with hθ
  set i := θ z with hi_def
  have hiO := hfacts.mem_orthogonalGroup
  have hii : i * i = 1 := hfacts.mul_self
  have hi2 : orderOf i = 2 := hfacts.orderOf_eq_two
  have hdet : LinearEquiv.det i = 1 := by
    have hmem : i ∈ θ.range := ⟨z, rfl⟩
    rw [hrange] at hmem
    exact det_eq_one_of_mem_commutator hmem
  have hW : PolarNondegOn Q (minusSp i) := polarNondegOn_minusSp h2 hQ hiO hii
  have hQ' : (polarBilin (Q.restrict (minusSp i))).Nondegenerate :=
    nondegenerate_polarBilin_restrict hW
  have hQ'' : (Q.restrict (minusSp i)).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ'
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have heven : Even (Module.finrank F (minusSp i)) := even_finrank_minusSp h2 hii hdet
  obtain ⟨l, hlen, hlorth, hlne, hlspan, hldisc⟩ :=
    exists_orthogonal_list_restrict Q (minusSp i) hQ''
  obtain ⟨c, hc, hzz⟩ := spinLift_sq_and_norm hQnd hiO hii rfl hlorth (hlen ▸ heven) hlspan hlne
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hz2' : (z : CliffordAlgebra Q) * z = 1 := by
    have := congrArg (fun x : spinGroup Q => (x : CliffordAlgebra Q)) hz2
    simpa using this
  have hsign : ((-1 : F) ^ l.length.choose 2) = 1 := by
    apply algebraMap_injective' Q
    rw [← hzz, hz2', map_one]
  have hchoose : Even (l.length.choose 2) :=
    (neg_one_pow_eq_one_iff_even (neg_one_ne_one h2)).mp hsign
  have h4a : 4 ∣ Module.finrank F (minusSp i) := by
    rw [← hlen]
    exact four_dvd_of_even_of_even_choose (hlen ▸ heven) hchoose
  have ha0 : Module.finrank F (minusSp i) ≠ 0 := by
    intro h0
    have hbot : minusSp i = ⊥ := Submodule.finrank_eq_zero.mp h0
    refine hz (LinearEquiv.ext fun x => ?_)
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
    have hv0 : v = 0 := by
      have : v ∈ (⊥ : Submodule F V) := hbot ▸ hv
      exact (Submodule.mem_bot _).mp this
    rw [hv0, add_zero]
    exact mem_plusSp.mp hu
  have hcase : Module.finrank F (minusSp i) = 4 ∨ 8 ≤ Module.finrank F (minusSp i) := by
    obtain ⟨k, hk⟩ := h4a
    omega
  rcases hcase with hdim | hdim
  swap
  ·
    exact (false_of_finrank_minus_ge_eight hFodd hQ hiO hii hdim hfacts.subnormal hfacts.perfect
      hfacts.le_nM hfacts.mem hi2
      (fun N hNO hNC hNp => hfacts.le_map_centralizer hNO hNC hNp) hfacts.unique).elim
  ·
    have hiso : ¬ (Q.restrict (minusSp i)).Anisotropic := by
      rw [QuadraticMap.not_anisotropic_iff_exists]
      obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_finrank_ge_three hFodd
        (Q.restrict (minusSp i)) hQ' (by omega)
      exact ⟨v, hv0, hvQ⟩
    have hP0 : (l.map Q).prod ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hc
      exact zero_ne_one hc
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_mul] at hc
      exact zero_ne_one hc
    have hdisc : TauCeti.RegularFormClass.discr (TauCeti.formClass (Q.restrict (minusSp i)) hQ'') =
        0 := by
      rw [hldisc (Units.mk0 _ hP0) rfl, TauCeti.squareClass_eq_zero_iff]
      refine ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), Units.ext ?_⟩
      simp only [Units.val_mk0, Units.val_mul]
      field_simp
      linear_combination hc
    obtain ⟨φ⟩ := hQ''.equivalent_hyperbolicPlane_prod_self hdim hdisc hiso
    obtain ⟨fr, hfr⟩ := Frame4.exists_frame_of_isometryEquiv (minusSp i) φ
    have hfri : fr.La (-1) = i := La_neg_one_eq_of_span_eq h2 hii hiO fr hfr
    have hperp : fr.perp = plusSp i :=
      le_antisymm (perp_le_plusSp h2 hii hiO fr hfr) (plusSp_le_perp h2 hiO fr hfr)
    have hiA : fr.La (-1) ∈ L.map θ := by rw [hfri]; exact hfacts.mem
    have hfix : ∀ a ∈ L.map θ, ∀ x ∈ fr.perp, a x = x := by
      intro a ha x hx
      rw [hperp] at hx
      exact (hfacts.le_nM ha).2.2 x hx
    have hAc : ∀ a ∈ L.map θ, a * fr.La (-1) = fr.La (-1) * a := by
      intro a ha
      rw [hfri]
      exact (hfacts.le_nM ha).2.1
    have hAO : L.map θ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun a ha => (hfacts.le_nM ha).1
    have hdec := Frame4.exists_mul_of_isPerfect_fix (F := fr) h2 hfacts.perfect hAO hAc hfix
    by_cases h4 : 4 ≤ Nat.card F
    · have hR : ∀ R : Subgroup (V ≃ₗ[F] V), IsFundamental Q R (fr.La (-1)) →
          R ≤ (Subgroup.centralizer ({z} : Set (spinGroup Q))).map θ := by
        intro R hR
        have hc := hR.le_centralizer
        rw [hfri] at hc
        exact hfacts.le_map_centralizer
          (hR.le_elementaryGroup.trans (elementaryGroup_le_orthogonalGroup Q)) hc
          (IsFundamental.commutator_eq h4 hR)
      rcases Frame4.eq_La_range_or_eq_swap hFodd h4 fr hfacts.subnormal hfacts.perfect
        (hR _ (IsFundamental.of_frame fr)) (hR _ (IsFundamental.of_frame_swap fr)) hdec hiA
        hfacts.unique with hA | hA
      · exact ⟨fr, hA⟩
      · exact ⟨fr.swap, hA⟩
    ·
      exfalso
      have hsolv : Group.IsSolvable ↥fr.La.range := by
        have := isSolvable_sl_two_of_card_lt (F := F) (by omega)
        exact Group.isSolvable_of_surjective (f := (MonoidHom.rangeRestrict fr.La))
          (MonoidHom.rangeRestrict_surjective _)
      have hsolv' : Group.IsSolvable ↥fr.swap.La.range := by
        have := isSolvable_sl_two_of_card_lt (F := F) (by omega)
        exact Group.isSolvable_of_surjective (f := (MonoidHom.rangeRestrict fr.swap.La))
          (MonoidHom.rangeRestrict_surjective _)
      have hcomm : ∀ x ∈ fr.La.range, ∀ y ∈ fr.swap.La.range, x * y = y * x := by
        rintro _ ⟨A', rfl⟩ _ ⟨B', rfl⟩
        exact fr.La_comm_La_swap A' B'
      have hperfA : Group.IsPerfect ↥(L.map θ) := Subgroup.isPerfect_iff.mpr hfacts.perfect
      have hAle : L.map θ ≤ fr.La.range ⊔ fr.swap.La.range := fun a ha => by
        obtain ⟨n, hn, m, hm, rfl⟩ := hdec a ha
        exact Subgroup.mul_mem_sup hn hm
      have h1 : L.map θ ≤ fr.swap.La.range :=
        le_of_perfect_of_solvable_commuting hcomm hsolv hAle hperfA
      have h2' : L.map θ ≤ ⊥ := by
        refine le_of_perfect_of_solvable_commuting (A := fr.swap.La.range) (B := ⊥)
          (fun x _ y hy => by rw [Subgroup.mem_bot.mp hy, mul_one, one_mul]) hsolv' ?_ hperfA
        rw [sup_bot_eq]
        exact h1
      have hi1 : i = 1 := by
        have := h2' hiA
        rw [Subgroup.mem_bot] at this
        rw [← hfri]
        exact this
      exact hz hi1

theorem card_eq_of_isClassicalMember_spin [Finite (spinGroup Q)]
    (hodd : Odd (Nat.card (GaloisField p f))) (hFodd : Odd (Nat.card F)) (hq : 5 ≤ p ^ f)
    (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hK : CFSG.Open.IsQuasisimple (spinGroup Q))
    {m : ℕ} (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    {L : Subgroup (spinGroup Q)} {z : spinGroup Q} (h : IsClassicalMember p f L z) :
    Nat.card F = p ^ f := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hFodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  set fr₀ := F₀.toFrame hij s t with hfr₀
  have : Nontrivial V := ⟨⟨fr₀.e₁, 0, fr₀.P.e_ne_zero⟩⟩
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hker2 : ∀ c ∈ (spinAction Q).ker, c * c = 1 := by
    intro c hc
    rcases (mem_ker_spinAction_iff Q hQnd c).mp hc with rfl | rfl
    · exact one_mul 1
    · apply Subtype.ext
      simp
  have hθy : ∀ A : SL(2, F), spinAction Q (F₀.longSL2 hij s t A) = fr₀.La A :=
    fun A => DFunLike.congr_fun (spinAction_comp_longSL2 F₀ hij s t) A
  by_cases hz : spinAction Q z = 1
  · exfalso
    have hzc : z ∈ Subgroup.center (spinGroup Q) := hker (MonoidHom.mem_ker.mpr hz)
    set y : spinGroup Q := F₀.longSL2 hij s t (-1) with hy
    have hy1 : spinAction Q y ≠ 1 := by
      rw [hy, hθy]
      intro h1
      exact sl2_neg_one_ne_one hFodd (fr₀.La_injective (h1.trans fr₀.La.map_one.symm))
    have hyy : y * y = 1 := by
      rw [hy, ← map_mul]
      have : (-1 : SL(2, F)) * (-1) = 1 := by simp
      rw [this, map_one]
    have hy2 : orderOf y = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hyy) (fun h1 => hy1 (by rw [h1, map_one]))
    exact false_of_isClassicalMember_of_central hK hodd h hzc hy2
      (fun hyz => hy1 (by rw [hyz]; exact hz))
  · obtain ⟨fr, hfr⟩ := exists_frame_map_eq_of_isClassicalMember_cross hodd hFodd hQ hker hker2
      hrange h hz
    have hLinf := inf_ker_eq_bot_of_isClassicalMember (spinAction Q) hker hker2 hodd h hz
    have hinj : Function.Injective ((spinAction Q).subgroupMap L) := by
      intro x y hxy
      have hxy' : spinAction Q x = spinAction Q y := congrArg Subtype.val hxy
      have hmem : (x : spinGroup Q)⁻¹ * y ∈ L ⊓ (spinAction Q).ker :=
        Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem x.2) y.2, MonoidHom.mem_ker.mpr (by
          rw [map_mul, map_inv, hxy', inv_mul_cancel])⟩
      rw [hLinf, Subgroup.mem_bot] at hmem
      exact Subtype.ext (inv_mul_eq_one.mp hmem)
    let e3 : ↥L ≃* ↥(L.map (spinAction Q)) :=
      MulEquiv.ofBijective ((spinAction Q).subgroupMap L)
        ⟨hinj, (spinAction Q).subgroupMap_surjective L⟩
    let eL : SL(2, F) ≃* ↥L :=
      (MonoidHom.ofInjective fr.La_injective).trans
        ((MulEquiv.subgroupCongr hfr.symm).trans e3.symm)
    exact card_eq_of_isClassicalMember_equiv_sl2' h hq eL

end Frame

section Tags

variable {p f : ℕ} [Fact p.Prime]

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem odd_card_galoisField {r e : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (he : 1 ≤ e) :
    Odd (Nat.card (GaloisField r e)) := by
  rw [GaloisField.card r e (by omega)]
  exact (Nat.Prime.odd_of_ne_two Fact.out hr2).pow

theorem classicalMemberParametersAt_pOmegaPlus : ClassicalMemberParametersAt p f .POmegaPlus := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hFodd := odd_card_galoisField (r := r) hr2 he
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hM : modelUniv .POmegaPlus n r e hr =
      ⟨spinGroup (Spin.quadPlus n (GaloisField r e)), Spin.plusDatum n (GaloisField r e) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus n r e hr = ModelFacts.modelUniv .POmegaPlus n r e hr).trans
      (ModelFacts.modelUniv_POmegaPlus (n := n) (p := r) (f := e) hn3)
  have hfin : Finite (modelUniv .POmegaPlus n r e hr).K :=
    ModelFacts.finite_modelUniv (t := .POmegaPlus) hr2 hr trivial hadm
  have hK := (ModelFacts.modelClauseZero .POmegaPlus n r e hr trivial hadm).1
  rw [hM] at hfin hK
  have hfin' : Finite (spinGroup (Spin.quadPlus n (GaloisField r e))) := hfin
  suffices h : ∀ M : LieUniversal, M =
      ⟨spinGroup (Spin.quadPlus n (GaloisField r e)), Spin.plusDatum n (GaloisField r e) hn3⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        r = p ∧ (e = f ∨ (StatedLieTag.POmegaPlus = .trialityD4 ∧ 3 * e = f)) from h _ hM L z hL
  intro M hM' L z hL
  subst hM'
  set k₀ : Fin n := ⟨0, by omega⟩ with hk₀
  have h1 := card_eq_of_isClassicalMember_spin hodd hFodd hq
    (nondegenerate_polarBilin_quadPlus n (GaloisField r e))
    (range_spinAction_quadPlus_eq_commutator hn3) hK (plusFrame n (GaloisField r e) hn3)
    (rootIdxD_ne n (by omega) k₀) true (rootSignD n k₀) hL
  rw [GaloisField.card r e (by omega)] at h1
  obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hr Fact.out (by omega) hf h1
  exact ⟨rfl, Or.inl rfl⟩

theorem classicalMemberParametersAt_pOmegaOdd : ClassicalMemberParametersAt p f .POmegaOdd := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have hn3 : 3 ≤ n := hadm.2.2.1
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hFodd := odd_card_galoisField (r := r) hr2 he
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hM : modelUniv .POmegaOdd n r e hr =
      ⟨spinGroup (Spin.quadOdd n (GaloisField r e)), Spin.oddDatum n (GaloisField r e)⟩ := rfl
  have hfin : Finite (modelUniv .POmegaOdd n r e hr).K :=
    ModelFacts.finite_modelUniv (t := .POmegaOdd) hr2 hr trivial hadm
  have hK := (ModelFacts.modelClauseZero .POmegaOdd n r e hr trivial hadm).1
  rw [hM] at hfin hK
  have hfin' : Finite (spinGroup (Spin.quadOdd n (GaloisField r e))) := hfin
  suffices h : ∀ M : LieUniversal, M =
      ⟨spinGroup (Spin.quadOdd n (GaloisField r e)), Spin.oddDatum n (GaloisField r e)⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        r = p ∧ (e = f ∨ (StatedLieTag.POmegaOdd = .trialityD4 ∧ 3 * e = f)) from h _ hM L z hL
  intro M hM' L z hL
  subst hM'
  have hk : (0 : ℕ) + 1 < n := by omega
  set k₀ : Fin n := ⟨0, by omega⟩ with hk₀
  set j₀ : Fin n := ⟨0 + 1, hk⟩ with hj₀
  have hij : k₀ ≠ j₀ := Fin.ne_of_val_ne (by simp [hk₀, hj₀])
  have h2 := ModelFacts.two_ne_zero_galoisField (p := r) e hr2
  have h1 := card_eq_of_isClassicalMember_spin hodd hFodd hq
    (nondegenerate_polarBilin_quadOdd n (GaloisField r e) h2)
    (range_spinAction_quadOdd_eq_commutator h2 hn3) hK
    (oddFrame n (GaloisField r e)).toHypFrame hij true false hL
  rw [GaloisField.card r e (by omega)] at h1
  obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hr Fact.out (by omega) hf h1
  exact ⟨rfl, Or.inl rfl⟩

theorem classicalMemberParametersAt_pOmegaMinus :
    ClassicalMemberParametersAt p f .POmegaMinus := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have hn4 : 4 ≤ n := hadm.2.2
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hFodd := odd_card_galoisField (r := r) hr2 he
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hM : modelUniv .POmegaMinus n r e hr =
      ⟨spinGroup (Spin.quadMinus n (GaloisField r e) (minusCoeffs r e).1 (minusCoeffs r e).2),
        Spin.Twisted.minusDatum n (minusCoeffs_irr r e)⟩ := rfl
  have hfin : Finite (modelUniv .POmegaMinus n r e hr).K :=
    ModelFacts.finite_modelUniv (t := .POmegaMinus) hr2 hr trivial hadm
  have hK := (ModelFacts.modelClauseZero .POmegaMinus n r e hr trivial hadm).1
  rw [hM] at hfin hK
  have hfin' : Finite
      (spinGroup (Spin.quadMinus n (GaloisField r e) (minusCoeffs r e).1 (minusCoeffs r e).2)) :=
    hfin
  suffices h : ∀ M : LieUniversal, M =
      ⟨spinGroup (Spin.quadMinus n (GaloisField r e) (minusCoeffs r e).1 (minusCoeffs r e).2),
        Spin.Twisted.minusDatum n (minusCoeffs_irr r e)⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        r = p ∧ (e = f ∨ (StatedLieTag.POmegaMinus = .trialityD4 ∧ 3 * e = f)) from h _ hM L z hL
  intro M hM' L z hL
  subst hM'
  have hk : (0 : ℕ) + 1 < n - 1 := by omega
  set k₀ : Fin (n - 1) := ⟨0, by omega⟩ with hk₀
  have hij := Spin.Twisted.succ_ne_of_lt n (k := k₀) hk
  have h1 := card_eq_of_isClassicalMember_spin hodd hFodd hq
    (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField r e) (minusCoeffs_irr r e))
    (range_spinAction_quadMinus_eq_commutator hn4 (minusCoeffs_irr r e)) hK
    (Spin.Twisted.minusFrame n (minusCoeffs r e).1 (minusCoeffs r e).2).toHypFrame hij true
    false hL
  rw [GaloisField.card r e (by omega)] at h1
  obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hr Fact.out (by omega) hf h1
  exact ⟨rfl, Or.inl rfl⟩

end Tags

end CFSG.ClassicalInvolution.Upgrade

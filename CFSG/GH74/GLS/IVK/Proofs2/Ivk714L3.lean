module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714L4

public section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveCoordinates
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.GH74.GLS.IVK.Proofs2

variable {A : Type} [Group A] [Finite A] {a : A} {L : Subgroup A}

theorem ivk714_inner_case_false_odd (ha : orderOf a = 2) {m ℓ e : ℕ} (hm : 3 ≤ m) (hmodd : m % 2 = 1)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e)
    {ρ : A →* MulAut (projectiveSL m k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}))
    {B : GL (Fin m) k} (hρa : ρ a = conjAut m k B) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    (hrank : StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
      2 ≤ CFSG.pRank 2 L ∨ Odd (Nat.card (center L))) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have h2 : conjAut m k (B ^ 2) = 1 := by
    rw [map_pow, ← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨μ, hμ⟩ := (conjAut_eq_one_iff hm _).mp h2
  have hB1 : ∀ c : kˣ, B ≠ GeneralLinearGroup.scalar (Fin m) c := by
    intro c hc
    have h1 : ρ a = 1 := by rw [hρa, hc, conjAut_scalar]
    rw [← map_one ρ] at h1
    rw [hinj h1, orderOf_one] at ha
    omega
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := inner_component_lift hm B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut m k), (L.map ρ).comap (conjAut m k)⁆ with hXhdef
  have hLnab : ∃ x y : L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_ne_commute_of_isQuasisimple hL₁.2.2
    set eρ := L.equivMapOfInjective ρ hinj
    refine ⟨eρ.symm x, eρ.symm y, fun hc => hxy ?_⟩
    have := congrArg eρ hc
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  by_cases hμs : IsSquare μ.val
  ·
    obtain ⟨r₀, hr₀⟩ := hμs
    have hr0 : r₀ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr₀
      exact μ.ne_zero hr₀
    set c₀ : kˣ := Units.mk0 r₀ hr0
    have hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin m) (c₀ ^ 2) := by
      rw [← hμ]
      congr 1
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr₀, sq]
    obtain ⟨r, hr2, ⟨eX⟩, hXi⟩ := square_component_sl hm htwo hsq hB1 hXh
    obtain ⟨eL⟩ := mulEquiv_of_lift_injective hinj hmap hXi
    set eLS := eL.trans eX
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    ·
      have hq3 : Nat.card k ≠ 3 := by
        intro h3
        have : Group.IsSolvable (GL (Fin 2) k) :=
          CatalogueBGeneralLinear.generalLinear_small_solvable 2 k (Or.inr ⟨rfl, Or.inr h3⟩)
        have : Group.IsSolvable (SpecialLinearGroup (Fin 2) k) :=
          Group.isSolvable_of_isSolvable_injective SpecialLinearGroup.toGL_injective
        have : Group.IsSolvable L :=
          Group.isSolvable_of_isSolvable_injective (f := eLS.toMonoidHom) eLS.injective
        have hq := hL₁.2.2
        have hL' : CFSG.Assembly.IsQuasisimple L :=
          (AssemblyBPredicates.isQuasisimple_iff_native L).2
            ((LocalAnalysis.ComponentInitial.isQuasisimple_congr
              (L.equivMapOfInjective ρ hinj)).2
              ((AssemblyBPredicates.isQuasisimple_iff_native _).1 hq))
        have : Group.IsPerfect L := ⟨hL'.1⟩
        have : Nontrivial L := by
          obtain ⟨x, y, hxy⟩ := hLnab
          exact nontrivial_of_ne (x * y) (y * x) hxy
        exact Group.IsPerfect.not_isSolvable L inferInstance
      have hq2 : Nat.card k ≠ 2 := by
        intro h
        apply htwo
        have := Fintype.ofFinite k
        have h0 := FiniteField.cast_card_eq_zero k
        rw [← Nat.card_eq_fintype_card, h] at h0
        exact_mod_cast h0
      have eQ : L ⧸ center L ≃* StatedProj (StatedSL 2 k) :=
        (QuotientGroup.congr (center L) (center (SpecialLinearGroup (Fin 2) k)) eLS
          (Subgroup.map_center_eq eLS)).trans
          (projectiveSpecialLinearGroupEquivStatedProj 2 k)
      have hX : StatedClassicalModel (L ⧸ center L) .PSL 2 ℓ e :=
        SectionRank.statedClassicalModel_of_mulEquiv eQ
          (statedClassicalModel_psl_two hℓ he hk (by rw [← hk]; exact hq2)
            (by rw [← hk]; exact hq3))
      obtain ⟨-, h7, h34⟩ :=
        UnbalancingLocal.small_standard_source_projective_linear_two_field_parameters_stated hX
      rcases hsrc with h | h | h
      · exact not_rank_or_odd_center_of_sl_two hk2 eLS (hrank h)
      · exact not_nonempty_iff.mpr h7 h
      · exact h34 h
    ·
      have hker : eLS.symm.toMonoidHom.ker ≤ center (SpecialLinearGroup (Fin r) k) := by
        intro x hx
        have : x = 1 := eLS.symm.injective (by rw [map_one]; exact hx)
        rw [this]
        exact one_mem _
      exact false_of_not_small_source
        (not_small_source_of_sl_cover hr3 hℓ hℓ2 he hk eLS.symm.toMonoidHom hker) hp2 hsrc
  ·
    have : Fact (¬ IsSquare μ.val) := ⟨hμs⟩
    obtain ⟨-, -⟩ := nonsquare_component_sl htwo hμ.symm hXh
    set d := matrixDimension B μ hμ.symm with hd
    have hmd : m = 2 * d := by
      have := matrixDimension_twice B μ hμ.symm
      rwa [Fintype.card_fin] at this
    omega

theorem ivk714_prime_pow_three_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : ¬ ℓ ^ 3 ∣ 2520 := by
  intro h
  have h3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega
  have hle : ℓ ^ 3 ≤ 2520 := Nat.le_of_dvd (by norm_num) h
  have hℓ13 : ℓ ≤ 13 := by
    by_contra hc
    push Not at hc
    have : 14 ^ 3 ≤ ℓ ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases ℓ <;> omega

omit [Finite A] in
theorem ivk714_graph_field_case_false (ha : orderOf a = 2) {m ℓ e : ℕ} (hm : 3 ≤ m) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e)
    {ρ : A →* MulAut (projectiveSL m k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}))
    {B : GL (Fin m) k} {σ : k ≃+* k} (hσ : σ ≠ 1)
    (hρa : ρ a = conjAut m k B * fieldAut m k σ * dualAut m k)
    (hsrc : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7))) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hα2 : (conjAut m k B * fieldAut m k σ * dualAut m k) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent hℓ he hk hm B σ hσ hα2
  have hg : 1 ≤ e / 2 := by obtain ⟨r, hr⟩ := heven; omega
  have hKe : Nat.card k = ℓ ^ (2 * (e / 2)) := by
    rw [hk]
    congr 1
    obtain ⟨r, hr⟩ := heven
    omega
  have hud : UnitaryFieldData ℓ (e / 2) k := ⟨hℓ, hg, hKe⟩
  have hσbar : ∀ x, σ x = hud.bar x := fun x => by rw [hσx, hud.bar_apply]
  obtain ⟨-, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_graph_field_full_centralizer_rigidity hud (n := m) hm σ hσbar
  set χ := conjAut m k H with hχ
  set β := fieldAut m k σ * dualAut m k with hβ
  set N := (unitarySU ℓ (e / 2) k m).map (conjAut m k) with hNdef
  have hρa' : ρ a = χ * β * χ⁻¹ := by rw [hρa, hH]
  have hY : (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}).map
      (MulAut.conj χ⁻¹).toMonoidHom =
        OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {β} := by
    rw [map_conj_inner_inf_centralizer, hρa']
    congr 3
    group
  set L₀ := (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom with hL₀def
  have hL₀ : CFSG.Assembly.IsComponentOf L₀
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {β}) := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [hY] at this
  have := finite_mulAut_projectiveSL (k := k) m
  have hL₀N : CFSG.Assembly.IsComponentOf L₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β i j).eq
  have hK2 : Nat.card k = (ℓ ^ (e / 2)) ^ 2 := by rw [hKe, ← pow_mul, mul_comm]
  have eU : unitaryPSU hud m ≃* StatedProj (StatedSU m (ℓ ^ (e / 2)) k) :=
    unitaryPSUEquiv hud (by omega)
  have hnq : (m, ℓ ^ (e / 2)) ≠ (3, 2) := fun h => by
    have h2 := congrArg Prod.snd h
    simp only at h2
    have hdvd2 : ℓ ∣ 2 := by rw [← h2]; exact dvd_pow_self ℓ (by omega)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hdvd2)
  have : IsSimpleGroup (StatedProj (StatedSU m (ℓ ^ (e / 2)) k)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU k ℓ (e / 2) hK2 m
      (by omega) hnq
  have : IsSimpleGroup (unitaryPSU hud m) := eU.isSimpleGroup
  have hNs : IsSimpleGroup N := ι.symm.isSimpleGroup
  have hL₀eq : L₀ = N := eq_of_isComponentOf_simple hNs hL₀N
  have hLimg : L.map ρ = N.map (MulAut.conj χ).toMonoidHom := by
    rw [← hL₀eq, hL₀def, map_conj_inv_map_conj]
  have eL : L ≃* unitaryPSU hud m :=
    ((L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLimg).trans
      ((N.equivMapOfInjective _ (MulAut.conj χ).injective).symm))).trans ι.symm
  have hLnab : ∃ x y : L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_ne_commute_of_isQuasisimple hL₁.2.2
    set eρ := L.equivMapOfInjective ρ hinj
    refine ⟨eρ.symm x, eρ.symm y, fun hc => hxy ?_⟩
    have := congrArg eρ hc
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have : IsSimpleGroup L := eL.isSimpleGroup
  have eZ : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq (OutcomeLocal.center_eq_bot_of_isSimpleGroup hLnab)).trans
      QuotientGroup.quotientBot
  have hdvd : ℓ ^ 3 ∣ Nat.card (unitaryPSU hud m) := by
    rw [Nat.card_congr eU.toEquiv]
    exact prime_cube_dvd_card_psu hℓ hg hK2 hm
  have hcard : Nat.card (unitaryPSU hud m) = 2520 := by
    rw [← CFSG.GH74.GLS.IVK.card_alt7, ← Nat.card_congr hsrc.some.toEquiv,
      Nat.card_congr (eZ.trans eL).toEquiv]
  rw [hcard] at hdvd
  exact ivk714_prime_pow_three_not_dvd hℓ hℓ2 hdvd

omit [Finite A] in
theorem ivk714_orthogonal_three_case_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e) {ρ : A →* MulAut (projectiveSL 3 k)}
    (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 3 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 3) k} (hρa : ρ a = conjAut 3 k B * dualAut 3 k)
    (hB : (B : Matrix (Fin 3) (Fin 3) k)ᵀ = B)
    (hsrc : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7))) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hm3 : 3 ≤ 3 := le_rfl
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift hm3 B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut 3 k), (L.map ρ).comap (conjAut 3 k)⁆ with hXhdef
  set R : GL (Fin 3) k := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup 3 k R with hOdef
  have hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R := by
    set Rm : Matrix (Fin 3) (Fin 3) k := (R : Matrix (Fin 3) (Fin 3) k) with hRm
    set Bm : Matrix (Fin 3) (Fin 3) k := (B : Matrix (Fin 3) (Fin 3) k) with hBm
    have hBR : Bm * Rm = 1 := by
      rw [hBm, hRm, hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc Rmᵀ = Rmᵀ * (Bm * Rm) := by rw [hBR, Matrix.mul_one]
      _ = (Bm * Rm)ᵀ * Rm := by rw [transpose_mul, hB, Matrix.mul_assoc]
      _ = Rm := by rw [hBR, transpose_one, Matrix.one_mul]
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQdef
  have hQ : Q.polarBilin.Nondegenerate :=
    CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R hR
  have hdim : Module.finrank k (Fin 3 → k) = 3 := Module.finrank_fin_fun k
  set eO := matrixOrthogonalEquiv hk2 R hR with heO
  have hXq := (AssemblyBPredicates.isQuasisimple_iff_native Xh).1 hXh.2.2
  by_cases hq3 : Nat.card k = 3
  ·
    have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
      (Or.inl ⟨hodd, Or.inl hdim⟩)
    obtain ⟨hexc, -⟩ := hcov
    obtain ⟨hprime, -⟩ := hexc (Or.inl ⟨hdim, hq3⟩)
    have : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
      isSolvable_of_prime_dvd_card_eq_or_eq hprime
    have : Group.IsSolvable O :=
      Group.isSolvable_of_isSolvable_injective (f := eO.symm.toMonoidHom) eO.symm.injective
    have : Group.IsSolvable Xh :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXh.1)
        (Subgroup.inclusion_injective hXh.1)
    have : Nontrivial Xh := CFSG.LocalCores.isQuasisimple_nontrivial hXq
    have : Group.IsPerfect Xh := hXq.1
    exact Group.IsPerfect.not_isSolvable Xh inferInstance
  obtain ⟨d, ψ, e', hψ, he', hcomm, hq, -⟩ := orthogonal_three_derived hodd hq3 Q hQ hdim
  have hcommO : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map eO.toMonoidHom =
      commutator O := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eO.surjective]
  have hqO : CFSG.IsQuasisimple (commutator O) := by
    refine (isQuasisimple_congr (((commutator _).equivMapOfInjective eO.toMonoidHom
      eO.injective).trans (MulEquiv.subgroupCongr hcommO))).1 hq
  set D : Subgroup (GL (Fin 3) k) := ⁅O, O⁆ with hDdef
  have hDmap : (commutator O).map O.subtype = D := Subgroup.map_subtype_commutator O
  have hqD : CFSG.IsQuasisimple D :=
    (isQuasisimple_congr (((commutator O).equivMapOfInjective O.subtype
      O.subtype_injective).trans (MulEquiv.subgroupCongr hDmap))).1 hqO
  have hXhD : Xh ≤ D := by
    have : Group.IsPerfect Xh := ⟨hXh.2.2.1⟩
    rw [← Subgroup.commutator_eq_self (H := Xh)]
    exact Subgroup.commutator_mono hXh.1 hXh.1
  have hDO : D ≤ O := by
    rw [← hDmap]
    exact Subgroup.map_subtype_le _
  have hXD : Xh = D := by
    have hc := isComponentOf_of_le hXh hXhD hDO
    have hcomp := (isComponentOf_iff_isComponent_subgroupOf hXhD).mp hc
    have htop := eq_top_of_isComponent_quasisimple hqD hcomp
    exact le_antisymm hXhD fun x hx => by
      have : (⟨x, hx⟩ : D) ∈ Xh.subgroupOf D := htop ▸ mem_top _
      exact this
  set Φ₀ : SpecialLinearGroup (Fin 2) k →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    e'.symm.toMonoidHom.comp
      (CatalogueBOrthogonal.traceZeroOrthogonalAction.comp
        (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) k →* GL (Fin 2) k)) with hΦ₀
  have hΦ₀r : Φ₀.range = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [hcomm, hΦ₀, MonoidHom.range_comp]
    rfl
  set f : SpecialLinearGroup (Fin 2) k →* MulAut (projectiveSL 3 k) :=
    (conjAut 3 k).comp (O.subtype.comp (eO.toMonoidHom.comp Φ₀)) with hf
  have hfr : f.range = L.map ρ := by
    rw [hf, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp, hΦ₀r, hcommO,
      hDmap, ← hXD]
    exact hmap
  obtain ⟨σ, hσ⟩ := exists_surjective_of_map_eq_range hinj f hfr.symm
  obtain ⟨e₀⟩ := hsrc
  have hk5 : 5 ≤ Nat.card k := by
    have hℓ3 : 3 ≤ ℓ := by
      have := hℓ.two_le
      omega
    have h3 : 3 ≤ Nat.card k := by
      rw [hk]
      exact hℓ3.trans (Nat.le_self_pow (by omega) ℓ)
    obtain ⟨j, hj⟩ := hodd
    omega
  exact not_surjective_sl2_alt7 hodd hk5
    ((e₀.toMonoidHom.comp (QuotientGroup.mk' (center L))).comp σ)
    ((e₀.surjective.comp (QuotientGroup.mk'_surjective _)).comp hσ)

end CFSG.ComponentClassification.OddSelector

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.Generic.S45 CFSG.GH74.GLS.IVK
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem linear_selector_three_false_alt7 {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hsrc : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
    (hrank : Odd (Nat.card (center L)))
    {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k]
    (hk : Nat.card k = ℓ ^ e) (φ : W ≃* projectiveSL 3 k) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hm3 : 3 ≤ 3 := le_rfl
  have hZ := center_projectiveSL_eq_bot (k := k) hm3
  obtain ⟨ρ, hinj, hρW, -, -⟩ := socle_extension hCW φ hZ
  obtain ⟨-, -, -, hL₁⟩ := socle_images φ hinj hρW hLW hL
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) hm3
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ a)
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hsrc' : StatedClassicalModel (L ⧸ center L) .PSL 2 3 1 ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := Or.inr (Or.inl hsrc)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      exact ivk714_inner_case_false_odd ha hm3 (by norm_num) hℓ hℓ2 he hk hinj hL₁ hρa hp2 hsrc'
        (fun _ => Or.inr hrank)
    · exact field_case_false ha hm3 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc'
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut 3 k B * dualAut 3 k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
      rcases transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
      · exact ivk714_orthogonal_three_case_false hℓ hℓ2 he hk hinj hL₁ hρa hB hsrc
      · exfalso
        have hdet : (B : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
          ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
        have h1 := congrArg Matrix.det hB
        rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at h1
        apply hdet
        have h2' : (2 : k) * (B : Matrix (Fin 3) (Fin 3) k).det = 0 := by
          linear_combination h1
        exact (mul_eq_zero.1 h2').resolve_left htwo
    · exact ivk714_graph_field_case_false ha hm3 hℓ hℓ2 he hk hinj hL₁ hτ hρa hsrc

theorem ivk714_psl_three {p f : ℕ} (hp2 : p ≠ 2) :
    Ivk714Empty (fun X _ => LieModel X .PSL 3 p f) := by
  intro K _ _ hs hK z hz h
  have hmodel := LQ.stated_of_lieModel_PSL hK
  have hZ : center K = ⊥ := center_eq_bot_of_simple_of_nonab hs h.nonabelian
  obtain ⟨L, hLW, hL, hq, hodd⟩ := h.exists_inner_component hZ
  have hCW := centralizer_inner_eq_bot_of_center_eq_bot hZ
  let e : K ≃* ↥(inner K) := MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)
  obtain ⟨⟨hr, hf', -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  let φ : ↥(inner K) ≃* projectiveSL 3 F :=
    e.symm.trans (e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)))
  exact linear_selector_three_false_alt7 (W := inner K) hCW hz hLW hL hq hodd hr hp2 hf' hF φ

theorem ivk714_l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk714Empty (fun X _ => LieModel X .PSL 3 p f) :=
  fun _ _ _ hp2 _ => ivk714_psl_three hp2

end CFSG.GH74.GLS.IVK.Proofs2

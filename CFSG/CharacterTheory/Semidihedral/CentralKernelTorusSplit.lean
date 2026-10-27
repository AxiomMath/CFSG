module

public import CFSG.CharacterTheory.Semidihedral.CentralKernelTorusSplitSupport
public import CFSG.CharacterTheory.Semidihedral.Local.SplitActualLayer
public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupNormalizer
public import CFSG.CharacterTheory.Semidihedral.CentralKernelTorusSplitModel

public section

namespace CFSG.Semidihedral.CentralKernelTorusSplit

noncomputable section

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.MatrixCoverData
open CFSG.Semidihedral.ActualFourGroupCentralizer (originalOddInclusion OriginalWProduct
  fixed_coefficient_action)
open CFSG.Semidihedral.Local
  (all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift
    all_local_prime_covers_split_actual_layer_except_central_three_at_nine)

theorem actual_central_odd_kernel_is_inverted_and_fixed_layer_torus_splits {G : Type}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    let L := CFSG.generalizedFitting (Gamma t)
    let T₀ := L.comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let D := Subgroup.centralizer ({s} : Set (C t))
    let R := (CFSG.pPrimeCore 2 D).map D.subtype
    let A₀ := N t ⊓ Subgroup.centralizer ({s} : Set (C t))
    let CJ := J ⊓ Subgroup.centralizer ({s} : Set (C t))
    let CT := T₀ ⊓ Subgroup.centralizer ({nu t s} : Set (H t))
    let qe := if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
        (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
          Set (C t)) ⊓ Y).map (nu t) = T₀) →
    (∀ x ∈ E, s * x * s⁻¹ = x⁻¹) ∧ E ⊓ Subgroup.centralizer ({s} : Set (C t)) = ⊥ ∧
    (∃ φ : CJ ≃* CT, ∀ x : CJ, (φ x : H t) = nu t x) ∧
    IsCyclic CJ ∧ Nat.card CJ = qe ∧
    ∃ W : Subgroup (C t), (∀ x, x ∈ W ↔ x ∈ CJ ∧ Odd (orderOf x)) ∧
      IsCyclic W ∧ Nat.card W = qe / 2 ∧
      CJ = Subgroup.zpowers (tInC t) ⊔ W ∧ Subgroup.zpowers (tInC t) ⊓ W = ⊥ ∧
      (∀ x ∈ Subgroup.zpowers (tInC t), ∀ w ∈ W, Commute x w) ∧
      W ⊓ N t = ⊥ ∧ W ≤ R ∧
      R ⊓ Y = W ⊔ A₀ ∧ W ⊓ A₀ = ⊥ ∧ (∀ w ∈ W, ∀ x ∈ A₀, Commute w x) ∧
      ∃ d ∈ J, orderOf d = 4 ∧ d ^ 2 = tInC t ∧ d * s * d⁻¹ = tInC t * s ∧
        ∀ w ∈ W, d * w * d⁻¹ = w⁻¹ := by
  intro L T₀ Y H₀ J E D R A₀ CJ CT qe hcov
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJperf, hJnormal, htJ, hJimage, hJN, hYJN, hEodd, hcenterJ, hEt, -, -, -,
      ⟨F', hF', hF'fin, eta', -, hF'card, -, -, -, -⟩, -, -, -⟩ :=
    (all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel).1 hcov
  replace hJperf : Group.IsPerfect J := hJperf
  replace hJnormal : J.Normal := hJnormal
  replace htJ : tInC t ∈ J := htJ
  replace hJimage : J.map (nu t) = T₀ := hJimage
  replace hJN : ⁅J, N t⁆ = ⊥ := hJN
  replace hYJN : Y = J ⊔ N t := hYJN
  replace hEodd : Odd (Nat.card E) := hEodd
  replace hcenterJ : (Subgroup.center J).map J.subtype = E ⊔ Subgroup.zpowers (tInC t) :=
    hcenterJ
  replace hEt : E ⊓ Subgroup.zpowers (tInC t) = ⊥ := hEt
  have hcardT₀' : Nat.card T₀ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F') :=
    Nat.card_congr eta'.toEquiv
  obtain ⟨-, -, -, -, hne9, -⟩ :=
    all_local_prime_covers_split_actual_layer_except_central_three_at_nine
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel (Or.inl hcov)
  have hfour :=
    CFSG.Semidihedral.ActualFourGroupNormalizer.actual_simple_layer_four_group_normalizer_action.{0}
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨-, F, hF, hFfin, A, a, hFcard, hAodd, -, -, -, -, -, haF, -, -, htorus, hPsiex⟩ :=
    hfour.1
  obtain ⟨Psi, hz, hu, hCdata, -, -, -, -⟩ := hPsiex s hs hst
  obtain ⟨⟨x0, y0, hxy⟩, hnorm⟩ := hfour.2 F A (MatrixCover.fixedUnit F A a)
    (fixed_coefficient_action F A a) s hs hst Psi hz hu hFcard hAodd haF
  have hNdata := hnorm x0 y0 hxy
  set a' := MatrixCover.fixedUnit F A a with ha'
  have hfix : ∀ sigma : A, (sigma : F ≃+* F) (a' : F) = a' := fixed_coefficient_action F A a
  have hFodd : Odd (Nat.card F) := hFcard ▸ hpodd.pow
  obtain ⟨-, -, -, hAutcyc, -, -⟩ :=
    CFSG.Semidihedral.SemilinearOuterQuotient.odd_field_projective_semilinear_exact_outer_quotient
      F hp hpodd hf hFcard
  have hAcyc : IsCyclic A := Subgroup.isCyclic A
  have hAcomm : ∀ σ τ : A, σ * τ = τ * σ := by
    obtain ⟨g, hg⟩ := hAcyc.exists_generator
    intro σ τ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg σ)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg τ)
    exact (Commute.zpow_zpow_self g i j).eq
  have hT₀perf : Group.IsPerfect T₀ := by
    have : Fintype F' := Fintype.ofFinite F'
    have h4 : ∃ s : Finset F', s.card = 4 := by
      obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F'))
        (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF'card]; omega)
      exact ⟨u, hu⟩
    have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    exact Group.IsPerfect.ofSurjective (f := eta'.symm.toMonoidHom) eta'.symm.surjective
  replace hT₀perf : Group.IsPerfect T₀ := hT₀perf
  let SLim := (originalSlInH F a' A hfix).range
  have hSLinj := MatrixFourGroupNormalizer.originalSlInH_injective F a' A hfix
  have hcommH : commutator (H t) =
      (commutator (OriginalH F a' A hfix)).map Psi.toMonoidHom := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ Psi.surjective]
  have hT₀le : T₀ ≤ SLim.map Psi.toMonoidHom :=
    calc T₀ = ⁅T₀, T₀⁆ := (Subgroup.isPerfect_iff.mp hT₀perf).symm
      _ ≤ commutator (H t) := Subgroup.commutator_mono le_top le_top
      _ = (commutator (OriginalH F a' A hfix)).map Psi.toMonoidHom := hcommH
      _ ≤ SLim.map Psi.toMonoidHom :=
        Subgroup.map_mono (commutator_le_originalSlInH_range F a' A hfix hAcomm)
  have hcardT₀ : Nat.card (SLim.map Psi.toMonoidHom) ≤ Nat.card T₀ := by
    rw [Subgroup.card_map_of_injective Psi.injective, hcardT₀',
      ← Nat.card_congr (MonoidHom.ofInjective hSLinj).toEquiv]
    exact (card_SL_two_congr (hFcard.trans hF'card.symm)).le
  have hT₀eq : T₀ = SLim.map Psi.toMonoidHom := Subgroup.eq_of_le_of_card_ge hT₀le hcardT₀
  have hνJ : ∀ x : J, nu t x ∈ T₀ := fun x => hJimage ▸ Subgroup.mem_map_of_mem _ x.2
  have hmemSL : ∀ x : J, Psi.symm (nu t x) ∈ SLim := by
    intro x
    have hx := hνJ x
    rw [hT₀eq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hyx]
    simpa using hy
  let eSL := MonoidHom.ofInjective hSLinj
  let πF : J →* SL F := eSL.symm.toMonoidHom.comp
    ((Psi.symm.toMonoidHom.comp ((nu t).comp J.subtype)).codRestrict SLim hmemSL)
  have hπF : ∀ x : J, originalSlInH F a' A hfix (πF x) = Psi.symm (nu t x) := fun x =>
    MonoidHom.apply_ofInjective_symm hSLinj ⟨Psi.symm (nu t x), hmemSL x⟩
  have hπFsurj : Function.Surjective πF := by
    intro X
    have hmem : Psi (originalSlInH F a' A hfix X) ∈ T₀ := by
      rw [hT₀eq]
      exact ⟨_, ⟨X, rfl⟩, rfl⟩
    rw [← hJimage] at hmem
    obtain ⟨x, hx, hxX⟩ := hmem
    refine ⟨⟨x, hx⟩, hSLinj ?_⟩
    rw [hπF]
    change Psi.symm (nu t x) = _
    rw [hxX, MulEquiv.symm_apply_apply]
  have hπFker : ∀ x : J, πF x = 1 ↔ (x : C t) ∈ N t := by
    intro x
    constructor
    · intro h
      have h1 : Psi.symm (nu t x) = 1 := by rw [← hπF, h, map_one]
      have h2 : nu t x = 1 := by
        have := congrArg Psi h1
        simpa using this
      exact (QuotientGroup.eq_one_iff _).mp h2
    · intro h
      apply hSLinj
      have h1 : nu t x = 1 := (QuotientGroup.eq_one_iff _).mpr h
      rw [hπF, map_one, h1, map_one]
  let tJ : J := ⟨tInC t, htJ⟩
  have hπFt : πF tJ = -1 := by
    apply hSLinj
    rw [hπF]
    change Psi.symm (nu t (tInC t)) = originalSlInH F a' A hfix (OddFieldSL2.minusIdentity F)
    rw [← hz, MulEquiv.symm_apply_apply]
    rfl
  have hsU : Psi.symm (nu t s) = originalU F a' A hfix := by
    rw [← hu, MulEquiv.symm_apply_apply]
  have hπFconj : ∀ x : J, πF (MulAut.conjNormal (s : C t) x) = beta F a' (πF x) := by
    intro x
    apply hSLinj
    rw [hπF, ← originalU_conj_originalSlInH, hπF]
    change Psi.symm (nu t (s * (x : C t) * s⁻¹)) = _
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hsU]
  have hEJ : E ≤ J := inf_le_left
  have hπFkerE : πF.ker = E.subgroupOf J := by
    ext x
    rw [MonoidHom.mem_ker, hπFker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have htc : ∀ y : C t, tInC t * y = y * tInC t := fun y =>
    (Subgroup.mem_center_iff.mp (tInC_central t) y).symm
  have hEinv : ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ := by
    by_cases h9 : p ^ f = 9
    · have hFcard9 : Nat.card F = 9 := hFcard.trans h9
      have hker : πF.ker ≤ Subgroup.center J := by
        intro x hx
        rw [hπFkerE, Subgroup.mem_subgroupOf] at hx
        have hmem : (x : C t) ∈ (Subgroup.center J).map J.subtype := by
          rw [hcenterJ]
          exact Subgroup.mem_sup_left hx
        obtain ⟨y, hy, hyx⟩ := hmem
        have hxy : y = x := Subtype.ext hyx
        rwa [← hxy]
      have hkerodd : Odd (Nat.card πF.ker) := by
        rw [hπFkerE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv]
        exact hEodd
      have htJc : tJ ∈ Subgroup.center J := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (htc y).symm
      have hkert : πF.ker ⊓ Subgroup.zpowers tJ = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hxk, hxt⟩
        have hxk' : x ∈ πF.ker := hxk
        rw [hπFkerE] at hxk'
        replace hxk : (x : C t) ∈ E := hxk'
        have hxt' : (x : C t) ∈ Subgroup.zpowers (tInC t) := by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxt
          exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk]; rfl⟩
        have h : (x : C t) ∈ E ⊓ Subgroup.zpowers (tInC t) := Subgroup.mem_inf.mpr ⟨hxk, hxt'⟩
        rw [hEt] at h
        exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h))
      have hdet : ¬ IsSquare ((MatrixCoverData.J F a' : GL2 F) :
          Matrix (Fin 2) (Fin 2) F).det := by
        intro h
        apply haF
        apply (CFSG.Semidihedral.SemilinearOuterQuotient.isSquare_unit_iff a').mpr
        rw [← MatrixCoverData.J_det F a', Matrix.GeneralLinearGroup.val_det_apply]
        exact h
      have hαt : MulAut.conjNormal (s : C t) tJ = tJ := by
        apply Subtype.ext
        change (s : C t) * tInC t * (s : C t)⁻¹ = tInC t
        rw [← htc, mul_inv_cancel_right]
      have hα : ∀ x : J, πF (MulAut.conjNormal (s : C t) x) =
          CFSG.LinearGroups.slSemilinearAut (MatrixCoverData.J F a') (RingEquiv.refl F)
            (πF x) := by
        intro x
        rw [slSemilinearAut_J_refl, hπFconj]
      have hinv := inverts_kernel_of_card_nine hFcard9 πF hπFsurj hker hkerodd tJ htJc hπFt
        hkert (MatrixCoverData.J F a') hdet (MulAut.conjNormal (s : C t)) hαt hα
      intro x hx
      have hxk : (⟨x, hx.1⟩ : J) ∈ πF.ker := by
        rw [hπFkerE]
        exact hx
      exact congrArg Subtype.val (hinv _ hxk)
    · have hE1 : E = ⊥ := (hne9 h9).1
      intro x hx
      rw [hE1, Subgroup.mem_bot] at hx
      rw [hx, mul_one, mul_inv_cancel, inv_one]
  have hECs : E ⊓ Subgroup.centralizer ({s} : Set (C t)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxs⟩
    have h1 : s * x * s⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp hxs, mul_inv_cancel_right]
    have h2 := hEinv x hxE
    rw [h1] at h2
    have hodd : Odd (orderOf x) := hEodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard E hxE)
    have hsq : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h2]
      exact inv_mul_cancel x
    have hord : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (Nat.not_odd_iff_even.mpr even_two)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hord)
  have hCTiff : ∀ X : SL F, Psi (originalSlInH F a' A hfix X) ∈ CT ↔ X ∈ Torus F a' := by
    intro X
    rw [← originalSlInH_commute_originalU_iff F a' A hfix X]
    constructor
    · rintro ⟨-, hc⟩
      have h := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [← hu, ← map_mul, ← map_mul] at h
      exact Psi.injective h
    · intro hX
      refine ⟨?_, ?_⟩
      · change Psi (originalSlInH F a' A hfix X) ∈ T₀
        rw [hT₀eq]
        exact ⟨_, ⟨X, rfl⟩, rfl⟩
      · apply Subgroup.mem_centralizer_singleton_iff.mpr
        rw [← hu, ← map_mul, ← map_mul, hX]
  have hCTmem : ∀ c ∈ CT, ∃ X ∈ Torus F a', Psi (originalSlInH F a' A hfix X) = c := by
    intro c hc
    have hcT : c ∈ T₀ := hc.1
    rw [hT₀eq] at hcT
    obtain ⟨_, ⟨X, rfl⟩, hX⟩ := hcT
    have hXc : Psi (originalSlInH F a' A hfix X) = c := hX
    refine ⟨X, (hCTiff X).mp (hXc ▸ hc), hXc⟩
  let ιT : Torus F a' →* CT :=
    ((Psi.toMonoidHom.comp (originalSlInH F a' A hfix)).comp (Torus F a').subtype).codRestrict
      CT (fun X => (hCTiff X.val).mpr X.2)
  have hιTinj : Function.Injective ιT := fun X Y h =>
    Subtype.ext (hSLinj (Psi.injective (congrArg Subtype.val h)))
  have hιTsurj : Function.Surjective ιT := by
    rintro ⟨c, hc⟩
    obtain ⟨X, hX, hXc⟩ := hCTmem c hc
    exact ⟨⟨X, hX⟩, Subtype.ext hXc⟩
  let eTC : Torus F a' ≃* CT := MulEquiv.ofBijective ιT ⟨hιTinj, hιTsurj⟩
  have : E.Normal := Subgroup.normal_inf_normal J (N t)
  have hνCJ : ∀ x : CJ, nu t x ∈ CT := by
    intro x
    refine ⟨hνJ ⟨x, x.2.1⟩, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp x.2.2]
  let νC : CJ →* CT := ((nu t).comp CJ.subtype).codRestrict CT hνCJ
  have hνCinj : Function.Injective νC := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : nu t x = 1 := congrArg Subtype.val hx
    have hxN : (x : C t) ∈ N t := (QuotientGroup.eq_one_iff _).mp h1
    have hmem : (x : C t) ∈ E ⊓ Subgroup.centralizer ({s} : Set (C t)) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨x.2.1, hxN⟩, x.2.2⟩
    rw [hECs] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hνCsurj : Function.Surjective νC := by
    rintro ⟨c, hcT, hcs⟩
    have hc' : c ∈ J.map (nu t) := by
      rw [hJimage]
      exact hcT
    obtain ⟨j, hj, rfl⟩ := hc'
    have hjs : s * j * s⁻¹ * j⁻¹ ∈ E := by
      refine Subgroup.mem_inf.mpr ⟨J.mul_mem (hJnormal.conj_mem j hj s) (J.inv_mem hj), ?_⟩
      apply (QuotientGroup.eq_one_iff _).mp
      change nu t (s * j * s⁻¹ * j⁻¹) = 1
      have h := Subgroup.mem_centralizer_singleton_iff.mp hcs
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
      group
    obtain ⟨c', hc'J, hc's, hc'E⟩ := exists_fixed_lift hEJ hEodd hs hj hjs
    refine ⟨⟨c', Subgroup.mem_inf.mpr ⟨hc'J, Subgroup.mem_centralizer_singleton_iff.mpr hc's⟩⟩,
      Subtype.ext ?_⟩
    change nu t c' = nu t j
    exact QuotientGroup.eq.mpr (Subgroup.mem_inf.mp hc'E).2
  let φ : CJ ≃* CT := MulEquiv.ofBijective νC ⟨hνCinj, hνCsurj⟩
  have hTS : torusSize (Nat.card F) = qe := by
    rw [hFcard]
    rfl
  have hCJcyc : IsCyclic CJ := by
    have : IsCyclic (Torus F a') := htorus.cyclic
    exact isCyclic_of_surjective (φ.symm.toMonoidHom.comp eTC.toMonoidHom)
      (φ.symm.surjective.comp eTC.surjective)
  have hCJcard : Nat.card CJ = qe := by
    rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr eTC.toEquiv, htorus.card, hTS]
  let ι : Torus F a' →* C t := CJ.subtype.comp (φ.symm.toMonoidHom.comp eTC.toMonoidHom)
  have hιinj : Function.Injective ι :=
    Subtype.val_injective.comp (φ.symm.injective.comp eTC.injective)
  have hιCJ : ∀ X, ι X ∈ CJ := fun X => (φ.symm (eTC X)).2
  have hνι : ∀ X : Torus F a', nu t (ι X) = Psi (originalSlInH F a' A hfix X) := fun X =>
    congrArg Subtype.val (φ.apply_symm_apply (eTC X))
  have hιsurj : ∀ x ∈ CJ, ∃ X, ι X = x := by
    intro x hx
    refine ⟨eTC.symm (φ ⟨x, hx⟩), ?_⟩
    change ((φ.symm (eTC (eTC.symm (φ ⟨x, hx⟩)))) : C t) = x
    rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  let W := (MatrixTorus.W F a').map ι
  have hWmem : ∀ x, x ∈ W ↔ x ∈ CJ ∧ Odd (orderOf x) := by
    intro x
    constructor
    · rintro ⟨X, hX, rfl⟩
      refine ⟨hιCJ X, ?_⟩
      rw [orderOf_injective ι hιinj]
      exact (htorus.odd_membership X).mp hX
    · rintro ⟨hx, hodd⟩
      obtain ⟨X, rfl⟩ := hιsurj x hx
      refine ⟨X, (htorus.odd_membership X).mpr ?_, rfl⟩
      rw [← orderOf_injective ι hιinj]
      exact hodd
  have hWcyc : IsCyclic W := by
    have : IsCyclic (MatrixTorus.W F a') := htorus.odd_cyclic
    let e := (MatrixTorus.W F a').equivMapOfInjective ι hιinj
    exact isCyclic_of_surjective e e.surjective
  have hWcard : Nat.card W = qe / 2 := by
    rw [Subgroup.card_map_of_injective hιinj, htorus.odd_card, hTS]
  have hWodd : Odd (Nat.card W) := by
    rw [Subgroup.card_map_of_injective hιinj, htorus.odd_card]
    exact torusSize_half_odd hFodd
  have htCJ : tInC t ∈ CJ :=
    Subgroup.mem_inf.mpr ⟨htJ, Subgroup.mem_centralizer_singleton_iff.mpr (htc s)⟩
  have hιz : ι (MatrixTorus.z F a') = tInC t := by
    have h : eTC (MatrixTorus.z F a') = φ ⟨tInC t, htCJ⟩ := by
      apply Subtype.ext
      change Psi (originalSlInH F a' A hfix (OddFieldSL2.minusIdentity F)) = nu t (tInC t)
      exact hz
    change ((φ.symm (eTC (MatrixTorus.z F a'))) : C t) = tInC t
    rw [h, MulEquiv.symm_apply_apply]
  have hcompl := torus_internal_direct F a' hFodd haF
  have hιrange : ι.range = CJ := by
    ext x
    constructor
    · rintro ⟨X, rfl⟩
      exact hιCJ X
    · intro hx
      exact hιsurj x hx
  have hCJdecomp : CJ = Subgroup.zpowers (tInC t) ⊔ W := by
    rw [← hιrange, MonoidHom.range_eq_map, ← hcompl.sup_eq_top, Subgroup.map_sup,
      MonoidHom.map_zpowers, hιz]
  have hCJdisj : Subgroup.zpowers (tInC t) ⊓ W = ⊥ := by
    rw [← hιz, ← MonoidHom.map_zpowers, ← Subgroup.map_inf_eq _ _ ι hιinj,
      hcompl.disjoint.eq_bot, Subgroup.map_bot]
  have hcommt : ∀ x ∈ Subgroup.zpowers (tInC t), ∀ w ∈ W, Commute x w := by
    intro x hx w _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (htc w) k))
  have hWN : W ⊓ N t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxN⟩
    have hxCJ := ((hWmem x).mp hxW).1
    have hmem : x ∈ E ⊓ Subgroup.centralizer ({s} : Set (C t)) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxCJ.1, hxN⟩, hxCJ.2⟩
    rwa [hECs] at hmem
  have hWD : W ≤ D := fun x hx => ((hWmem x).mp hx).1.2
  have hJnorm : ∀ g : C t, g ∈ Subgroup.normalizer (J : Set (C t)) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hJnormal]
    exact Subgroup.mem_top g
  have hconjW : ∀ g : C t, g * s * g⁻¹ * s⁻¹ ∈ Subgroup.zpowers (tInC t) →
      ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hgs w hw
    have hgJ := hJnorm g
    obtain ⟨⟨hwJ, hws⟩, hwodd⟩ := (hWmem w).mp hw
    rw [hWmem]
    refine ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgJ w).mp hwJ, ?_⟩, ?_⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgs
      have hgsg : g * s * g⁻¹ = tInC t ^ k * s := by
        rw [hk]
        group
      have hws' : w * s = s * w := Subgroup.mem_centralizer_singleton_iff.mp hws
      have hwt : w * tInC t ^ k = tInC t ^ k * w := ((Commute.zpow_left (htc w) k)).eq.symm
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hcomm : (g * w * g⁻¹) * (g * s * g⁻¹) = (g * s * g⁻¹) * (g * w * g⁻¹) := by
        calc (g * w * g⁻¹) * (g * s * g⁻¹) = g * (w * s) * g⁻¹ := by group
          _ = g * (s * w) * g⁻¹ := by rw [hws']
          _ = (g * s * g⁻¹) * (g * w * g⁻¹) := by group
      rw [hgsg] at hcomm
      have hxt : (g * w * g⁻¹) * tInC t ^ k = tInC t ^ k * (g * w * g⁻¹) :=
        ((Commute.zpow_left (htc (g * w * g⁻¹)) k)).eq.symm
      calc g * w * g⁻¹ * s = (tInC t ^ k)⁻¹ * (tInC t ^ k * (g * w * g⁻¹)) * s := by group
        _ = (tInC t ^ k)⁻¹ * ((g * w * g⁻¹) * tInC t ^ k) * s := by rw [hxt]
        _ = (tInC t ^ k)⁻¹ * ((g * w * g⁻¹) * (tInC t ^ k * s)) := by group
        _ = (tInC t ^ k)⁻¹ * ((tInC t ^ k * s) * (g * w * g⁻¹)) := by rw [hcomm]
        _ = s * (g * w * g⁻¹) := by group
    · have h : orderOf (g * w * g⁻¹) = orderOf w :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective w
      rw [h]
      exact hwodd
  have hWnormD : (W.subgroupOf D).Normal := by
    constructor
    intro w hw g
    change (g : C t) * (w : C t) * (g : C t)⁻¹ ∈ W
    apply hconjW (g : C t) _ w hw
    have hgs : (g : C t) * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp g.2
    rw [hgs, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hWR : W ≤ R := by
    have hcop : Nat.Coprime 2 (Nat.card (W.subgroupOf D)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWD).toEquiv]
      exact Nat.coprime_two_left.mpr hWodd
    have hle : W.subgroupOf D ≤ CFSG.pPrimeCore 2 D := le_sSup ⟨hWnormD, hcop⟩
    have hmap := Subgroup.map_mono (f := D.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hWD] at hmap
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hA₀D : A₀ ≤ D := inf_le_right
  have hA₀R : A₀ ≤ R := by
    have hnorm : (A₀.subgroupOf D).Normal := by
      constructor
      intro x hx g
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (inferInstance : (N t).Normal).conj_mem _ (Subgroup.mem_inf.mp hx).1 _
      · exact (D.mul_mem (D.mul_mem g.2 x.2) (D.inv_mem g.2))
    have hcop : Nat.Coprime 2 (Nat.card (A₀.subgroupOf D)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀D).toEquiv]
      exact Nat.coprime_two_left.mpr (hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    have hle : A₀.subgroupOf D ≤ CFSG.pPrimeCore 2 D := le_sSup ⟨hnorm, hcop⟩
    have hmap := Subgroup.map_mono (f := D.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hA₀D] at hmap
  have hJcent : J ≤ Subgroup.centralizer (N t : Set (C t)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN
  have hcommJN : ∀ x ∈ J, ∀ y ∈ N t, Commute x y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hJcent hx) y hy).symm
  let Ds := CFSG.Semidihedral.ActualFourGroupCentralizer.D s
  let Rs := CFSG.Semidihedral.ActualFourGroupCentralizer.R s
  let N0 := CFSG.Semidihedral.ActualFourGroupCentralizer.N0InR s
  have : N0.Normal := hCdata.kernel_normal
  have hRs : (Rs : Subgroup Ds) = CFSG.pPrimeCore 2 Ds :=
    CFSG.Semidihedral.KleinFourOddKernel.piCore_odd_eq_pPrimeCore
  obtain ⟨eR, heR⟩ := hCdata.original_quotient
  have hcoord : ∀ (e : Rs ⧸ N0 ≃* OriginalWProduct F A a' hfix),
      (∀ r, Psi (originalOddInclusion F A a' hfix (e (QuotientGroup.mk' N0 r))) =
        nu t ((r : Ds) : C t)) →
      ∀ r : Rs, ((r : Ds) : C t) ∈ Y →
        ∃ w₀ : MatrixTorus.W F a', e (QuotientGroup.mk' N0 r) = SemidirectProduct.inl w₀ ∧
          nu t (ι (w₀ : Torus F a')) = nu t ((r : Ds) : C t) := by
    intro e he r hrY
    have h1 := he r
    have hT : Psi (originalOddInclusion F A a' hfix (e (QuotientGroup.mk' N0 r))) ∈ T₀ := by
      rw [h1]
      exact hrY
    rw [hT₀eq] at hT
    obtain ⟨y, hy, hyeq⟩ := hT
    have hy' : originalOddInclusion F A a' hfix (e (QuotientGroup.mk' N0 r)) ∈ SLim := by
      have h2 := Psi.injective hyeq
      rw [← h2]
      exact hy
    have hright := (originalOddInclusion_mem_range_iff F a' A hfix _).mp hy'
    refine ⟨(e (QuotientGroup.mk' N0 r)).left, SemidirectProduct.ext rfl hright, ?_⟩
    rw [hνι, ← h1]
    have hw : e (QuotientGroup.mk' N0 r) =
        SemidirectProduct.inl (e (QuotientGroup.mk' N0 r)).left :=
      SemidirectProduct.ext rfl hright
    conv_rhs => rw [hw]
    rfl
  have hRY : ∀ r ∈ R, r ∈ Y → ∃ w ∈ W, w⁻¹ * r ∈ A₀ := by
    rintro _ ⟨r₀, hr₀, rfl⟩ hrY
    have hr₀' : r₀ ∈ Rs := by
      rw [hRs]
      exact hr₀
    obtain ⟨w₀, -, hνw⟩ := hcoord eR heR ⟨r₀, hr₀'⟩ hrY
    refine ⟨ι (w₀ : Torus F a'), ⟨w₀, w₀.2, rfl⟩, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · exact QuotientGroup.eq.mp hνw
    · exact D.mul_mem (D.inv_mem (hWD ⟨w₀, w₀.2, rfl⟩)) r₀.2
  have hRYeq : R ⊓ Y = W ⊔ A₀ := by
    apply le_antisymm
    · rintro r ⟨hrR, hrY⟩
      obtain ⟨w, hw, ha⟩ := hRY r hrR hrY
      have hr : r = w * (w⁻¹ * r) := by group
      rw [hr]
      exact Subgroup.mul_mem_sup hw ha
    · apply sup_le
      · refine le_inf hWR fun x hx => ?_
        rw [hYJN]
        exact Subgroup.mem_sup_left ((hWmem x).mp hx).1.1
      · refine le_inf hA₀R fun x hx => ?_
        rw [hYJN]
        exact Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1
  have hWA₀ : W ⊓ A₀ = ⊥ := by
    rw [eq_bot_iff, ← hWN]
    exact inf_le_inf_left _ inf_le_left
  have hcommWA : ∀ w ∈ W, ∀ x ∈ A₀, Commute w x := fun w hw x hx =>
    hcommJN w ((hWmem w).mp hw).1.1 x (Subgroup.mem_inf.mp hx).1
  obtain ⟨d, hd4, hd2, hds, hdX, -, -, -, eR', heR', -, hinvW, -⟩ :=
    hNdata.actual_lift_and_action
  have hdorder : orderOf (d : C t) = 4 := (Subgroup.orderOf_coe d).trans hd4
  have hdsq : (d : C t) ^ 2 = tInC t := congrArg Subtype.val hd2
  have hdY : (d : C t) ∈ Y := by
    change nu t (d : C t) ∈ T₀
    rw [hdX, hT₀eq]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  have hdJ : (d : C t) ∈ J := by
    have hd4' : (d : C t) ^ 2 ^ 2 = 1 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hdorder, pow_orderOf_eq_one]
    have hdY' : (d : C t) ∈ J ⊔ N t := by
      rw [← hYJN]
      exact hdY
    exact mem_of_pow_two_pow_eq_one hcommJN hNodd hdY' hd4'
  have hdinv : ∀ w ∈ W, (d : C t) * w * (d : C t)⁻¹ = w⁻¹ := by
    intro w hw
    obtain ⟨r₀, hr₀, hr₀w⟩ := hWR hw
    have hr₀' : r₀ ∈ Rs := by
      rw [hRs]
      exact hr₀
    let rr : Rs := ⟨r₀, hr₀'⟩
    have hrrY : ((rr : Ds) : C t) ∈ Y := by
      change D.subtype r₀ ∈ Y
      rw [hr₀w, hYJN]
      exact Subgroup.mem_sup_left ((hWmem w).mp hw).1.1
    obtain ⟨w₀, hw₀, -⟩ := hcoord eR' heR' rr hrrY
    have h2 := hinvW w₀
    rw [← hw₀, MulEquiv.symm_apply_apply,
      CFSG.Semidihedral.ActualFourGroupNormalizer.conjugationOnOddQuotient_mk] at h2
    have h3 : QuotientGroup.mk' N0
        (CFSG.Semidihedral.ActualFourGroupNormalizer.conjugationOnR s d rr) =
          QuotientGroup.mk' N0 rr⁻¹ := by
      apply eR'.injective
      calc eR' (QuotientGroup.mk' N0
            (CFSG.Semidihedral.ActualFourGroupNormalizer.conjugationOnR s d rr)) =
            SemidirectProduct.inl w₀⁻¹ := h2
        _ = (SemidirectProduct.inl w₀)⁻¹ := map_inv _ _
        _ = (eR' (QuotientGroup.mk' N0 rr))⁻¹ := by rw [hw₀]
        _ = eR' (QuotientGroup.mk' N0 rr)⁻¹ := (map_inv eR' _).symm
        _ = eR' (QuotientGroup.mk' N0 rr⁻¹) := congrArg eR' (map_inv _ rr).symm
    have h4 := QuotientGroup.eq.mp h3
    have h5 : (((CFSG.Semidihedral.ActualFourGroupNormalizer.conjugationOnR s d rr : Ds) :
        C t))⁻¹ * ((rr : Ds) : C t)⁻¹ ∈ N t := h4
    rw [CFSG.Semidihedral.ActualFourGroupNormalizer.conjugationOnR_value] at h5
    change ((d : C t) * D.subtype r₀ * (d : C t)⁻¹)⁻¹ * (D.subtype r₀)⁻¹ ∈ N t at h5
    rw [hr₀w] at h5
    have hdw : (d : C t) * w * (d : C t)⁻¹ ∈ W := by
      apply hconjW (d : C t) _ w hw
      rw [hds, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers _
    have h6 : ((d : C t) * w * (d : C t)⁻¹)⁻¹ * w⁻¹ ∈ W ⊓ N t :=
      Subgroup.mem_inf.mpr ⟨W.mul_mem (W.inv_mem hdw) (W.inv_mem hw), h5⟩
    rw [hWN, Subgroup.mem_bot, mul_eq_one_iff_eq_inv, inv_inv, inv_eq_iff_eq_inv] at h6
    exact h6
  exact ⟨hEinv, hECs, ⟨φ, fun x => rfl⟩, hCJcyc, hCJcard, W, hWmem, hWcyc, hWcard, hCJdecomp,
    hCJdisj, hcommt, hWN, hWR, hRYeq, hWA₀, hcommWA, (d : C t), hdJ, hdorder, hdsq, hds,
    hdinv⟩

end

end CFSG.Semidihedral.CentralKernelTorusSplit

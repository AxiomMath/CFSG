module

public import CFSG.CharacterTheory.Semidihedral.CentralKernelTorusSplit
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactorModel
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactorSupport

public section

namespace CFSG.Semidihedral.StationaryConfinement

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

variable {G : Type} [Group G]

theorem centralizer_closure_pair (t s : G) :
    Subgroup.centralizer (Subgroup.closure ({t, s} : Set G) : Set G) =
      C t ⊓ Subgroup.centralizer ({s} : Set G) := by
  rw [Subgroup.centralizer_closure]
  ext x
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, Subgroup.mem_inf]

variable [Finite G]

theorem fixed_factor_ambient_data
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap
          (nu t)).map (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (s : G) (hsC : s ∈ C t) (hs : orderOf s = 2) (hts : t ≠ s) :
    let qe := if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let Na := (N t).map (C t).subtype
    let Ya := Y.map (C t).subtype
    let Ja := J.map (C t).subtype
    let Ea := (J ⊓ N t).map (C t).subtype
    let A₀ := Na ⊓ Subgroup.centralizer ({s} : Set G)
    let D := C t ⊓ Subgroup.centralizer ({s} : Set G)
    let R := (CFSG.pPrimeCore 2 D).map D.subtype
    let V := Subgroup.closure ({t, s} : Set G)
    ∃ W : Subgroup G,
      (∀ x : G, x ∈ W ↔ x ∈ Ja ⊓ Subgroup.centralizer ({s} : Set G) ∧ Odd (orderOf x)) ∧
      IsCyclic W ∧ Nat.card W = qe / 2 ∧ W ≤ R ∧
      W ⊓ A₀ = ⊥ ∧ (∀ w ∈ W, ∀ a ∈ A₀, Commute w a) ∧ W ⊔ A₀ = R ⊓ Ya ∧
      (∀ x ∈ Ea, s * x * s⁻¹ = x⁻¹) ∧
      (∃ d ∈ Ja, orderOf d = 4 ∧ d ^ 2 = t ∧ d * s * d⁻¹ = t * s ∧
        ∀ w ∈ W, d * w * d⁻¹ = w⁻¹) ∧
      Subgroup.centralizer (V : Set G) = V ⊔ R ∧
      ⁅R, R⁆ ≤ Ya ∧ (∀ x ∈ R, (∀ y ∈ ⁅R, R⁆, x * y = y * x) → x ∈ Ya) := by
  intro qe T₀ Y H₀ J Na Ya Ja Ea A₀ D R V
  classical
  let sC : C t := ⟨s, hsC⟩
  have hsC2 : orderOf sC = 2 := (Subgroup.orderOf_coe sC).symm.trans hs
  have hst : sC ≠ tInC t := fun h => hts (congrArg Subtype.val h).symm
  let ι := (C t).subtype
  have hιinj : Function.Injective ι := (C t).subtype_injective
  obtain ⟨hEinv, -, -, -, -, W₀, hW₀mem, hW₀cyc, hW₀card, -, -, -, -, hW₀R, hRY, hW₀A, hW₀comm,
      d, hdJ, hd4, hd2, hds, hdinv⟩ :=
    CentralKernelTorusSplit.actual_central_odd_kernel_is_inverted_and_fixed_layer_torus_splits
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel sC hsC2 hst hcov
  obtain ⟨hRRint, hXint⟩ := fixed_core_derived_centralizer_le_layer n hn S0 f0 hG t ht hnonab
    hcentral hnc p f hp hpodd hf hq hmodel hcov sC hsC2 hst
  obtain ⟨-, F, hF, hFfin, A, a, -, -, -, -, -, -, -, -, -, -, -, hPsiex⟩ :=
    ActualFourGroupCentralizer.actual_simple_layer_four_group_centralizer_odd_core
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, -, -, hCdata, -, hDamb, hVamb, -⟩ := hPsiex sC hsC2 hst
  set Dint := Subgroup.centralizer ({sC} : Set (C t)) with hDint
  set Rint := (CFSG.pPrimeCore 2 Dint).map Dint.subtype with hRint
  set A₀int : Subgroup (C t) := N t ⊓ Subgroup.centralizer ({sC} : Set (C t)) with hA₀int
  have hDmap : Dint.map ι = D := hDamb
  have hRmap : Rint.map ι = R := by
    change ((CFSG.pPrimeCore 2 Dint).map Dint.subtype).map (C t).subtype =
      (CFSG.pPrimeCore 2 ↥(C t ⊓ Subgroup.centralizer ({s} : Set G))).map
        (C t ⊓ Subgroup.centralizer ({s} : Set G)).subtype
    rw [← hDamb]
    exact (ambient_core_of_subgroup_map (C t) Dint).symm
  have hA₀map : A₀int.map ι = A₀ := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyN, hys⟩, rfl⟩
      refine ⟨⟨y, hyN, rfl⟩, ?_⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hys)
    · rintro ⟨⟨y, hyN, rfl⟩, hys⟩
      refine ⟨y, ⟨hyN, ?_⟩, rfl⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hys)
  set W := W₀.map ι with hWdef
  refine ⟨W, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨⟨hyJ, hys⟩, hyodd⟩ := (hW₀mem y).mp hy
      refine ⟨⟨⟨y, hyJ, rfl⟩, ?_⟩, ?_⟩
      · apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hys)
      · rw [show orderOf (ι y) = orderOf y from Subgroup.orderOf_coe y]
        exact hyodd
    · rintro ⟨⟨⟨y, hyJ, rfl⟩, hys⟩, hyodd⟩
      refine ⟨y, (hW₀mem y).mpr ⟨⟨hyJ, ?_⟩, ?_⟩, rfl⟩
      · apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hys)
      · rwa [show orderOf (ι y) = orderOf y from Subgroup.orderOf_coe y] at hyodd
  · let e := W₀.equivMapOfInjective ι hιinj
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  · rw [Subgroup.card_map_of_injective hιinj]
    exact hW₀card
  · rw [← hRmap]
    exact Subgroup.map_mono hW₀R
  · rw [← hA₀map, ← Subgroup.map_inf_eq _ _ ι hιinj, hW₀A, Subgroup.map_bot]
  · rintro _ ⟨w, hw, rfl⟩ _ ha
    rw [← hA₀map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact congrArg Subtype.val (hW₀comm w hw b hb)
  · rw [← hA₀map, ← Subgroup.map_sup, ← hRY, Subgroup.map_inf_eq _ _ ι hιinj, hRmap]
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hEinv x hx)
  · refine ⟨(d : G), ⟨d, hdJ, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [← hd4]
      exact Subgroup.orderOf_coe d
    · exact congrArg Subtype.val hd2
    · exact congrArg Subtype.val hds
    · rintro _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (hdinv w hw)
  ·
    have hjoin : (KleinFourOddKernel.fourSubgroup (tInC t) sC).subgroupOf Dint ⊔
        CFSG.piCore KleinFourOddKernel.oddPrimes Dint = ⊤ := hCdata.lifted.generated_join
    have hRs : CFSG.piCore KleinFourOddKernel.oddPrimes Dint = CFSG.pPrimeCore 2 Dint :=
      KleinFourOddKernel.piCore_odd_eq_pPrimeCore
    rw [hRs] at hjoin
    have hfour : KleinFourOddKernel.fourSubgroup (tInC t) sC ≤ Dint := by
      apply sup_le_iff.mpr
      constructor
      · rw [Subgroup.zpowers_le]
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact (Subgroup.mem_center_iff.mp (tInC_central t) sC).symm
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hDint : Dint = KleinFourOddKernel.fourSubgroup (tInC t) sC ⊔ Rint := by
      have h := congrArg (Subgroup.map Dint.subtype) hjoin
      rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hfour] at h
      exact h.symm
    have hVamb' : (KleinFourOddKernel.fourSubgroup (tInC t) sC).map ι = V := by
      rw [show V = Subgroup.zpowers t ⊔ Subgroup.zpowers s from
        StationaryOddLocalization.closure_pair_eq_zpowers_sup t s]
      exact hVamb
    rw [centralizer_closure_pair, show C t ⊓ Subgroup.centralizer ({s} : Set G) = D from rfl,
      ← hDmap, hDint, Subgroup.map_sup, hVamb', hRmap]
  · rw [← hRmap, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hRRint
  · intro x hxR hxc
    rw [← hRmap] at hxR
    obtain ⟨x', hx'R, rfl⟩ := hxR
    refine ⟨x', ?_, rfl⟩
    apply hXint x' hx'R
    intro y hy
    have hyR : ι y ∈ ⁅R, R⁆ := by
      rw [← hRmap, ← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem ι hy
    have h := hxc (ι y) hyR
    apply hιinj
    rw [map_mul, map_mul]
    exact h

end CFSG.Semidihedral.StationaryConfinement

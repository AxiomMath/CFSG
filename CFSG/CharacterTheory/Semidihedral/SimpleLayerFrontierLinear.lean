module

public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierBrauer
public import CFSG.CharacterTheory.Semidihedral.EscapingLocalEigensubgroups
public import CFSG.CharacterTheory.Semidihedral.Local.SplitActualLayer
public import CFSG.CharacterTheory.Semidihedral.FieldInterface

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.SimpleLayerFrontier

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.Principal

@[expose] def SevenNineCoreHypothesis : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) →
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
      (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → (p ^ f = 7 ∨ p ^ f = 9) →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
      EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G) →
    let s₀ : G := fS (s n)
    let e : ℤ := if p ^ f = 7 then -1 else 1
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Na := (N t).map (C t).subtype
    let Ja := J.map (C t).subtype
    let A₀ := Na ⊓ Subgroup.centralizer ({s₀} : Set G)
    let JS := Ja ⊔ Subgroup.zpowers s₀
    let a₀ := Nat.card A₀
    n = 5 ∧ (∀ x ∈ Na, s₀ * x * s₀⁻¹ = x⁻¹ → x = 1) ∧ E = ⊥ ∧ Na = A₀ ∧ IsCyclic Na ∧
      Nat.card Na = a₀ ∧ (a₀ : ℤ) ∣ ((p ^ f : ℕ) + e) / 2 ∧
      (p ^ f = 7 → a₀ = 1 ∨ a₀ = 3) ∧ (p ^ f = 9 → a₀ = 1 ∨ a₀ = 5) ∧
      (∃ φ : J ≃* T₀, ∀ x : J, (φ x : H t) = nu t x) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (T₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      (Y = J ⊔ N t ∧ J ⊓ N t = ⊥ ∧ ∀ x ∈ J, ∀ y ∈ N t, Commute x y) ∧
      (JS ⊔ Na = C t ∧ JS ⊓ Na = ⊥ ∧ ∀ x ∈ JS, ∀ y ∈ Na, Commute x y) ∧
      N t ≤ Subgroup.center (C t) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (a : Fˣ), Nat.card F = p ^ f ∧
        ¬ IsSquare a ∧ Nonempty (JS ≃* MatrixCoverData.M F a)) ∧
      (p ^ f = 7 → Nat.card G = 2328480 * a₀ ∨ Nat.card G = 1876896 * a₀) ∧
      (p ^ f = 9 → Nat.card G = 8514720 * a₀ ∨ Nat.card G = 6441120 * a₀ ∨
        Nat.card G = 7236000 * a₀)

@[expose] def FieldFactorOneHypothesis : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) →
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
      (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 < p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
      EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n)) →
      (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2 →
      (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} ≠ ⊥ →
    let s₀ : G := fS (s n)
    let Na : Subgroup G := (N t).map (C t).subtype
    let A₀ : Subgroup G := Na ⊓ Subgroup.centralizer {s₀}
    let qe : ℕ := if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1
    3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card ↥(C t ⊓ Subgroup.centralizer {s₀})) : ℤ) ≤
      padicValNat p (Nat.card G) ∧
    (∀ x : G, x ∈ Na → s₀ * x * s₀⁻¹ = x⁻¹ → x = 1) ∧ Na = A₀ ∧
    N t ≠ ⊥ ∧ IsCyclic (N t) ∧ Nat.card (N t) ∣ qe / 2 ∧ ¬ p ∣ Nat.card (N t)

theorem nonempty_mulEquiv_prod_of_internal {G : Type*} [Group G] (A B X : Subgroup G)
    (hsup : A ⊔ B = X) (hinf : A ⊓ B = ⊥) (hcomm : ∀ x ∈ A, ∀ y ∈ B, Commute x y) :
    Nonempty (X ≃* A × B) := by
  have hc : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hc) :=
    Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hinf)
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hc).range = X := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hsup]
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem eq_top_of_index_two_le {G : Type*} [Group G] {H K : Subgroup G} (hH : H.index = 2)
    (hHK : H ≤ K) {x : G} (hxK : x ∈ K) (hxH : x ∉ H) : K = ⊤ := by
  have hmul := Subgroup.relIndex_mul_index hHK
  rw [hH] at hmul
  have hdvd : K.index ∣ 2 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    rw [h2] at hmul
    have hrel : H.relIndex K = 1 := by omega
    exact hxH (Subgroup.relIndex_eq_one.mp hrel hxK)

theorem linear_branch_seven
    (hSN : SevenNineCoreHypothesis)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq7 : p ^ f = 7)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  obtain ⟨-, ht2, -, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨-, -, -, -, hcyc, hcard, hdvd, -, -, -, -, -, ⟨hsup, hinf, hcomm⟩, -,
      ⟨F, hF, hFfin, a, hFcard, ha, ⟨eJS⟩⟩, -, -⟩ :=
    hSN G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
      (Or.inl hq7) hmodel hcov
  obtain ⟨eC⟩ := nonempty_mulEquiv_prod_of_internal _ _ _ hsup hinf hcomm
  have : IsCyclic ((N t).map (C t).subtype) := hcyc
  have hK : Nat.card ((N t).map (C t).subtype) ∣ (p ^ f - 1) / 2 := by
    rw [hcard]
    have h3 : ((p ^ f : ℕ) + (if p ^ f = 7 then (-1 : ℤ) else 1)) / 2 = 3 := by
      rw [hq7]
      norm_num
    rw [h3] at hdvd
    rw [hq7]
    exact_mod_cast hdvd
  exact stated_classical_model_psl_three_of_centralizer_prod p f hp (by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two)
    hf ⟨by omega, by omega⟩ G hGnonab F hFcard a ha ((N t).map (C t).subtype) hK t ht2
    ((eC.trans (eJS.prodCongr (MulEquiv.refl _))).trans MulEquiv.prodComm)

theorem noncentral_involution_not_mem_layer_preimage {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (sC : C t) (hs : orderOf sC = 2) (hst : sC ≠ tInC t) :
    sC ∉ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) := by
  intro hsY
  obtain ⟨-, hJindex, -, -, hunique, -, -⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  have hLJ : CFSG.generalizedFitting (Gamma t) ≤ J t := simple_le_index_two _ _ hJindex hnonab
  have hsJ : nu t sC ∈ (J t).comap (barKappa t) := hLJ hsY
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2))
  have hsN : sC ∉ N t := by
    intro h
    have hdvd : orderOf sC ∣ Nat.card (N t) := by
      rw [← Subgroup.orderOf_mk sC h]
      exact orderOf_dvd_natCard _
    rw [hs] at hdvd
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)
  have hord : orderOf (⟨nu t sC, hsJ⟩ : (J t).comap (barKappa t)) = 2 := by
    rw [Subgroup.orderOf_mk]
    apply orderOf_eq_prime
    · have hs1 : sC ^ 2 = 1 := by
        rw [← hs]
        exact pow_orderOf_eq_one sC
      rw [← map_pow, hs1, map_one]
    · intro h1
      apply hsN
      have : sC ∈ (nu t).ker := h1
      rwa [QuotientGroup.ker_mk'] at this
  have heq : nu t sC = nu t (tInC t) := hunique _ hord
  have hmem : sC * (tInC t)⁻¹ ∈ N t := by
    rw [← QuotientGroup.ker_mk' (N t)]
    change nu t (sC * (tInC t)⁻¹) = 1
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  have hcomm : Commute sC (tInC t) := by
    have := tInC_central t
    exact (Subgroup.mem_center_iff.mp this) sC
  have htC2 : orderOf (tInC t) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hs1 : sC ^ 2 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one sC
  have ht1 : tInC t ^ 2 = 1 := by
    rw [← htC2]
    exact pow_orderOf_eq_one _
  have hsq : (sC * (tInC t)⁻¹) ^ 2 = 1 := by
    rw [hcomm.inv_right.mul_pow, hs1, inv_pow, ht1, inv_one, one_mul]
  have hne : sC * (tInC t)⁻¹ ≠ 1 := by
    intro h
    exact hst (mul_inv_eq_one.mp h)
  have hord2 : orderOf (sC * (tInC t)⁻¹) = 2 := orderOf_eq_prime hsq hne
  have hdvd : orderOf (sC * (tInC t)⁻¹) ∣ Nat.card (N t) := by
    rw [← Subgroup.orderOf_mk _ hmem]
    exact orderOf_dvd_natCard _
  rw [hord2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)

theorem field_group_card_eq_one_of_index_two {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (p f : ℕ) (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (data : ActualMatrixData t n p f F A rho)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    Nat.card A = 1 := by
  obtain ⟨-, hJindex, -, -, -, -, -⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  have hLJ : CFSG.generalizedFitting (Gamma t) ≤ J t := simple_le_index_two _ _ hJindex hnonab
  obtain ⟨-, -, -, hA⟩ := data.compatible_layer
  set T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  set Jb := (J t).comap (barKappa t)
  have hT₀J : T₀ ≤ Jb := Subgroup.comap_mono hLJ
  have hT₀ : T₀.index = 2 := by
    have h := hY
    rwa [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective (N t))] at h
  have hJb : Jb.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ (barKappa_surjective t), hJindex]
  have hmul := Subgroup.relIndex_mul_index hT₀J
  rw [hT₀, hJb] at hmul
  have hrel : T₀.relIndex Jb = 1 := by omega
  rw [← hA]
  exact hrel

@[expose] noncomputable def semidirectProductTrivialRightEquiv {N K : Type*} [Group N] [Group K]
    [Subsingleton K] (φ : K →* MulAut N) : N ≃* N ⋊[φ] K :=
  MulEquiv.ofBijective (SemidirectProduct.inl : N →* N ⋊[φ] K)
    ⟨SemidirectProduct.inl_injective, fun x => ⟨x.left, by
      refine SemidirectProduct.ext ?_ ?_
      · simp
      · exact Subsingleton.elim _ _⟩⟩

theorem linear_branch_field_one
    (hFO : FieldFactorOneHypothesis)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq3 : p ^ f % 4 = 3)
    (hq5 : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n)))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} ≠ ⊥) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨-, -, hNA, -, hNcyc, hNdvd, -⟩ :=
    hFO G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq5 hmodel
      hcov hY hA₀
  have hcover := EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage
    t (fS (s n) : G) hcov
  obtain ⟨⟨-, -, hJN, -, -⟩, hJnormal, -, hYJN, hne9, -⟩ :=
    Local.all_local_prime_covers_split_actual_layer_except_central_three_at_nine n hn S fS hG t ht2
      hnonab hcentral hnc p f hp hpodd hf hq5.le hmodel (Or.inl hcover)
  obtain ⟨hE, -, -, -⟩ := hne9 (by omega)
  set T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) with hT₀
  set Y := T₀.comap (nu t) with hYdef
  set H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
  set J := (CFSG.perfectResidual H₀).map H₀.subtype with hJdef
  let sC : C t := ⟨(fS (s n) : G), hsC⟩
  have hsC2 : orderOf sC = 2 := by
    rw [← hs2, ← Subgroup.orderOf_coe]
  have hsCt : sC ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  have hsY : sC ∉ Y :=
    noncentral_involution_not_mem_layer_preimage n hn S fS hG t ht2 hnonab sC hsC2 hsCt
  have hsN : ∀ y ∈ N t, Commute sC y := by
    intro y hy
    have hyNa : (y : G) ∈ (N t).map (C t).subtype := ⟨y, hy, rfl⟩
    rw [hNA] at hyNa
    have hyc := Subgroup.mem_centralizer_singleton_iff.mp hyNa.2
    exact Subtype.ext hyc.symm
  have hJN' : J ≤ Subgroup.centralizer (N t : Set (C t)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN
  set JS := J ⊔ Subgroup.zpowers sC with hJS
  have hJS_cent : JS ≤ Subgroup.centralizer (N t : Set (C t)) := by
    refine sup_le hJN' ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hsN y hy).symm.eq)
  have hcomm : ∀ x ∈ JS, ∀ y ∈ N t, Commute x y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hJS_cent hx) y hy).symm
  have hsup : JS ⊔ N t = ⊤ := by
    apply eq_top_of_index_two_le hY (x := sC)
    · rw [hYJN]
      exact sup_le_sup_right le_sup_left _
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers sC))
    · exact hsY
  have hzY : Subgroup.zpowers sC ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxz, hxY⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have hk : sC ^ k = sC ^ (k % 2) := by
      have h := (zpow_mod_orderOf sC k).symm
      rw [hsC2] at h
      exact_mod_cast h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [hk, h0, zpow_zero]
      exact Subgroup.one_mem _
    · exfalso
      rw [hk, h1, zpow_one] at hxY
      exact hsY hxY
  have hinf : JS ⊓ N t = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxJS, hxN⟩
    have hxset : x ∈ (J : Set (C t)) * (Subgroup.zpowers sC : Set (C t)) := by
      rw [← Subgroup.normal_mul J (Subgroup.zpowers sC)]
      exact hxJS
    obtain ⟨j, hj, z, hz, hjz⟩ := hxset
    simp only at hjz
    subst hjz
    have hzY' : z ∈ Y := by
      have : z = j⁻¹ * (j * z) := by group
      rw [this, hYJN]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (J.inv_mem hj))
        (Subgroup.mem_sup_right hxN)
    have hz1 : z = 1 := by
      have : z ∈ Subgroup.zpowers sC ⊓ Y := ⟨hz, hzY'⟩
      rw [hzY] at this
      exact this
    subst hz1
    rw [mul_one] at hxN ⊢
    have : j ∈ J ⊓ N t := ⟨hj, hxN⟩
    rw [hE] at this
    exact this
  obtain ⟨eC⟩ := nonempty_mulEquiv_prod_of_internal JS (N t) ⊤ hsup hinf hcomm
  let νJS : JS →* H t := (nu t).comp JS.subtype
  have hνJS : Function.Bijective νJS := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x hx
      have hxN : (x : C t) ∈ N t := by
        have : (x : C t) ∈ (nu t).ker := hx
        rwa [QuotientGroup.ker_mk'] at this
      have : (x : C t) ∈ JS ⊓ N t := ⟨x.2, hxN⟩
      rw [hinf] at this
      exact Subtype.ext this
    · intro y
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (N t) y
      have hc : c ∈ (JS : Set (C t)) * (N t : Set (C t)) := by
        rw [← Subgroup.mul_normal JS (N t), hsup]
        trivial
      obtain ⟨x, hx, m, hm, rfl⟩ := hc
      refine ⟨⟨x, hx⟩, ?_⟩
      change nu t x = nu t (x * m)
      rw [map_mul]
      have : nu t m = 1 := by
        change m ∈ (nu t).ker
        rwa [QuotientGroup.ker_mk']
      rw [this, mul_one]
  let eJS : JS ≃* H t := MulEquiv.ofBijective νJS hνJS
  obtain ⟨F, hFfield, hFfin, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  have hA1 : Nat.card A = 1 :=
    field_group_card_eq_one_of_index_two n hn S fS hG t ht2 hnonab p f F A rho data hY
  have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA1).1
  have hfixedodd : Odd (Nat.card (MatrixCover.FixedField F A)) := by
    rw [data.fixed_field_card]
    exact hpodd.pow
  obtain ⟨a₀, ha₀⟩ : ∃ a : (MatrixCover.FixedField F A)ˣ, ¬ IsSquare a := by
    have := Fintype.ofFinite (MatrixCover.FixedField F A)
    have hchar : ringChar (MatrixCover.FixedField F A) ≠ 2 := by
      intro h2
      have := FiniteField.even_card_iff_char_two.mp h2
      rw [← Nat.card_eq_fintype_card] at this
      exact (Nat.not_even_iff_odd.mpr hfixedodd) (Nat.even_iff.mpr this)
    obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare hchar
    have hb0 : b ≠ 0 := fun h => hb (h ▸ ⟨0, by rw [mul_zero]⟩)
    refine ⟨Units.mk0 b hb0, ?_⟩
    rw [SemilinearOuterQuotient.isSquare_unit_iff]
    exact hb
  obtain ⟨hnsq, phi, -⟩ := data.every_coefficient a₀ ha₀
  let eM : MatrixCoverData.M F (MatrixCover.fixedUnit F A a₀) ≃* H t :=
    (semidirectProductTrivialRightEquiv (MatrixCover.matrixFieldAction F A a₀)).trans phi
  have hNdvd' : Nat.card (N t) ∣ (p ^ f - 1) / 2 := by
    have : (if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1) = p ^ f - 1 := by
      split_ifs with h
      · omega
      · rfl
    rw [this] at hNdvd
    exact hNdvd
  have : IsCyclic (N t) := hNcyc
  have hcard : Nat.card F = p ^ f := data.field_card
  exact stated_classical_model_psl_three_of_centralizer_prod p f hp (by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two)
    hf ⟨hq3, by omega⟩ G hGnonab F hcard (MatrixCover.fixedUnit F A a₀) hnsq (N t) hNdvd' t ht2
    (((Subgroup.topEquiv.symm.trans eC).trans ((eJS.trans eM.symm).prodCongr
      (MulEquiv.refl _))).trans MulEquiv.prodComm)

theorem linear_branch_of_stationary_covers
    (hSN : SevenNineCoreHypothesis)
    (hFO : FieldFactorOneHypothesis)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hbranch : p ^ f = 7 ∨
      ((((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2 ∧
        (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} ≠ ⊥)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  have hq5 : 5 ≤ p ^ f := FieldInterface.psl_two_field_size_ge_five hp (by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two) hf hmodel
  by_cases hq7 : p ^ f = 7
  · exact linear_branch_seven hSN G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc
      p f hp hpodd hf hq7 hmodel hcov
  · obtain ⟨hY, hA₀⟩ := hbranch.resolve_left hq7
    have hgt : 5 < p ^ f := by omega
    exact linear_branch_field_one hFO G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc
      p f hp hpodd hf hq3 hgt hmodel hcov hY hA₀

end CFSG.Semidihedral.SimpleLayerFrontier

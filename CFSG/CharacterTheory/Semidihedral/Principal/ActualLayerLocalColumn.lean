module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalEvenFourierColumn

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.TwoRankLowerBound.Helpers CFSG.GorensteinWalter

universe u

variable {G : Type u} [Group G]

theorem actualLayer_exists_centralizer_presentation (n : ℕ) (hn : 4 ≤ n) {t : G}
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hf : ((f (r n) ^ (2 ^ (n - 2)) : S) : G) = t) :
    ∃ (P : Sylow 2 (C t)) (e : SemidihedralGroup n ≃* (P : Subgroup (C t))),
      (∀ x, ((e x : C t) : G) = (f x : G)) ∧ (e (r n) : C t) ^ (modulus n / 2) = tInC t := by
  have hz : (f (z n) : G) = t := by
    simpa only [z, half, map_pow] using hf
  have hle : (S : Subgroup G) ≤ C t := by
    have hzc : f (z n) ∈ Subgroup.center S := by
      rw [← Subgroup.map_center_eq f]
      exact ⟨z n, z_mem_center n hn, rfl⟩
    intro g hg
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← hz]
    exact congrArg (fun x : S => (x : G)) (Subgroup.mem_center_iff.mp hzc ⟨g, hg⟩)
  refine ⟨S.subtype hle, f.trans (Subgroup.subgroupOfEquivOfLe hle).symm, fun x => rfl, ?_⟩
  apply Subtype.ext
  change ((f (r n) : G)) ^ (modulus n / 2) = t
  rw [← hf, show modulus n / 2 = 2 ^ (n - 2) from by
    rw [modulus_eq_two_mul_half (by omega), half]
    omega]
  simp

theorem actualLayer_gamma_two_power_mem_linear {F : Type} [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (hd : Odd (Nat.card A)) (g : OddFieldLift.Gamma F A) (k : ℕ)
    (hg : g ^ (2 ^ k) = 1) : g ∈ OddFieldLift.gammaLinear F A := by
  let x := (OddFieldLift.gammaSemidirectEquiv F A).symm g
  have hx : x ^ (2 ^ k) = 1 := by
    change ((OddFieldLift.gammaSemidirectEquiv F A).symm g) ^ (2 ^ k) = 1
    rw [← map_pow, hg, map_one]
  have hr : x.right ^ (2 ^ k) = 1 := by
    change (SemidirectProduct.rightHom x) ^ (2 ^ k) = 1
    rw [← map_pow, hx, map_one]
  have hrc := pow_card_eq_one' (x := x.right)
  have hodd : Odd (Nat.card (OddFieldLift.gammaField F A)) := by
    rw [OddFieldLift.gammaField_card]
    exact hd
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (OddFieldLift.gammaField F A)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hr1 : x.right = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hr, hrc⟩
  have hprod : g = (x.left : OddFieldLift.Gamma F A) * (x.right : OddFieldLift.Gamma F A) := by
    calc
      g = OddFieldLift.gammaSemidirectEquiv F A x :=
        ((OddFieldLift.gammaSemidirectEquiv F A).apply_symm_apply g).symm
      _ = _ := SemilinearOddExtensions.internalSemidirectEquiv_apply _ _ _ x
  rw [hr1, Subgroup.coe_one, mul_one] at hprod
  rw [hprod]
  exact x.left.property

theorem actualLayer_localAction_mem_coordinateD {t : G} {n p f : ℕ} {F : Type} [Field F]
    [Finite F] {A : Subgroup (F ≃+* F)} {rho : Gamma t →* coordinateE F}
    (data : ActualMatrixData t n p f F A rho) (c : C t) (k : ℕ) (hc : c ^ (2 ^ k) = 1) :
    localAction F rho c ∈ coordinateD F := by
  let g : OddFieldLift.Gamma F A := ⟨rho (kappa t c), data.full_image ▸ ⟨kappa t c, rfl⟩⟩
  have hg : g ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    change rho (kappa t c) ^ (2 ^ k) = 1
    rw [← map_pow, ← map_pow, hc, map_one, map_one]
  exact actualLayer_gamma_two_power_mem_linear A data.field_group_odd g k hg

theorem actualLayer_sq_mem_N_of_mem_NZ {t : G} (ht : orderOf t = 2) {x : C t} (hx : x ∈ NZ t) :
    x ^ 2 ∈ N t := by
  have : (N t).Normal := CFSG.pPrimeCore_normal
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hcomm : Commute a (tInC t ^ k) :=
    (show Commute a (tInC t) from Subgroup.mem_center_iff.mp (tInC_central t) a).zpow_right k
  have ht2 : tInC t ^ 2 = 1 := by
    have : orderOf (tInC t) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact ht
    rw [← this, pow_orderOf_eq_one]
  have htk : (tInC t ^ k) ^ 2 = 1 := by
    have h : (tInC t ^ k) ^ 2 = (tInC t ^ 2) ^ k := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast (tInC t) 2, ← zpow_mul, mul_comm]
    rw [h, ht2, one_zpow]
  rw [hcomm.mul_pow, htk, mul_one]
  exact pow_mem ha 2

theorem actualLayer_orderOf_kappa_rotation [Finite G] {t : G} (ht : orderOf t = 2) {n : ℕ}
    (hn : 4 ≤ n) {ρ : C t} (hρt : ρ ^ (modulus n / 2) = tInC t) :
    orderOf (kappa t ρ) = modulus n / 2 := by
  obtain ⟨hM, -, hK2, hhalf⟩ := modulus_eq_four_mul hn
  have hM2 : modulus n / 2 = 2 ^ (n - 3 + 1) := by rw [pow_succ]; omega
  have hfin : kappa t ρ ^ 2 ^ (n - 3 + 1) = 1 := by
    rw [← hM2, ← map_pow, hρt]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hnot : ¬ kappa t ρ ^ 2 ^ (n - 3) = 1 := by
    intro h
    rw [← map_pow] at h
    have hmem : ρ ^ 2 ^ (n - 3) ∈ NZ t := by
      rw [← QuotientGroup.ker_mk' (NZ t)]
      exact MonoidHom.mem_ker.mpr h
    have hsq := actualLayer_sq_mem_N_of_mem_NZ ht hmem
    rw [← pow_mul, ← pow_succ, ← hM2, hρt] at hsq
    have hdvd : orderOf (tInC t) ∣ Nat.card (N t) := Subgroup.orderOf_dvd_natCard _ hsq
    have ho : orderOf (tInC t) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact ht
    rw [ho] at hdvd
    have hcop : Nat.Coprime 2 (Nat.card (N t)) := CFSG.pPrimeCore_coprime_card
    exact absurd (Nat.dvd_one.mp (Nat.Coprime.dvd_of_dvd_mul_left hcop
      (by rw [mul_one]; exact hdvd))) (by norm_num)
  rw [orderOf_eq_prime_pow hnot hfin, hM2]

theorem actualLayer_orderOf_localAction {t : G} {n p f : ℕ} {F : Type} [Field F] [Finite F]
    {A : Subgroup (F ≃+* F)} {rho : Gamma t →* coordinateE F}
    (data : ActualMatrixData t n p f F A rho) (c : C t) :
    orderOf (localAction F rho c) = orderOf (kappa t c) := by
  change orderOf ((coordinateE F).subtype (rho (kappa t c))) = _
  rw [orderOf_injective _ (coordinateE F).subtype_injective,
    orderOf_injective _ data.faithful]

theorem actualLayer_ringChar_ne_two {F : Type} [Field F] [Fintype F] (hF : Odd (Nat.card F)) :
    ringChar F ≠ 2 := by
  intro h
  have hcardEven := FiniteField.even_card_iff_char_two.mp h
  rw [← Nat.card_eq_fintype_card] at hcardEven
  obtain ⟨k, hk⟩ := hF
  omega

theorem actualLayer_localPhi_rotation [Finite G] {t : G} (ht : orderOf t = 2) {n p f : ℕ}
    (hn : 4 ≤ n) {F : Type} [Field F] [Fintype F] {A : Subgroup (F ≃+* F)}
    {rho : Gamma t →* coordinateE F} (data : ActualMatrixData t n p f F A rho)
    (hF : Odd (Nat.card F)) {ρ : C t} (hρ : orderOf ρ = modulus n)
    (hρt : ρ ^ (modulus n / 2) = tInC t) (j : ℤ) (hj0 : ¬ j ≡ 0 [ZMOD modulus n])
    (hj1 : ¬ j ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    localPhi F rho (ρ ^ j) = localPhi F rho (ρ ^ (modulus n / 4)) := by
  obtain ⟨hM, -, hK2, hhalf⟩ := modulus_eq_four_mul hn
  set g := localAction F rho ρ with hg
  have hgD : g ∈ coordinateD F := by
    refine actualLayer_localAction_mem_coordinateD data ρ (n - 1) ?_
    rw [← modulus, ← hρ, pow_orderOf_eq_one]
  have hgord : orderOf g = modulus n / 2 := by
    rw [hg, actualLayer_orderOf_localAction data, actualLayer_orderOf_kappa_rotation ht hn hρt]
  set M' := modulus n / 2 with hM'
  have hM'pos : (0 : ℤ) < M' := by omega
  have hmod0 : 0 ≤ j % (M' : ℤ) := Int.emod_nonneg _ hM'pos.ne'
  have hmodlt : j % (M' : ℤ) < M' := Int.emod_lt_of_pos _ hM'pos
  have hMM : (modulus n : ℤ) = 2 * (M' : ℤ) := by
    rw [hM']
    push_cast
    omega
  have hmodne : j % (M' : ℤ) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · apply hj0
      rw [Int.modEq_iff_dvd]
      exact ⟨-m, by rw [hk, hm, hMM]; ring⟩
    · apply hj1
      rw [Int.modEq_iff_dvd]
      exact ⟨-m, by rw [hk, hm, hMM]; ring⟩
  set j' := (j % (M' : ℤ)).toNat with hj'
  have hj'eq : ((j' : ℕ) : ℤ) = j % (M' : ℤ) := Int.toNat_of_nonneg hmod0
  have hgj : localAction F rho (ρ ^ j) = g ^ j' := by
    rw [map_zpow, ← zpow_mod_orderOf, hgord, ← hj'eq, zpow_natCast]
  have hgq : localAction F rho (ρ ^ (modulus n / 4)) = g ^ (M' / 2) := by
    rw [map_pow, show M' / 2 = modulus n / 4 by omega]
  have hcard := card_fixed_pow_eq_of_two_power_order (actualLayer_ringChar_ne_two hF) hgD
    ⟨n - 2, by omega⟩ (by omega) hgord j' (by omega) (by omega)
  rw [localPhi, localPhi, hgj, hgq, hcard]

theorem actualLayer_not_mem_K_of_orderOf [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0) (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G)
    (ht : orderOf t = 2) (x : C t) (hx : orderOf x = modulus n) : x ∉ K t := by
  obtain ⟨S, f, hcenter⟩ := InvolutionFusion.exists_centered_semidihedral_sylow
    n hn S0 f0 hG t ht
  have hcenter' : CentralizerResidual.centeredInvolution n S f = t := hcenter
  subst hcenter'
  intro hxK
  obtain ⟨T, hT⟩ := CentralizerResidual.oddResidual_sylow n hn S f hG
  have hQK := CentralizerResidual.centralizerQuaternion_le_oddResidual n hn S f hG
  let y : CentralizerResidual.oddResidual n S f := ⟨x, hxK⟩
  have hy : orderOf y = modulus n := (Subgroup.orderOf_coe y).symm.trans hx
  have h2 : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := n - 1) (by rw [Nat.card_zpowers, hy, modulus])
  obtain ⟨T', hT'⟩ := h2.exists_le_sylow
  let y' : (T' : Subgroup (CentralizerResidual.oddResidual n S f)) :=
    ⟨y, hT' (Subgroup.mem_zpowers y)⟩
  have hy' : orderOf y' = modulus n := (Subgroup.orderOf_coe y').symm.trans hy
  let φ : (T' : Subgroup (CentralizerResidual.oddResidual n S f)) ≃*
      QuaternionGroup (2 ^ (n - 3)) :=
    (Sylow.equiv T' T).trans ((MulEquiv.subgroupCongr hT).trans
      ((Subgroup.subgroupOfEquivOfLe hQK).trans
        (CentralizerResidual.centralizerQuaternionEquiv n hn S f).symm))
  have hdvd := Monoid.order_dvd_exponent (φ y')
  rw [MulEquiv.orderOf_eq, hy', QuaternionGroup.exponent] at hdvd
  obtain ⟨hM, hKeven, hK2, -⟩ := modulus_eq_four_mul hn
  have hlcm : lcm (2 ^ (n - 3)) 2 = 2 ^ (n - 3) := Nat.lcm_eq_left (even_iff_two_dvd.mp hKeven)
  rw [hlcm] at hdvd
  have := Nat.le_of_dvd (by positivity) hdvd
  omega

theorem actualLayer_localEpsilon_cast (F : Type) :
    (((if Nat.card F % 4 = 1 then 1 else -1 : ℤ)) : ℂ) = localEpsilon F := by
  unfold localEpsilon
  split_ifs <;> simp

theorem actual_layer_local_principal_column [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0) (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G)
    (ht : orderOf t = 2) (F : Type) [Field F] [Fintype F] (A : Subgroup (F ≃+* F))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (rho : Gamma t →* coordinateE F) (data : ActualMatrixData t n p f F A rho)
    [Fintype (C t)] (basis : FiniteIrreducibleCharacterBasis (C t))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (cdata : ActualCharacterData F rho (p ^ f) basis ideal principal)
    (ldelta lphi ldeltaPhi : basis.index)
    (hdelta : ∀ c, (basis.representation ldelta).character c = localDelta F rho c)
    (hphi : ∀ c, (basis.representation lphi).character c = localPhi F rho c)
    (hdeltaPhi : ∀ c, (basis.representation ldeltaPhi).character c =
      localDelta F rho c * localPhi F rho c)
    (P : Sylow 2 (C t)) (e : SemidihedralGroup n ≃* (P : Subgroup (C t)))
    (he : (e (r n) : C t) ^ (modulus n / 2) = tInC t) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : C t := e (r n)
    let σ : C t := e (s n)
    let M : ℕ := modulus n
    let q : ℕ := p ^ f
    let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
    let χ : basis.index → C t → ℂ := fun c => (basis.representation c).character
    let h : Subgroup.zpowers ρ → ℂ := fun x => 1 - cyclicLinearCharacter ρ M 2 x
    χ ldelta ρ = -1 ∧
      (∀ j : ℤ, ¬ j ≡ 0 [ZMOD M] → ¬ j ≡ (M / 2 : ℕ) [ZMOD M] → χ lphi (ρ ^ j) = ε) ∧
      χ lphi (tInC t) = q ∧ χ lphi σ = -ε ∧
      ∃ η : basis.index, η ∈ B ∧ η ≠ principal ∧ η ≠ ldelta ∧ η ≠ lphi ∧ η ≠ ldeltaPhi ∧
        principalCyclicProjection basis B ρ h = 1 + (ε : ℂ) • χ lphi - (ε : ℂ) • χ η ∧
        χ η 1 = q + ε ∧ χ η (tInC t) = q + ε ∧ χ η σ = 0 ∧
        ∀ α ∈ B, characterPairing (fun x : Subgroup.zpowers ρ => χ α x) h =
          (if α = principal then 1 else 0) + (ε : ℂ) * (if α = lphi then 1 else 0) -
            (ε : ℂ) * (if α = η then 1 else 0) := by
  intro B ρ σ M q ε χ h
  obtain ⟨hNZK, -, -, -, -, -, -⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  have hFodd : Odd (Nat.card F) := data.field_card ▸ hpodd.pow
  have hF : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, hf, data.field_card⟩
  have hεC : (ε : ℂ) = localEpsilon F := actualLayer_localEpsilon_cast F
  obtain ⟨ld, lp, ldp, hd', hphi', hdp', hnodup, hP, -, -, -, -, -, -, -⟩ := cdata.characters
  have hld : ld = ldelta := basis.distinct (funext fun c => (hd' c).trans (hdelta c).symm)
  have hlp : lp = lphi := basis.distinct (funext fun c => (hphi' c).trans (hphi c).symm)
  have hldp : ldp = ldeltaPhi :=
    basis.distinct (funext fun c => (hdp' c).trans (hdeltaPhi c).symm)
  subst hld hlp hldp
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil] at hnodup
  obtain ⟨⟨h1δ, h1φ, h1δφ, -⟩, ⟨hδφne, hδδφ, -⟩, ⟨hφδφ, -⟩, -⟩ := hnodup
  have hpB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have hδB : ld ∈ B := (hP ld (by simp)).2.1
  have hφB : lp ∈ B := (hP lp (by simp)).2.1
  have hδφB : ldp ∈ B := (hP ldp (by simp)).2.1
  have hρ : orderOf ρ = M := suppliedRotation_orderOf (by omega) e
  obtain ⟨hM, -, hK2, -⟩ := modulus_eq_four_mul hn
  have hord4 : orderOf (ρ ^ (M / 4)) = 4 := by
    rw [orderOf_pow_of_dvd (by omega) ⟨4, by omega⟩, hρ]
    change modulus n / (modulus n / 4) = 4
    rw [hM, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel _ (by positivity)]
  have hσ2 : orderOf σ = 2 := suppliedReflection_orderOf (by omega) e
  have hσt : σ ≠ tInC t := by
    intro hst
    have hsz : e (s n) = e (z n) := by
      apply Subtype.ext
      change σ = (e (r n ^ half n) : C t)
      rw [hst, map_pow, Subgroup.coe_pow, ← he, show half n = modulus n / 2 from by
        rw [modulus_eq_two_mul_half (by omega)]
        omega]
    have h' := e.injective hsz
    exact (MatrixCover.semidihedral_reflection n hn).2 (h' ▸ z_mem_center n hn)
  have hδρ : χ ld ρ = -1 := by
    change (basis.representation ld).character ρ = -1
    rw [hdelta]
    exact localDelta_eq_neg_one_of_not_mem F rho ρ fun h1 =>
      actualLayer_not_mem_K_of_orderOf n hn S0 f0 hG t ht ρ hρ
        ((localDelta_eq_one_iff F A rho data.faithful data.full_image data.residual_image
          hNZK hF ρ).mp h1)
  have hrot : ∀ j : ℤ, ¬ j ≡ 0 [ZMOD M] → ¬ j ≡ (M / 2 : ℕ) [ZMOD M] →
      χ lp (ρ ^ j) = ε := by
    intro j hj0 hj1
    change (basis.representation lp).character (ρ ^ j) = ε
    rw [hphi, actualLayer_localPhi_rotation ht hn data hFodd hρ he j hj0 hj1,
      (cdata.order_four_values _ hord4).1, hεC]
  have htq : χ lp (tInC t) = q := by
    change (basis.representation lp).character (tInC t) = ((p ^ f : ℕ) : ℂ)
    rw [hphi]
    exact (cdata.kernel_values (tInC t) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))).1
  have hσv : χ lp σ = -ε := by
    change (basis.representation lp).character σ = -ε
    rw [hphi, (cdata.noncentral_involution_values σ hσ2 hσt).2.1, hεC]
  refine ⟨hδρ, hrot, htq, hσv, ?_⟩
  have hδdeg : (basis.representation ld).character 1 = 1 := by
    rw [hdelta]
    exact (localDelta_eq_one_iff F A rho data.faithful data.full_image data.residual_image
      hNZK hF 1).mpr (one_mem _)
  have hδsq : ∀ c, (basis.representation ld).character c *
      (basis.representation ld).character c = 1 := by
    intro c
    rw [hdelta]
    unfold localDelta
    split_ifs <;> norm_num
  have hφdeg : (basis.representation lp).character 1 = q := by
    rw [hphi, localPhi_on_NZ F rho 1 (one_mem _), data.field_card]
  have hq1 : 1 < q := Nat.one_lt_pow (by omega) hp.one_lt
  have hεpm : ε = 1 ∨ ε = -1 := by
    simp only [ε]
    split_ifs <;> simp
  have hδφ : ∀ c, (basis.representation ldp).character c =
      (basis.representation ld).character c * (basis.representation lp).character c :=
    fun c => by rw [hdeltaPhi, hdelta, hphi]
  have hφt : (basis.representation lp).character ((e (r n) : C t) ^ (modulus n / 2)) = q := by
    rw [he]
    exact htq
  obtain ⟨η, -, hη⟩ := local_even_Fourier_principal_character_column hn e basis ideal principal
    hprincipal ld lp ldp q ε hδdeg hδsq hδρ hφB hφdeg hpodd.pow hq1 hεpm hδφ hδB hδφB
    h1δ h1φ h1δφ hδφne hδδφ hφδφ hφt hσv hrot
  have hl : 1 ≤ M / 4 - 1 := by
    change 1 ≤ modulus n / 4 - 1
    rw [hM, Nat.mul_div_cancel_left _ (by norm_num)]
    omega
  obtain ⟨hηB, hη1, hηδ, hηφ, hηδφ, hE, hηdeg, hηt, hησ⟩ := hη 1 le_rfl hl
  have hfun : (fun x : Subgroup.zpowers ρ => 1 - cyclicLinearCharacter ρ M (2 * ((1 : ℕ) : ℤ)) x) =
      h := by
    funext x
    simp [h]
  change principalCyclicProjection basis B ρ
    (fun x => 1 - cyclicLinearCharacter ρ M (2 * ((1 : ℕ) : ℤ)) x) = _ at hE
  rw [hfun] at hE
  change (basis.representation (η 1)).character (ρ ^ (M / 2)) = q + ε at hηt
  rw [he] at hηt
  have hηB' : η 1 ∈ B := hηB
  refine ⟨η 1, hηB, hη1, hηδ, hηφ, hηδφ, hE, hηdeg, hηt, hησ, fun α hα => ?_⟩
  let k : basis.index → ℂ := fun d =>
    characterPairing (fun x : Subgroup.zpowers ρ => χ d x) h
  let k' : basis.index → ℂ := fun d => (if d = principal then 1 else 0) +
    (ε : ℂ) * (if d = lp then 1 else 0) - (ε : ℂ) * (if d = η 1 then 1 else 0)
  have hcomb : (fun g => ∑ d ∈ B, k d * χ d g) = fun g => ∑ d ∈ B, k' d * χ d g := by
    funext g
    have h1 : (∑ d ∈ B, k d * χ d g) = principalCyclicProjection basis B ρ h g := rfl
    rw [h1, hE]
    simp only [k', add_mul, sub_mul, ite_mul, one_mul, zero_mul, mul_assoc,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' B, hpB, hφB, hηB', ite_true]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, χ,
      hprincipal]
  have hk := basis_combination_coefficient basis hα k
  rw [hcomb, basis_combination_coefficient basis hα k'] at hk
  exact hk.symm

end CFSG.Semidihedral.Principal

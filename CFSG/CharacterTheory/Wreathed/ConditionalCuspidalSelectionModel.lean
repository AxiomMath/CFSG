module

public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeries
public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelectionTrace
public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelectionCount

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.TwoRankLowerBound.Helpers
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.CentralSL2Abelianization
  CFSG.Wreathed.CentralSL2

section Degrees

theorem succ_ne_odd_mul_pred {q s : ℕ} (hq : 3 ≤ q) (hs : Odd s) : q + 1 ≠ s * (q - 1) := by
  obtain ⟨k, rfl⟩ := hs
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · omega
  · have h1 : (2 * k + 1) * (q - 1) ≥ 3 * (q - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem mem_cuspidalLabels_of_degree {H : Type} [Group H] [Fintype H]
    (basisH : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principalH : basisH.index) {m : ℕ} {ℓ : Fin m → H → ℂ} {Φ : H → ℂ}
    {PH : Set (H → ℂ)} {q : ℕ} (hq : 3 ≤ q) (hℓ1 : ∀ r, ℓ r 1 = 1) (hΦ1 : Φ 1 = q)
    (hPH1 : ∀ θ ∈ PH, θ 1 = (q : ℂ) + 1) {l : basisH.index}
    (hl : l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH) {s : ℕ}
    (hs : Odd s) (hdeg : (basisH.representation l).character 1 = (s : ℂ) * ((q : ℂ) - 1)) :
    l ∈ cuspidalLabels basisH ideal principalH (MonoidHom.id H) ℓ Φ PH := by
  have hq1 : 1 ≤ q := by omega
  have hcast : (basisH.representation l).character 1 = ((s * (q - 1) : ℕ) : ℂ) := by
    rw [hdeg, natCast_mul_sub_one hq1]
  have hs0 : 0 < s := hs.pos
  obtain ⟨-, -, h1, h2⟩ := degree_separation hq hs0
  refine Finset.mem_sdiff.mpr ⟨hl, fun hFP => ?_⟩
  rcases Finset.mem_union.mp hFP with hF | hP
  · simp only [linearAugmentationLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hF
    obtain ⟨r, hr | hr⟩ := hF
    · have := congrFun hr 1
      rw [hcast, MonoidHom.id_apply, hℓ1] at this
      exact h1.symm (by exact_mod_cast this)
    · have := congrFun hr 1
      rw [hcast, MonoidHom.id_apply, hℓ1, one_mul, hΦ1] at this
      exact h2.symm (by exact_mod_cast this)
  · simp only [principalSeriesLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    obtain ⟨θ, hθ, hlθ⟩ := hP
    have := congrFun hlθ 1
    rw [hcast, MonoidHom.id_apply, hPH1 θ hθ] at this
    exact succ_ne_odd_mul_pred hq hs (by exact_mod_cast this.symm)

end Degrees

section Model

variable {G : Type} [Group G] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)} {F : Type} [Field F] [Fintype F]
  {Sigma : Subgroup (F ≃+* F)} {b : Fˣ} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
  {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma ≃* centralizerOddCoreQuotient n S e}

local notation "W" => SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
  (wreathModulus_even hn) Sigma hSigma
local notation "H" => centralizerOddCoreQuotient n S e
local notation "K" => CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)

theorem cuspidalLabel_comp_mem_aboveFamily [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    [Fintype H] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (basisH : FiniteIrreducibleCharacterBasis H) (principalH : basisH.index)
    {σ₀ : Sigma} {hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀} {ζm ζd : ℂ}
    {hζm : IsPrimitiveRoot ζm (2 ^ n)} {hζd : IsPrimitiveRoot ζd (Nat.card Sigma)}
    {lam Ξ : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (linearCharacter F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma σ₀ hgen ζm ζd hζm hζd r v (Ψ.symm h) : ℂ))
    (hΞ : ∀ r v h, Ξ r v h = lam r v h * ΦH h) {ℓ : Fin (2 ^ n) → H → ℂ}
    (hℓ : ∀ r h, lam r 0 h = ℓ r h)
    (hlamP : ∀ r v, (∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (basisH.representation l).character = lam r v) → v = 0)
    (hxiP : ∀ r v, (∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (basisH.representation l).character = Ξ r v) → v = 0)
    {PH : Set (H → ℂ)}
    (hPH : ∀ (P : PrincipalSeriesParameter F b (2 ^ n)) (ν : parameterStabilizer hSigma P →* ℂˣ),
      P.1.1 ≠ 1 → (∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisH.representation l).character = fun h => principalInduced
          (hm := wreathModulus_pos n) (heven := wreathModulus_even hn) hSigma P ν (Ψ.symm h)) →
      (fun h => principalInduced (hm := wreathModulus_pos n) (heven := wreathModulus_even hn)
        hSigma P ν (Ψ.symm h)) ∈ PH)
    {l : basisH.index} (hl : l ∈ cuspidalLabels basisH ideal principalH (MonoidHom.id H) ℓ ΦH PH) :
    (fun g => (basisH.representation l).character (Ψ g)) ∈ aboveFamily hSigma cuspBase := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hdata.card
  obtain ⟨hlB, hlFP⟩ := Finset.mem_sdiff.mp hl
  have hlF : l ∉ linearAugmentationLabels basisH (MonoidHom.id H) ℓ ΦH :=
    fun h => hlFP (Finset.mem_union_left _ h)
  have hlP : l ∉ principalSeriesLabels basisH (MonoidHom.id H) PH :=
    fun h => hlFP (Finset.mem_union_right _ h)
  have hback : ∀ φ : W → ℂ, (fun g => (basisH.representation l).character (Ψ g)) = φ →
      (basisH.representation l).character = fun h => φ (Ψ.symm h) := by
    intro φ hφ
    rw [← hφ]
    funext h
    exact (congrArg _ (MulEquiv.apply_symm_apply Ψ h)).symm
  have hθW : (fun g => (basisH.representation l).character (Ψ g)) ∈ BlocksIrr W :=
    Semidihedral.Principal.comp_mem_blocksIrr Ψ.toMonoidHom Ψ.surjective
      (CFSG.BlockBasics.basis_character_mem_irr basisH l)
  obtain ⟨hcomplete, -⟩ := semilinear_complete_family (hm := wreathModulus_pos n)
    (heven := wreathModulus_even hn) hSigma σ₀ hgen ζm ζd hζm hζd (hp.odd_of_ne_two hpodd)
    hdata.nonsquare hdata.sigma_odd
  rw [hcomplete] at hθW
  rcases hθW with ((h1 | h2) | h3) | h4
  · exfalso
    obtain ⟨⟨r, v⟩, hrv⟩ := h1
    have hchar : (basisH.representation l).character = lam r v := by
      rw [hback _ hrv.symm]
      funext h
      rw [hlam]
    have hv := hlamP r v ⟨l, hlB, hchar⟩
    subst hv
    apply hlF
    simp only [linearAugmentationLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨r, Or.inl ?_⟩
    rw [hchar]
    funext h
    exact hℓ r h
  · exfalso
    obtain ⟨⟨r, v⟩, hrv⟩ := h2
    have hchar : (basisH.representation l).character = Ξ r v := by
      rw [hback _ hrv.symm]
      funext h
      rw [hΞ, hlam, compatibleModel_augmentation_symm hn hdata hΦ]
    have hv := hxiP r v ⟨l, hlB, hchar⟩
    subst hv
    apply hlF
    simp only [linearAugmentationLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨r, Or.inr ?_⟩
    rw [hchar]
    funext h
    rw [hΞ, hℓ]
    rfl
  · exfalso
    obtain ⟨P, ν, hP, hPν⟩ := h3
    have hchar : (basisH.representation l).character = fun h => principalInduced
        (hm := wreathModulus_pos n) (heven := wreathModulus_even hn) hSigma P ν (Ψ.symm h) :=
      hback _ hPν
    apply hlP
    simp only [principalSeriesLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨_, hPH P ν hP ⟨l, hlB, hchar⟩, hchar⟩
  · exact h4

theorem augmentation_generator [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ} (hp : p.Prime)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    {σ₀ : Sigma} (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) :
    ΦH (Ψ ⟨1, σ₀⟩) = (p : ℂ) ^ (f / Nat.card Sigma) := by
  rw [compatibleModel_augmentation hn hdata hΦ, fixedPointCount_field F b _ _ _ Sigma hSigma hp
    hdata.card σ₀, orderOf_eq_card_of_forall_mem_zpowers hgen]
  ring

theorem odd_orderOf_generator [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) (σ₀ : Sigma) :
    Odd (orderOf (Ψ ⟨1, σ₀⟩)) := by
  rw [MulEquiv.orderOf_eq]
  change Odd (orderOf (SemidirectProduct.inr σ₀ : W))
  rw [orderOf_injective _ SemidirectProduct.inr_injective]
  exact hdata.sigma_odd.of_dvd_nat (orderOf_dvd_natCard σ₀)

theorem one_lt_fixedFieldCard {p f d : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hd : d ∣ f) :
    1 < p ^ (f / d) := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
  have hfd : 1 ≤ f / d := (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (by omega) hd)
  exact Nat.one_lt_pow (by omega) hp.one_lt

theorem cuspidalLabel_restrict [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    [Fintype H] {basisH : FiniteIrreducibleCharacterBasis H} {l : basisH.index}
    (habove : (fun g => (basisH.representation l).character (Ψ g)) ∈ aboveFamily hSigma cuspBase)
    {σ₀ : Sigma} (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) {u : ℕ} (hu : 0 < u)
    (hodd : ∀ y : H, Odd (orderOf y) → (basisH.representation l).character y = u * (ΦH y - 1)) :
    (fun g => (basisH.representation l).character (Ψ (SemidirectProduct.inl g))) ∈ cuspBase ∧
      twistStabilizer hSigma
        (fun g => (basisH.representation l).character (Ψ (SemidirectProduct.inl g))) = ⊤ ∧
      (basisH.representation l).character (Ψ ⟨1, σ₀⟩) =
        u * ((p : ℂ) ^ (f / Nat.card Sigma) - 1) := by
  have hval : (basisH.representation l).character (Ψ ⟨1, σ₀⟩) =
      u * ((p : ℂ) ^ (f / Nat.card Sigma) - 1) := by
    rw [hodd _ (odd_orderOf_generator hn hdata σ₀), augmentation_generator hn hp hdata hΦ hgen]
  have hne : (basisH.representation l).character (Ψ ⟨1, σ₀⟩) ≠ 0 := by
    rw [hval]
    have h1 := one_lt_fixedFieldCard hp hf hdata.sigma_dvd
    refine mul_ne_zero (Nat.cast_ne_zero.mpr hu.ne') ?_
    rw [sub_ne_zero]
    exact_mod_cast h1.ne'
  obtain ⟨hξ, θ, hθ, habove'⟩ := habove
  obtain ⟨χ, hχ, hres, ρ', hξρ⟩ := exists_twistInduced_of_liesAbove hSigma hθ.1 hξ habove'
  have hσ₀ : σ₀ ∈ twistStabilizer hSigma θ := by
    apply mem_twistStabilizer_of_twistInduced_ne_zero hSigma hθ.1 hχ hres ρ' 1 σ₀
    rw [← hξρ]
    exact hne
  have hStab := eq_top_of_generator_mem hgen hσ₀
  have hθeq : (fun g => (basisH.representation l).character (Ψ (SemidirectProduct.inl g))) = θ := by
    have h := twistInduced_inl_of_top hSigma hStab hχ hres ρ'
    rw [← hξρ] at h
    exact h
  rw [hθeq]
  exact ⟨hθ, hStab, hval⟩

theorem cuspidalLabel_mem_twoPrimary [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    [Fintype H] {basisH : FiniteIrreducibleCharacterBasis H} {l : basisH.index}
    (hθ : (fun g => (basisH.representation l).character (Ψ (SemidirectProduct.inl g))) ∈
      cuspBase)
    (hodd : ∀ y : H, Odd (orderOf y) → (basisH.representation l).character y = ΦH y - 1)
    (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E) (h2 : (2 : F) ≠ 0)
    (z₀ y₀ : Eˣ) (hz₀ : (z₀ : E) * (z₀ : E) ^ Nat.card F = algebraMap F E b)
    (hy₀ : (y₀ : E) * (y₀ : E) ^ Nat.card F = -1) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∃ P : NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀,
      (P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k) ∧
      (fun g => (basisH.representation l).character (Ψ (SemidirectProduct.inl g))) =
        cuspidalCharacter hdata.nonsquare ψ (nonsplitCharacter F b (2 ^ n) (wreathModulus_pos n)
          (wreathModulus_even hn) E basis h2 z₀ hz₀ P) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hdata.card
  have hb := hdata.nonsquare
  set θ := fun g => (basisH.representation l).character (Ψ (SemidirectProduct.inl g)) with hθdef
  rw [cuspBase_eq basis (hp.odd_of_ne_two hpodd) hb y₀ hy₀ h2 hψ] at hθ
  obtain ⟨μ, hμ, hθμ⟩ := hθ
  have hθμ' : cuspidalCharacter hb ψ μ = θ := hθμ
  set eq := nonsplitCharacterEquiv F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
    basis h2 z₀ hz₀ with heq
  set P := eq.symm μ with hP
  have hμP : μ = nonsplitCharacter F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
      basis h2 z₀ hz₀ P := (eq.apply_symm_apply μ).symm
  refine ⟨P, ⟨?_, ?_⟩, ?_⟩
  · intro h1
    apply hμ
    rw [hμP]
    exact (minusWeyl_fixed_iff hb y₀ hy₀ h2 z₀ hz₀ P).mpr h1
  · rw [← nonsplitCharacter_two_pow_iff F E basis b (wreathModulus_pos n) (wreathModulus_even hn)
      h2 z₀ hz₀ rfl P, ← hμP]
    apply exists_two_pow_orderOf_of_forall_odd μ
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1, map_one]
    have htA : (t : K) ∉ Subgroup.zpowers (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) ^ 2) := by
      intro hmem
      have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
      rw [card_zpowers_A hb, Subgroup.orderOf_coe] at hdvd
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [pow_zero, orderOf_eq_one_iff] at hk
        exact ht1 hk
      · rw [hk] at ht
        exact (Nat.not_even_iff_odd.mpr ht) (Nat.even_pow.mpr ⟨even_two, hk0.ne'⟩)
    have htodd : Odd (orderOf (Ψ (SemidirectProduct.inl (t : K)) : H)) := by
      rw [MulEquiv.orderOf_eq, orderOf_injective _ SemidirectProduct.inl_injective,
        Subgroup.orderOf_coe]
      exact ht
    have hθt : θ t = -2 := by
      rw [hθdef]
      dsimp only
      rw [hodd _ htodd, compatibleModel_augmentation hn hdata hΦ, fixedPointCount_inl,
        card_fixed_nonsplitTorus hb t.2 htA]
      norm_num
    have hval := cuspidalCharacter_nonsplit hb y₀ hy₀ h2 ψ μ htA
    rw [hθμ', hθt] at hval
    have hnorm : ∀ s : nonsplitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
        E basis, ‖((μ s : ℂˣ) : ℂ)‖ = 1 := by
      intro s
      have := finite_of_basis F E basis
      have : Finite (nonsplitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
          E basis) := Nat.finite_of_card_ne_zero (by
        rw [card_nonsplitTorus z₀ hz₀]
        exact Nat.mul_ne_zero (wreathModulus_pos n).ne' (by omega))
      apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card (nonsplitTorus F b (2 ^ n)
        (wreathModulus_pos n) (wreathModulus_even hn) E basis))
      · rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
      · exact Nat.card_pos.ne'
    have h4 := eq_one_of_norm_le_one_of_sum_eq_card (Finset.univ : Finset (Fin 2))
      ![((μ t : ℂˣ) : ℂ), ((μ (minusWeylConj h2 y₀ hy₀ t) : ℂˣ) : ℂ)]
      (fun i _ => by fin_cases i <;> simp [hnorm])
      (by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
        linear_combination hval) 0 (Finset.mem_univ _)
    exact Units.ext (by simpa using h4)
  · rw [← hθμ', hμP]

end Model

end CFSG.Wreathed

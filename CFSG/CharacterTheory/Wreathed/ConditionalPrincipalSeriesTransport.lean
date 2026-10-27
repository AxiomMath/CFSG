module

public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesRows
public import CFSG.CharacterTheory.Wreathed.ConditionalLinearAugmentationTwistsRows

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

section Transport

variable {E H : Type} [Group E] [Fintype E] [Group H] [Fintype H]

omit [Fintype H] in
theorem principalSeriesLabels_card (basisE : FiniteIrreducibleCharacterBasis E) (fE : E →* H)
    (hfE : Function.Surjective fE) {PH : Set (H → ℂ)} (hPH : ∀ θ ∈ PH, θ ∈ BlocksIrr H) :
    (principalSeriesLabels basisE fE PH).card = PH.ncard := by
  have hmem : ∀ l, l ∈ principalSeriesLabels basisE fE PH ↔
      ∃ θ ∈ PH, (basisE.representation l).character = fun y => θ (fE y) := by
    intro l
    simp [principalSeriesLabels]
  have hcomp : ∀ θ θ' : H → ℂ, ((fun y => θ (fE y)) = fun y => θ' (fE y)) → θ = θ' := by
    intro θ θ' h
    funext z
    obtain ⟨y, rfl⟩ := hfE z
    exact congrFun h y
  choose g hg hgchar using fun l : principalSeriesLabels basisE fE PH => (hmem l.1).mp l.2
  have hinj : Function.Injective fun l : principalSeriesLabels basisE fE PH =>
      (⟨g l, hg l⟩ : PH) := by
    intro l l' h
    have h' : g l = g l' := congrArg Subtype.val h
    apply Subtype.ext
    apply basisE.distinct
    change (basisE.representation l.1).character = (basisE.representation l'.1).character
    rw [hgchar, hgchar, h']
  have hsurj : Function.Surjective fun l : principalSeriesLabels basisE fE PH =>
      (⟨g l, hg l⟩ : PH) := by
    rintro ⟨θ, hθ⟩
    obtain ⟨l, hl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basisE
      (Semidihedral.Principal.comp_mem_blocksIrr fE hfE (hPH θ hθ))
    have hlmem : l ∈ principalSeriesLabels basisE fE PH := (hmem l).mpr ⟨θ, hθ, hl⟩
    refine ⟨⟨l, hlmem⟩, Subtype.ext ?_⟩
    exact hcomp _ _ ((hgchar ⟨l, hlmem⟩).symm.trans hl)
  rw [← Nat.card_eq_finsetCard, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)

theorem conditionalPrincipalSeriesCuspidalData_of_inflation
    (basisE : FiniteIrreducibleCharacterBasis E) (basisH : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (principalE : basisE.index) (principalH : basisH.index) (fE : E →* H)
    (hfE : Function.Surjective fE)
    (hblock : ∀ χ, χ ∈ coefficientBlock basisE (localizedComplexIntegerRing ideal) principalE ↔
      ∃ θ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisE.representation χ).character = (basisH.representation θ).character ∘ fE)
    {m d : ℕ} [NeZero d] {lam Ξ : Fin m → Fin d → H → ℂ} {ℓ : Fin m → H → ℂ} {Φ : H → ℂ}
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q κ : ℕ}
    (hdataE : ConditionalTwistResidualData basisE ideal principalE fE lam Ξ Φ ε q)
    (hℓ : ∀ r h, lam r 0 h = ℓ r h) (hΞ : ∀ r h, Ξ r 0 h = ℓ r h * Φ h)
    {I : Type*} {Θ : I → H → ℂ} {adm sel : I → Prop}
    (hΘirr : ∀ i, adm i → Θ i ∈ BlocksIrr H)
    (hΘP : ∀ i, adm i →
      ((∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisH.representation l).character = Θ i) ↔ sel i))
    {PH : Set (H → ℂ)} (hPHcard : PH.ncard = m * (κ - 1) / 2)
    (hPHprin : ∀ θ ∈ PH, ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal)
      principalH, (basisH.representation l).character = θ)
    (hPHodd : ∀ θ ∈ PH, ∀ y : H, Odd (orderOf y) → θ y = 1 + Φ y)
    (hdegC : ∀ θ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (∃ r, (basisH.representation θ).character = ℓ r ∨
        (basisH.representation θ).character = fun h => ℓ r h * Φ h) ∨
      (basisH.representation θ).character ∈ PH ∨
      ∃ u : ℕ, 0 < u ∧ u ∣ d ∧ (basisH.representation θ).character 1 = (u : ℂ) * ((q : ℂ) - 1))
    (hκ1 : ε = 1 → κ = m) (hκ2 : ε = -1 → κ = 2) (hmeven : Even m) (hm : 2 ≤ m) (hq : 3 ≤ q) :
    ConditionalPrincipalSeriesCuspidalData basisE ideal principalE fE Θ adm sel PH ℓ Φ ε q d κ := by
  set B := coefficientBlock basisE (localizedComplexIntegerRing ideal) principalE with hBdef
  set Fl := linearAugmentationLabels basisE fE ℓ Φ with hFldef
  set PL := principalSeriesLabels basisE fE PH with hPLdef
  set c₀ : OddElements E → ℂ := oddRestriction (1 : E → ℂ) with hc₀
  set c₁ : OddElements E → ℂ := oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y)) with hc₁
  have hreg := hdataE.regular_basis
  have hεZ : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεC : (ε : ℂ) * ε = 1 := by exact_mod_cast hεZ
  have hfodd : ∀ y : E, Odd (orderOf y) → Odd (orderOf (fE y)) := fun y hy =>
    hy.of_dvd_nat (orderOf_map_dvd fE y)
  have h1odd : Odd (orderOf (1 : E)) := by rw [orderOf_one]; exact odd_one
  have hmem := exists_coefficientBlock_comp_iff basisE basisH ideal principalE principalH fE hfE
    hblock
  have hΦ1 : Φ (fE 1) = q := hreg.degree
  have hq1 : (q : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero, ← Nat.cast_one, Ne, Nat.cast_inj]
    omega
  have hPLmem : ∀ l, l ∈ PL ↔ ∃ θ ∈ PH, (basisE.representation l).character =
      fun y => θ (fE y) := by
    intro l
    simp [hPLdef, principalSeriesLabels]
  have hPLB : PL ⊆ B := by
    intro l hl
    obtain ⟨θ, hθ, hlθ⟩ := (hPLmem l).mp hl
    obtain ⟨l', hl', hl'θ⟩ := (hmem θ).mpr (hPHprin θ hθ)
    rwa [basisE.distinct (hl'θ.trans hlθ.symm)] at hl'
  have hPLodd : ∀ l ∈ PL, ∀ y : E, Odd (orderOf y) →
      (basisE.representation l).character y = 1 + Φ (fE y) := by
    intro l hl y hy
    obtain ⟨θ, hθ, hlθ⟩ := (hPLmem l).mp hl
    rw [hlθ]
    exact hPHodd θ hθ _ (hfodd y hy)
  have hPLrow : ∀ l ∈ PL, oddRestriction (basisE.representation l).character =
      (1 - ε) • c₀ + ε • c₁ := by
    intro l hl
    rw [hc₀, hc₁, oddRestriction_eq_zsmul_add_iff]
    intro y hy
    rw [hPLodd l hl y hy]
    simp only [Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub,
      Int.cast_one]
    linear_combination (-(Φ (fE y))) * hεC
  have hFam : twistFamilyLabels basisE fE lam Ξ = Fl := by
    ext l
    have h1 : ∀ r, (fun y => lam r 0 (fE y)) = (fun y => ℓ r (fE y)) := fun r =>
      funext fun y => hℓ r _
    have h2 : ∀ r, (fun y => Ξ r 0 (fE y)) = (fun y => ℓ r (fE y) * Φ (fE y)) := fun r =>
      funext fun y => hΞ r _
    simp only [twistFamilyLabels, hFldef, linearAugmentationLabels, Finset.mem_filter,
      Finset.mem_univ, true_and, h1, h2]
  have hFldeg : ∀ l ∈ Fl, (basisE.representation l).character 1 = 1 ∨
      (basisE.representation l).character 1 = q := by
    intro l hl
    rw [← hFam] at hl
    simp only [twistFamilyLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    obtain ⟨r, hr | hr⟩ := hl
    · left
      rw [hr]
      exact (hdataE.lam_irreducible r 0).2
    · right
      rw [hr]
      exact (hdataE.xi_irreducible r 0).2
  have hPLdeg : ∀ l ∈ PL, (basisE.representation l).character 1 = (q : ℂ) + 1 := by
    intro l hl
    rw [hPLodd l hl 1 h1odd, hΦ1]
    ring
  have hdisj : ∀ l ∈ PL, l ∉ Fl := by
    intro l hl hlF
    have hdeg := hPLdeg l hl
    rcases hFldeg l hlF with h | h
    · rw [h] at hdeg
      have : (q : ℂ) = 0 := by linear_combination -hdeg
      rw [Nat.cast_eq_zero] at this
      omega
    · rw [h] at hdeg
      have : (1 : ℂ) = 0 := by linear_combination -hdeg
      exact one_ne_zero this
  have hT : residualTorusLabels basisE ideal principalE fE lam Ξ = B \ Fl := by
    rw [residualTorusLabels, hFam]
  have hPLT : PL ⊆ B \ Fl := fun l hl => Finset.mem_sdiff.mpr ⟨hPLB hl, hdisj l hl⟩
  have hCL : cuspidalLabels basisE ideal principalE fE ℓ Φ PH = (B \ Fl) \ PL := by
    ext l
    simp only [cuspidalLabels, Finset.mem_sdiff, Finset.mem_union, ← hBdef, ← hFldef, ← hPLdef]
    tauto
  have hCLB : ∀ {l}, l ∈ cuspidalLabels basisE ideal principalE fE ℓ Φ PH → l ∈ B := by
    intro l hl
    rw [hCL] at hl
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hl).1).1
  choose A Bc hAB hb0 hab0 hA1 huniq using fun χ : B => hreg.coefficients χ.1 χ.2
  let Rfull : basisE.index → Fin 2 → ℤ := fun l =>
    if h : l ∈ B then ![A ⟨l, h⟩ - ε * Bc ⟨l, h⟩, ε * Bc ⟨l, h⟩] else 0
  have hRfull : ∀ l (h : l ∈ B), Rfull l = ![A ⟨l, h⟩ - ε * Bc ⟨l, h⟩, ε * Bc ⟨l, h⟩] :=
    fun l h => dite_eq_left h
  have hRrow : ∀ l (h : l ∈ B), oddRestriction (basisE.representation l).character =
      Rfull l 0 • c₀ + Rfull l 1 • c₁ := by
    intro l h
    rw [hRfull l h, hc₀, hc₁, oddRestriction_eq_zsmul_add_iff]
    intro y hy
    rw [hAB ⟨l, h⟩ y hy]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.one_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul]
    linear_combination (-(Bc ⟨l, h⟩ : ℂ) * Φ (fE y)) * hεC
  have hPLcoef : ∀ l (h : l ∈ PL), A ⟨l, hPLB h⟩ = 1 ∧ Bc ⟨l, hPLB h⟩ = 1 := by
    intro l h
    have h' := huniq ⟨l, hPLB h⟩ 1 1 (fun y hy => by
      rw [hPLodd l h y hy]
      push_cast
      ring)
    exact ⟨h'.1.symm, h'.2.symm⟩
  have hPLR : ∀ l ∈ PL, Rfull l = ![1 - ε, ε] := by
    intro l h
    rw [hRfull l (hPLB h), (hPLcoef l h).1, (hPLcoef l h).2, mul_one]
  have hTmem : ∀ l, l ∈ residualTorusLabels basisE ideal principalE fE lam Ξ ↔ l ∈ B \ Fl := by
    intro l
    rw [hT]
  set Q : Matrix (residualTorusLabels basisE ideal principalE fE lam Ξ) (Fin 2) ℤ :=
    fun χ => Rfull χ.1 with hQdef
  have hgramT := hdataE.residual_gram Q (fun χ =>
    hRrow χ.1 (Finset.mem_sdiff.mp ((hTmem χ.1).mp χ.2)).1)
  have hsumT : ∀ i j : Fin 2, ∑ l ∈ B \ Fl, Rfull l i * Rfull l j =
      ((m : ℤ) • !![2, -1; -1, ((m / 2 : ℕ) : ℤ)]) i j := by
    intro i j
    have h := congrFun (congrFun hgramT i) j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.transpose_apply] at h
    rw [← h, ← hT]
    exact (Finset.sum_coe_sort _ (fun l => Rfull l i * Rfull l j)).symm
  set CL := cuspidalLabels basisE ideal principalE fE ℓ Φ PH with hCLdef
  have hsplit : ∀ i j : Fin 2, ∑ l ∈ CL, Rfull l i * Rfull l j =
      ((m : ℤ) • !![2, -1; -1, ((m / 2 : ℕ) : ℤ)]) i j -
        (PL.card : ℤ) * (![1 - ε, ε] i * ![1 - ε, ε] j) := by
    intro i j
    have hPLsum : ∑ l ∈ PL, Rfull l i * Rfull l j =
        (PL.card : ℤ) * (![1 - ε, ε] i * ![1 - ε, ε] j) := by
      rw [Finset.sum_congr rfl (g := fun _ => ![1 - ε, ε] i * ![1 - ε, ε] j)
        fun l hl => by rw [hPLR l hl], Finset.sum_const, nsmul_eq_mul]
    have h := Finset.sum_sdiff hPLT (f := fun l => Rfull l i * Rfull l j)
    rw [← hCL, hPLsum, hsumT i j] at h
    linear_combination h
  have hPLcard : (PL.card : ℤ) = ((m * (κ - 1) / 2 : ℕ) : ℤ) := by
    rw [principalSeriesLabels_card basisE fE hfE fun θ hθ => by
      obtain ⟨l, -, hl⟩ := hPHprin θ hθ
      rw [← hl]
      exact CFSG.BlockBasics.basis_character_mem_irr basisH l, hPHcard]
  obtain ⟨m', hm'⟩ := hmeven
  have hm'1 : 1 ≤ m' := by omega
  have hm2 : m / 2 = m' := by omega
  have hmm : m * (m - 1) / 2 = m' * (2 * m' - 1) := by
    rw [hm', show m' + m' = 2 * m' by ring, show 2 * m' * (2 * m' - 1) = 2 * (m' * (2 * m' - 1))
      by ring, Nat.mul_div_cancel_left _ two_pos]
  have hgramC1 : ε = 1 → ∀ i j : Fin 2, ∑ l ∈ CL, Rfull l i * Rfull l j =
      (((m / 2 : ℕ) : ℤ) • !![4, -2; -2, 1]) i j := by
    intro h1 i j
    have hκ := hκ1 h1
    have hc : ((m' * (2 * m' - 1) : ℕ) : ℤ) = (m' : ℤ) * (2 * m' - 1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * m')]
      ring
    rw [hsplit i j, hPLcard, hκ, h1, hm2, hmm, hc, hm']
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hgramC2 : ε = -1 → ∀ i j : Fin 2, ∑ l ∈ CL, Rfull l i * Rfull l j =
      (((m * (m - 1) / 2 : ℕ) : ℤ) • !![0, 0; 0, 1]) i j := by
    intro h2 i j
    have hκ := hκ2 h2
    have hm1 : m * (2 - 1) / 2 = m' := by omega
    have hc : ((m' * (2 * m' - 1) : ℕ) : ℤ) = (m' : ℤ) * (2 * m' - 1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * m')]
      ring
    rw [hsplit i j, hPLcard, hκ, h2, hm2, hm1, hmm, hc, hm']
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hab : ∀ l (h : l ∈ CL), A ⟨l, hCLB h⟩ + Bc ⟨l, hCLB h⟩ = 0 := by
    rcases hε with h1 | h2
    · have hsq : ∑ l ∈ CL, (Rfull l 0 + 2 * Rfull l 1) ^ 2 = 0 := by
        have e : ∀ l, (Rfull l 0 + 2 * Rfull l 1) ^ 2 = Rfull l 0 * Rfull l 0 +
            4 * (Rfull l 0 * Rfull l 1) + 4 * (Rfull l 1 * Rfull l 1) := fun l => by ring
        simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hgramC1 h1 0 0, hgramC1 h1 0 1, hgramC1 h1 1 1]
        simp
        ring
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg _)).mp hsq
      intro l h
      have h0 := hzero l h
      rw [hRfull l (hCLB h), h1] at h0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h0
      linarith
    · have hsq : ∑ l ∈ CL, Rfull l 0 ^ 2 = 0 := by
        simp only [sq]
        rw [hgramC2 h2 0 0]
        simp
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg _)).mp hsq
      intro l h
      have h0 := hzero l h
      rw [hRfull l (hCLB h), h2] at h0
      simp only [Matrix.cons_val_zero, neg_mul, one_mul, sub_neg_eq_add, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h0
      exact h0
  have hu : ∀ χ : CL, ∃ u : ℕ, 0 < u ∧ u ∣ d ∧
      (basisE.representation χ).character 1 = (u : ℂ) * ((q : ℂ) - 1) := by
    intro χ
    have hχB := hCLB χ.2
    have hCLmem : ∀ l, l ∈ CL ↔ l ∈ (B \ Fl) \ PL := fun l => by rw [hCL]
    have hχ : χ.1 ∈ (B \ Fl) \ PL := (hCLmem χ.1).mp χ.2
    obtain ⟨⟨-, hχF⟩, hχP⟩ := Finset.mem_sdiff.mp hχ |>.imp_left Finset.mem_sdiff.mp
    obtain ⟨θ, hθ, hχθ⟩ := (hblock χ.1).mp hχB
    rcases hdegC θ hθ with ⟨r, hr | hr⟩ | hθP | ⟨u, hu, hud, hdeg⟩
    · exfalso
      apply hχF
      simp only [hFldef, linearAugmentationLabels, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨r, Or.inl (by rw [hχθ, hr]; rfl)⟩
    · exfalso
      apply hχF
      simp only [hFldef, linearAugmentationLabels, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨r, Or.inr (by rw [hχθ, hr]; rfl)⟩
    · exact absurd ((hPLmem χ.1).mpr ⟨_, hθP, hχθ⟩) hχP
    · refine ⟨u, hu, hud, ?_⟩
      rw [hχθ, Function.comp_apply, map_one, hdeg]
  choose u hu0 hud hudeg using hu
  have hBu : ∀ χ : CL, Bc ⟨χ.1, hCLB χ.2⟩ = u χ := by
    intro χ
    have h1 := hA1 ⟨χ.1, hCLB χ.2⟩
    have hA : (A ⟨χ.1, hCLB χ.2⟩ : ℂ) = -Bc ⟨χ.1, hCLB χ.2⟩ := by
      have := hab χ.1 χ.2
      have : A ⟨χ.1, hCLB χ.2⟩ = -Bc ⟨χ.1, hCLB χ.2⟩ := by linarith
      exact_mod_cast this
    rw [hudeg χ, hA] at h1
    have h2 : ((Bc ⟨χ.1, hCLB χ.2⟩ : ℂ) - u χ) * ((q : ℂ) - 1) = 0 := by linear_combination -h1
    have h3 := (mul_eq_zero.mp h2).resolve_right hq1
    exact_mod_cast sub_eq_zero.mp h3
  have hRu : ∀ χ : CL, Rfull χ.1 = ![-(1 + ε) * (u χ : ℤ), ε * (u χ : ℤ)] := by
    intro χ
    rw [hRfull χ.1 (hCLB χ.2), hBu χ, show A ⟨χ.1, hCLB χ.2⟩ = -(u χ : ℤ) by
      have := hab χ.1 χ.2
      rw [hBu χ] at this
      linarith]
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      ring
    · simp
  have hsum_u : ∀ i j : Fin 2, ∑ χ : CL, Rfull χ.1 i * Rfull χ.1 j =
      ∑ l ∈ CL, Rfull l i * Rfull l j := fun i j =>
    Finset.sum_coe_sort CL (fun l => Rfull l i * Rfull l j)
  have hsq_u : ∑ χ : CL, ((u χ : ℤ)) ^ 2 = ∑ l ∈ CL, Rfull l 1 * Rfull l 1 := by
    rw [← hsum_u]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hRu χ]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show ε * (u χ : ℤ) * (ε * (u χ : ℤ)) = (ε * ε) * (u χ : ℤ) ^ 2 by ring, hεZ, one_mul]
  refine ⟨hreg, fun i hi => Semidihedral.Principal.comp_mem_blocksIrr fE hfE (hΘirr i hi),
    fun i hi => (hmem (Θ i)).trans (hΘP i hi), hPLB, ?_, hPLodd, hPLrow, ?_, ?_⟩
  · have h := hPLcard
    rw [← hPHcard] at h ⊢
    exact_mod_cast h
  · refine ⟨u, fun χ => ⟨hu0 χ, hud χ, hudeg χ, fun y hy => ?_, ?_⟩, fun h1 => ?_, fun h2 => ?_⟩
    · rw [hAB ⟨χ.1, hCLB χ.2⟩ y hy, hBu χ, show (A ⟨χ.1, hCLB χ.2⟩ : ℂ) = -(u χ : ℂ) by
        have := hab χ.1 χ.2
        rw [hBu χ] at this
        have : A ⟨χ.1, hCLB χ.2⟩ = -(u χ : ℤ) := by linarith
        exact_mod_cast this]
      push_cast
      ring
    · rw [hRrow χ.1 (hCLB χ.2), hRu χ]
      rfl
    · have h := hsq_u
      rw [hgramC1 h1 1 1] at h
      simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val',
        Matrix.cons_val_fin_one, smul_eq_mul, mul_one] at h
      exact_mod_cast h
    · have h := hsq_u
      rw [hgramC2 h2 1 1] at h
      simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val',
        Matrix.cons_val_fin_one, smul_eq_mul, mul_one] at h
      exact_mod_cast h
  · intro Q' hQ'
    have hQ'eq : ∀ χ : CL, Q' χ = Rfull χ.1 := by
      intro χ
      have h := (hQ' χ).symm.trans (hRrow χ.1 (hCLB χ.2))
      obtain ⟨h0, h1⟩ := hreg.linearIndependent.eq_of_pair h
      ext i
      fin_cases i
      · exact h0
      · exact h1
    have hmat : ∀ i j : Fin 2, (Q'.transpose * Q') i j = ∑ l ∈ CL, Rfull l i * Rfull l j := by
      intro i j
      rw [Matrix.mul_apply, ← hsum_u]
      simp only [Matrix.transpose_apply, hQ'eq]
      rfl
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · ext i j
      rw [hmat, hgramC1 h1]
    · ext i j
      rw [hmat, hgramC2 h2]

end Transport

section Correspondence

variable {E E' H : Type} [Group E] [Fintype E] [Group E'] [Fintype E'] [Group H]

theorem principalFamilyCorrespondence_of_regularRow (σ : E' →* E)
    (basis : FiniteIrreducibleCharacterBasis E) (basis' : FiniteIrreducibleCharacterBasis E')
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (principal' : basis'.index) (fE : E →* H) (fE' : E' →* H) (hcomp : ∀ y, fE (σ y) = fE' y)
    (hfE' : Function.Surjective fE')
    (hinfl : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∃ φ : H → ℂ, (basis.representation χ).character = fun y => φ (fE y))
    {m : ℕ} (ℓ : Fin m → H → ℂ) (Φ : H → ℂ) (PH : Set (H → ℂ)) (ε : ℤ)
    (hcorr : RegularRowCorrespondence σ basis basis' ideal principal principal'
      (fun y => Φ (fE y)) (fun y => Φ (fE' y)) ε) :
    PrincipalFamilyCorrespondence σ basis basis' ideal principal principal' fE fE' ℓ Φ PH ε := by
  obtain ⟨bij, hbij, -, hrow⟩ := hcorr
  have hkey : ∀ (θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
      (φ : H → ℂ), ((basis.representation θ).character = fun y => φ (fE y)) ↔
        ((basis'.representation (bij θ)).character = fun y => φ (fE' y)) := by
    intro θ φ
    constructor
    · intro h
      rw [hbij, h]
      funext y
      simp only [Function.comp_apply, hcomp]
    · intro h
      obtain ⟨ψ, hψ⟩ := hinfl θ.1 θ.2
      have h' : (fun y => ψ (fE' y)) = fun y => φ (fE' y) := by
        rw [← h, hbij, hψ]
        funext y
        simp only [Function.comp_apply, hcomp]
      have hψφ : ψ = φ := by
        funext z
        obtain ⟨y, rfl⟩ := hfE' z
        exact congrFun h' y
      rw [hψ, hψφ]
  have hF : ∀ θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      θ.1 ∈ linearAugmentationLabels basis fE ℓ Φ ↔
        (bij θ).1 ∈ linearAugmentationLabels basis' fE' ℓ Φ := by
    intro θ
    simp only [linearAugmentationLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    exact exists_congr fun r => or_congr (hkey θ (ℓ r)) (hkey θ fun h => ℓ r h * Φ h)
  have hP : ∀ θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      θ.1 ∈ principalSeriesLabels basis fE PH ↔
        (bij θ).1 ∈ principalSeriesLabels basis' fE' PH := by
    intro θ
    simp only [principalSeriesLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    exact exists_congr fun φ => and_congr_right fun _ => hkey θ φ
  refine ⟨bij, hbij, hrow, hF, hP, fun θ => ?_⟩
  simp only [cuspidalLabels, Finset.mem_sdiff, Finset.mem_union]
  rw [hF θ, hP θ]
  exact ⟨fun h => ⟨(bij θ).2, h.2⟩, fun h => ⟨θ.2, h.2⟩⟩

variable {E'' : Type} [Group E''] [Fintype E'']

theorem PrincipalFamilyCorrespondence.trans {σ : E' →* E} {σ' : E'' →* E'}
    {basis : FiniteIrreducibleCharacterBasis E} {basis' : FiniteIrreducibleCharacterBasis E'}
    {basis'' : FiniteIrreducibleCharacterBasis E''} {ideal : Ideal ComplexAlgebraicIntegers}
    [ideal.IsMaximal] {principal : basis.index} {principal' : basis'.index}
    {principal'' : basis''.index} {fE : E →* H} {fE' : E' →* H} {fE'' : E'' →* H} {m : ℕ}
    {ℓ : Fin m → H → ℂ} {Φ : H → ℂ} {PH : Set (H → ℂ)} {ε : ℤ}
    (h₁ : PrincipalFamilyCorrespondence σ basis basis' ideal principal principal' fE fE' ℓ Φ PH ε)
    (h₂ : PrincipalFamilyCorrespondence σ' basis' basis'' ideal principal' principal'' fE' fE''
      ℓ Φ PH ε) :
    PrincipalFamilyCorrespondence (σ.comp σ') basis basis'' ideal principal principal'' fE fE''
      ℓ Φ PH ε := by
  obtain ⟨τ₁, hc₁, hr₁, hF₁, hP₁, hC₁⟩ := h₁
  obtain ⟨τ₂, hc₂, hr₂, hF₂, hP₂, hC₂⟩ := h₂
  refine ⟨τ₁.trans τ₂, fun θ => ?_, fun θ r₀ r₁ => (hr₁ θ r₀ r₁).trans (hr₂ (τ₁ θ) r₀ r₁),
    fun θ => (hF₁ θ).trans (hF₂ (τ₁ θ)), fun θ => (hP₁ θ).trans (hP₂ (τ₁ θ)),
    fun θ => (hC₁ θ).trans (hC₂ (τ₁ θ))⟩
  rw [Equiv.trans_apply, hc₂, hc₁]
  rfl

end Correspondence

end CFSG.Wreathed

module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderTranslate
public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegrees

public noncomputable section

open scoped Classical ComplexConjugate

namespace CFSG.Wreathed.BrauerWreathedOrder

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.ConditionalGlobalDegrees CFSG.Wreathed.ConditionalSquareRoot
  CFSG.Wreathed.ConditionalGeneralBase

variable {G : Type} [Group G] [Fintype G]

theorem sum_mul_eq_zero_of_conj (basis : FiniteIrreducibleCharacterBasis G)
    (s : Finset basis.index) (coeff : basis.index → ℂ)
    (h : ∀ z : G, Odd (orderOf z) →
      ∑ χ ∈ s, coeff χ * conj ((basis.representation χ).character z) = 0)
    {z : G} (hz : Odd (orderOf z)) :
    ∑ χ ∈ s, coeff χ * (basis.representation χ).character z = 0 := by
  have hz' : Odd (orderOf z⁻¹) := by rwa [orderOf_inv]
  rw [← h z⁻¹ hz']
  exact Finset.sum_congr rfl fun χ _ => by rw [character_eq_conj_inv basis χ z]

theorem apply_eq_zero_of_sum_smul_eq (basis : FiniteIrreducibleCharacterBasis G)
    (s : Finset basis.index) (coeff : basis.index → ℂ) {Y : G → ℂ}
    (hY : ∑ χ ∈ s, coeff χ • (basis.representation χ).character = Y) {z : G}
    (h : ∑ χ ∈ s, coeff χ * (basis.representation χ).character z = 0) : Y z = 0 := by
  rw [← hY, Finset.sum_apply]
  simpa only [Pi.smul_apply, smul_eq_mul] using h

omit [Fintype G] in
theorem not_odd_orderOf_pow_odd {y : G} {m : ℕ} (hy : orderOf y = 2 * m) {k : ℕ} (hk : Odd k) :
    ¬ Odd (orderOf (y ^ k)) := by
  intro ho
  have h1 : y ^ (k * orderOf (y ^ k)) = 1 := by rw [pow_mul, pow_orderOf_eq_one]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hy] at h2
  have h3 : 2 ∣ k * orderOf (y ^ k) := dvd_trans (dvd_mul_right 2 m) h2
  exact Nat.not_even_iff_odd.mpr (hk.mul ho) (even_iff_two_dvd.mpr h3)

theorem sum_squareRootColumn_mul_eq_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) {y : G} {m : ℕ}
    (hy : orderOf y = 2 * m) (M₀ : ℕ) (ζ : ℂ) (r : ℕ) (c : basis.index → ℤ)
    (hc : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (c χ : ℂ) = (M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀,
        (basis.representation χ).character (y ^ (2 * i + 1)) * ζ ^ (-((r : ℤ) * (2 * i + 1))))
    {z : G} (hz : Odd (orderOf z)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (c χ : ℂ) * (basis.representation χ).character z = 0 := by
  apply sum_principal_combination_mul_eq_zero basis ideal principal (Finset.range M₀)
    (fun i => y ^ (2 * i + 1)) _ (fun i => (M₀ : ℂ)⁻¹ * ζ ^ (-((r : ℤ) * (2 * i + 1)))) _ _ hz
  · intro i _
    exact not_odd_orderOf_pow_odd hy (odd_two_mul_add_one i)
  · intro χ hχ
    rw [hc χ hχ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_fourierTransform_mul_eq_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (a : G) (m : ℕ) (C : ℕ → Subgroup G) (Φ : G → ℂ) (ε : ℤ) (hε : ε ≠ 0)
    (v : basis.index → ℕ → Fin 2 → ℂ)
    (hv : IsCentralSectionRows basis ideal principal a m C Φ ε v)
    (huniq : ∀ k ∈ Finset.Ico 1 m, ∀ w : Fin 2 → ℂ,
      (∀ r ∈ C k, Odd (orderOf r) →
        (basis.representation principal).character (a ^ k * r) = w 0 + w 1 * (1 + ε * Φ r)) →
      w = v principal k)
    (hC : ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ C k, Odd (orderOf r) → ¬ Odd (orderOf (a ^ k * r)))
    (ζ : ℂ) (j : ℕ) (ℓ : Fin 2) {z : G} (hz : Odd (orderOf z)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      fourierTransform m ζ (fun k => v χ k ℓ) j * (basis.representation χ).character z = 0 := by
  simp only [fourierTransform, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  convert mul_zero ((m : ℂ)⁻¹) using 2
  refine Finset.sum_eq_zero fun k hk => ?_
  simp only [← Finset.mul_sum]
  rw [sum_rows_mul_eq_zero basis ideal principal a m C Φ ε hε v hv huniq hC hk ℓ hz, mul_zero]

omit [Fintype G] in
theorem not_odd_orderOf_pow_mul {a : G} {n : ℕ} (ha : orderOf a = 2 ^ n) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 (2 ^ n)) {r : G} (hr : r ∈ Subgroup.centralizer {a ^ (k : ℤ)})
    (hro : Odd (orderOf r)) : ¬ Odd (orderOf (a ^ k * r)) := by
  rw [Finset.mem_Ico] at hk
  have hdvd : orderOf (a ^ k) ∣ 2 ^ n := by
    rw [← ha]
    exact orderOf_pow_dvd k
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hne : a ^ k ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ha] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hodd : ¬ Odd (orderOf (a ^ k)) := by
    intro ho
    rw [hi] at ho
    rcases i with _ | i
    · rw [pow_zero, orderOf_eq_one_iff] at hi
      exact hne hi
    · rw [pow_succ] at ho
      exact Nat.not_even_iff_odd.mpr ho (even_two.mul_left _)
  have hcomm : Commute (a ^ k) r := by
    have h := Subgroup.mem_centralizer_iff.mp hr (a ^ (k : ℤ)) (Set.mem_singleton _)
    rw [zpow_natCast] at h
    exact h
  exact not_odd_orderOf_mul hodd hcomm hro ⟨i, hi⟩

theorem character_one_eq_finrank (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index) :
    (basis.representation χ).character 1 =
      ((Module.finrank ℂ (basis.representation χ).vector : ℤ) : ℂ) := by
  rw [FiniteComplexRepresentation.character, Representation.char_one]
  push_cast
  rfl

theorem six_principal_characters_of_localHyp
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f) {q : ℕ} (hq : p ^ f = q) (hq4 : q % 4 = 1)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    ∃ χ : Fin 6 → basis.index,
      (∀ i, χ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) ∧
      χ 0 = principal ∧
      (basis.representation (χ 0)).character 1 = 1 ∧
      (basis.representation (χ 1)).character 1 = (q : ℂ) ^ 3 ∧
      (basis.representation (χ 2)).character 1 = (q : ℂ) * ((q : ℂ) ^ 2 + q + 1) ∧
      (basis.representation (χ 3)).character 1 = (q : ℂ) ^ 2 + q + 1 ∧
      (basis.representation (χ 4)).character 1 = (q : ℂ) ^ 3 - 1 ∧
      (basis.representation (χ 5)).character 1 = ((q : ℂ) + 1) * ((q : ℂ) ^ 2 + q + 1) ∧
      ∀ g : G, Odd (orderOf g) →
        -1 + (basis.representation (χ 1)).character g =
            (basis.representation (χ 2)).character g -
              (basis.representation (χ 3)).character g ∧
          (basis.representation (χ 2)).character g -
              (basis.representation (χ 3)).character g =
            (basis.representation (χ 4)).character g ∧
          (basis.representation (χ 2)).character g + (basis.representation (χ 3)).character g =
            (basis.representation (χ 5)).character g := by
  classical
  let _ : Fintype (centralizerOddCoreQuotient n S e) := Fintype.ofFinite _
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  have hm4 : 4 ≤ 2 ^ n := calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨θ, hθ⟩ : ∃ θ : ℂ, IsPrimitiveRoot θ (2 * 2 ^ n) :=
    ⟨_, Complex.isPrimitiveRoot_exp _ (by positivity)⟩
  have hζ : IsPrimitiveRoot (θ ^ 2) (2 ^ n) := hθ.pow (by positivity) rfl
  obtain ⟨-, H⟩ := conditional_global_principal_degrees_and_involution_values_of_localHyp n hn S
    e p f hp hpodd hf hloc ideal basis principal hprincipal
  obtain ⟨F, _, _, Sigma, b, hSigma, ρ, Ψ, hdata⟩ := hloc.modelData
  obtain ⟨⟨σ0, υ0, g0, hσ⟩, H2⟩ := H F Sigma b hSigma ρ Ψ hdata
  obtain ⟨⟨v, hv⟩, H4⟩ := H2 (θ ^ 2) hζ θ hθ rfl
  obtain ⟨⟨lam, hlam⟩, H6⟩ := H4 v hv ⟨σ0, hσ.left_mem⟩ ⟨υ0, hσ.right_mem⟩ g0 hσ
  obtain ⟨⟨α, β, η, σ', χ, δ, e₀, hcons⟩, H8⟩ := H6 lam hlam
  obtain ⟨⟨ω, iB, iD, τ₀, κ, γ, εs, hcore, heven⟩, H10⟩ := H8 α β η σ' χ δ e₀ hcons
  obtain ⟨V, hV1, hV2⟩ := exists_orbitRepresentatives (2 ^ n)
  obtain ⟨⟨P, Q, er, ψ, ρ₀, Δ, hwit⟩, H12⟩ := H10 ω iB iD τ₀ κ γ εs hcore heven V hV1 hV2
  obtain ⟨⟨hσ'', hτ₀, hκ, hρ₀⟩, ⟨hdA, hdB, hdD, -, hdχ, -, hdψ, -⟩, -, -, -, -, hVcard, -⟩ :=
    H12 P Q er ψ ρ₀ Δ hwit
  obtain ⟨-, -, -, -, -, -, -, -, hY0, hXj, hC, -, -⟩ := hcore.2
  obtain ⟨-, hαB, -, -, -, -, hχB, -⟩ := hcons
  obtain ⟨-, -, -, -, -, -, -, -, -, hψV, -, -, -⟩ := hwit
  obtain ⟨hyord, -, -, -, -, -, -, hSR⟩ :=
    (conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp n hn S e p f hp
      hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨-, hcr, -⟩ := hSR (θ ^ 2) hζ θ hθ rfl
  obtain ⟨vG, -, -, huniqG, -⟩ :=
    (conditional_global_central_section_integral_fourier_columns_of_localHyp n hn S e p f hp hpodd
      hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata (θ ^ 2) hζ
  obtain ⟨-, -, -, -, -, -, -, -, hGBζ⟩ :=
    (conditional_general_base_integral_columns_and_second_row_reconstruction_of_localHyp n hn S e
      p f hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨-, hGBv⟩ := hGBζ (θ ^ 2) hζ θ hθ rfl
  obtain ⟨-, hGBlam⟩ := hGBv v hv ⟨σ0, hσ.left_mem⟩ ⟨υ0, hσ.right_mem⟩ g0 hσ
  obtain ⟨-, -, -, -, -, -, -, -, hodd, -⟩ := hGBlam lam hlam
  have hqF : Nat.card F = q := hdata.card.trans hq
  have hε : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 := by simp [hqF, hq4]
  have hε0 : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) ≠ 0 := by rw [hε]; norm_num
  have hprin : principal ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
    coefficientBlock_self_mem basis _ principal
  have h1J : 1 ∈ (Finset.Ico 1 (2 ^ n)).filter Odd :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩, odd_one⟩
  have hVpos : 0 < (V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card := by
    rw [hVcard]
    apply Nat.div_pos _ (by norm_num)
    calc 8 = 4 * 2 := by norm_num
      _ ≤ 2 ^ n * (2 ^ n - 2) := Nat.mul_le_mul hm4 (by omega)
  obtain ⟨I₀, hI₀⟩ := Finset.card_pos.mp hVpos
  have hI₀V : I₀ ∈ V := (Finset.mem_filter.mp hI₀).1
  obtain ⟨hψB, -, -, -, -, -, -, -, hψcf, -⟩ := hψV I₀ hI₀V
  have hrows : ∀ (j : ℕ) (ℓ : Fin 2) (z : G), Odd (orderOf z) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        fourierTransform (2 ^ n) (θ ^ 2) (fun k => v χ k ℓ) j *
          (basis.representation χ).character z = 0 := fun j ℓ z hz =>
    sum_fourierTransform_mul_eq_zero basis ideal principal _ _ _ _ _ hε0 v hv
      (fun k hk w hw => (huniqG principal hprin k hk w hw).trans
        (huniqG principal hprin k hk _ fun r hr hro => hv principal hprin k hk r hr hro).symm)
      (fun k hk r hr hro => not_odd_orderOf_pow_mul (orderOf_wreathModelHom_a n S e) hk hr hro)
      (θ ^ 2) j ℓ hz
  refine ⟨![principal, α e₀, α iD, α iB, χ 1, ψ I₀], ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hprin
    · exact (hαB e₀).1
    · exact (hαB iD).1
    · exact (hαB iB).1
    · exact (hχB 1 h1J).1
    · exact hψB
  · show (basis.representation principal).character 1 = 1
    rw [hprincipal]
    rfl
  all_goals simp only [hε] at hσ'' hκ hρ₀ hdB hdD hdχ hdψ
  · show (basis.representation (α e₀)).character 1 = _
    rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (α e₀)).vector : ℤ)
      = (Nat.card F : ℤ) ^ 3 from hdA, hqF]
    push_cast
    ring
  · show (basis.representation (α iD)).character 1 = _
    rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (α iD)).vector : ℤ)
      = Nat.card F * ((Nat.card F : ℤ) ^ 2 + 1 * Nat.card F + 1) from hdD, hqF]
    push_cast
    ring
  · show (basis.representation (α iB)).character 1 = _
    rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (α iB)).vector : ℤ)
      = (Nat.card F : ℤ) ^ 2 + 1 * Nat.card F + 1 from hdB, hqF]
    push_cast
    ring
  · show (basis.representation (χ 1)).character 1 = _
    rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (χ 1)).vector : ℤ)
      = (Nat.card F : ℤ) ^ 3 - 1 from hdχ 1 h1J, hqF]
    push_cast
    ring
  · show (basis.representation (ψ I₀)).character 1 = _
    rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (ψ I₀)).vector : ℤ)
      = (Nat.card F + 1) * ((Nat.card F : ℤ) ^ 2 + 1 * Nat.card F + 1) from hdψ I₀ hI₀V, hqF]
    push_cast
    ring
  · intro g hg
    have eY := (congrFun hY0 g).symm.trans (sum_squareRootColumn_mul_eq_zero basis ideal
      principal hyord _ (θ ^ 2) 0 _ (fun χ hχ => hcr χ hχ 0 (by omega)) hg)
    have eX := apply_eq_zero_of_sum_smul_eq basis _ _ (hXj 1 h1J) (hrows 1 0 g hg)
    have eC := apply_eq_zero_of_sum_smul_eq basis _ _ hC (sum_mul_eq_zero_of_conj basis _ _
      (hodd ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n))) hg)
    have eψ := apply_eq_zero_of_sum_smul_eq basis _ _ hψcf (sum_mul_eq_zero_of_conj basis _ _
      (hodd I₀.1 I₀.2) hg)
    subst hσ'' hτ₀ hκ hρ₀
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul] at eY eX eC eψ
    push_cast at eY eX eC eψ
    show -1 + (basis.representation (α e₀)).character g =
        (basis.representation (α iD)).character g - (basis.representation (α iB)).character g ∧
      (basis.representation (α iD)).character g - (basis.representation (α iB)).character g =
        (basis.representation (χ 1)).character g ∧
      (basis.representation (α iD)).character g + (basis.representation (α iB)).character g =
        (basis.representation (ψ I₀)).character g
    refine ⟨by linear_combination -eY, by linear_combination (1 / 2 : ℂ) * eX + (1 / 2 : ℂ) * eY,
      by linear_combination eψ - eC⟩

end CFSG.Wreathed.BrauerWreathedOrder

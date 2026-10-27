module

public import CFSG.CharacterTheory.Wreathed.FourPointThreePairsColumns
public import CFSG.CharacterTheory.Wreathed.FourPointOrderEight
public import CFSG.CharacterTheory.Wreathed.FourPointThreePairsDichotomy
public import CFSG.CharacterTheory.Wreathed.FourPointThreePairsRoot

public noncomputable section

namespace CFSG.Wreathed.FourPointThreePairs

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.FourPointOrderFour
  CFSG.Wreathed.FourPointGaussianColumns CFSG.Wreathed.FourPointCentralFourier
  CFSG.Wreathed.FourPointOrderEight CFSG.Wreathed.WreathCentralSquare
  CFSG.Wreathed.SquareRootSmallCharacterRigidity

open scoped BigOperators Classical

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_fourier_support_three_pairs_and_adjacent_degrees
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let H := centralizerOddCoreQuotient n S e
    let N := involutionCentralizer n S e
    let π := centralizerOddCoreMap n S e
    let aN : N := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))
    let s : G := wreathModelHom S e (Original.s (2 ^ n))
    let w : G := wreathModelHom S e (Original.z (2 ^ n))
    let a : G := wreathModelHom S e (Original.a (2 ^ n))
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let C := orderFourCentralizer n S e
    let ρ : G := s * w
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let u := cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let iF := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let U₀ : W := iF (CentralSL2.upperSL (ZMod 3) 1)
    n = 2 ∧ (∃ Φ : W ≃* H, Φ (u ^ 2) = π aN) ∧
    ∀ Φ : W ≃* H, Φ (u ^ 2) = π aN →
      (∃ z : N, (z : G) ∈ C ∧ Odd (orderOf z) ∧ π z = Φ U₀) ∧
      ∀ z : N, (z : G) ∈ C → Odd (orderOf z) → π z = Φ U₀ →
        ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
          (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
          (_ : (basis.representation principal).character = 1) (i : ℂ), i ^ 2 = -1 →
          let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
          let X : basis.index → G → ℂ := fun χ => (basis.representation χ).character
          let d : basis.index → ℂ := fun χ => X χ 1
          let Ax : basis.index → ℂ := fun χ => X χ x
          let Bx : basis.index → ℂ := fun χ => X χ (x * z)
          let T : basis.index → ℂ := fun χ => X χ a
          let Ua : basis.index → ℂ := fun χ => X χ (a * z)
          let v : basis.index → ℕ → Fin 2 → ℂ := fun χ n' =>
            if n' = 1 then ![(T χ + 2 * Ua χ) / 3, (T χ - Ua χ) / 3]
            else if n' = 2 then ![(Ax χ + 2 * Bx χ) / 3, (Ax χ - Bx χ) / 3]
            else ![starRingEnd ℂ ((T χ + 2 * Ua χ) / 3), starRingEnd ℂ ((T χ - Ua χ) / 3)]
          let f : basis.index → ℕ → Fin 2 → ℂ := fun χ j ℓ =>
            (1 / 4) * ∑ n' ∈ Finset.Icc 1 3, (i ^ (j * n') - 1) * v χ n' ℓ
          let P : basis.index → ℝ := fun χ => (X χ ρ).re
          let Q : basis.index → ℝ := fun χ => imCoeff i (X χ ρ)
          let L : ℕ → basis.index → ℂ := fun j χ => f χ j 0
          let deg : basis.index → ℕ := fun χ => Module.finrank ℂ (basis.representation χ).vector
          let E := B₀.filter (fun χ => P χ ≠ 0)
          let J := B₀.filter (fun χ => Q χ ≠ 0)
          let Eplus : ℕ → Finset basis.index := fun j => E.filter (fun χ => L j χ = P χ)
          let Eminus : ℕ → Finset basis.index := fun j => E.filter (fun χ => L j χ = -P χ)
          (∀ χ ∈ B₀, (∃ k : ℤ, imCoeff i (T χ) = 2 * k) ∧
            (∃ k : ℤ, L 1 χ = P χ + 2 * k) ∧ (∃ k : ℤ, L 3 χ = P χ + 2 * k) ∧
            (∃ k : ℤ, L 1 χ = L 3 χ + 2 * k) ∧ (∃ k : ℤ, L 2 χ = P χ + Q χ + 2 * k) ∧
            ∃ k : ℤ, d χ = P χ + Q χ + 2 * k) ∧
          E.card = 4 ∧ J.card = 4 ∧ principal ∈ E ∧ principal ∉ J ∧
          ((E ∩ J).card = 0 ∨ (E ∩ J).card = 2) ∧
          B₀.filter (fun χ => Odd (deg χ)) = symmDiff E J ∧
          ((E ∩ J).card = 0 → (B₀.filter (fun χ => Odd (deg χ))).card = 8) ∧
          ((E ∩ J).card = 2 → (B₀.filter (fun χ => Odd (deg χ))).card = 4) ∧
          ∃ χ₁ ψ₁ χ₂ ψ₂ χ₃ ψ₃ : basis.index,
            (∀ g, X ψ₁ g = starRingEnd ℂ (X χ₁ g)) ∧ (∀ g, X ψ₂ g = starRingEnd ℂ (X χ₂ g)) ∧
            (∀ g, X ψ₃ g = starRingEnd ℂ (X χ₃ g)) ∧ [χ₁, ψ₁, χ₂, ψ₂, χ₃, ψ₃].Nodup ∧
            B₀.filter (fun χ => imCoeff i (Ua χ) ≠ 0) = {χ₁, ψ₁, χ₂, ψ₂, χ₃, ψ₃} ∧
            imCoeff i (Ua χ₁) = 1 ∧ imCoeff i (Ua χ₂) = 1 ∧ imCoeff i (Ua χ₃) = 1 ∧
            imCoeff i (T χ₁) = 4 ∧ imCoeff i (T χ₂) = -2 ∧ imCoeff i (T χ₃) = -2 ∧
            (∀ χ ∈ B₀, χ ∉ ({χ₁, ψ₁, χ₂, ψ₂, χ₃, ψ₃} : Finset basis.index) →
              imCoeff i (T χ) = 0 ∧ imCoeff i (Ua χ) = 0) ∧
            ∃ (η β : ℕ → basis.index) (ε : ℕ → ℤ),
              (∀ j ∈ ({1, 3} : Finset ℕ),
                η j ∈ B₀ ∧ η j ∉ E ∧ (ε j = 1 ∨ ε j = -1) ∧ L j (η j) = 2 * ε j ∧
                (∀ χ ∈ B₀, χ ∉ E → χ ≠ η j → L j χ = 0) ∧
                (∀ χ ∈ E, L j χ = 1 ∨ L j χ = -1) ∧
                (Eplus j).card = 2 ∧ (Eminus j).card = 2 ∧ Eminus j = {principal, β j} ∧
                β j ≠ principal ∧ d (η j) = ‖1 + P (β j) * d (β j)‖ ∧
                (d (η j) = d (β j) - 1 ∨ d (η j) = d (β j) + 1) ∧
                ∑ χ ∈ Eplus j, P χ * d χ = -ε j * d (η j) ∧
                ∑ χ ∈ Eminus j, P χ * d χ = ε j * d (η j) ∧
                ∀ ψ ∈ ({η j, β j} : Finset basis.index), (basis.representation ψ).IsIrreducible ∧
                  (basis.representation ψ).character ≠ 1 ∧
                  MonoidHom.ker (basis.representation ψ).representation = ⊥ ∧ 2 ≤ deg ψ) ∧
              (∀ g, X (η 3) g = starRingEnd ℂ (X (η 1) g)) ∧ ε 3 = ε 1 ∧
              (∀ g, X (β 3) g = starRingEnd ℂ (X (β 1) g)) ∧
              (η 1 ≠ η 3 →
                ({χ₁, ψ₁} : Finset basis.index) = {η 1, η 3} ∧ ∀ χ ∈ E, L 1 χ = L 3 χ) ∧
              (η 1 = η 3 → (∀ g, X (η 1) g = starRingEnd ℂ (X (η 1) g)) ∧ χ₁ ∈ E ∧ ψ₁ ∈ E) := by
  intro H N π aN s w a x C ρ W u iF U₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  subst hn2
  obtain ⟨-, hΦex, hGc⟩ :=
    four_point_central_section_integral_fourier_columns hnonab 2 hn S e alpha
  obtain ⟨-, -, -, hρ2, hρ4, -, -, -, -, -, -, -, -, -, -, hGo⟩ :=
    four_point_order_eight_centralizer_and_norm_four_columns hnonab 2 hn S e alpha
  obtain ⟨-, -, hGg⟩ :=
    four_point_global_gaussian_columns_and_conjugate_pair_dichotomy hnonab 2 hn S e alpha
  refine ⟨rfl, hΦex, ?_⟩
  intro Φ hΦ
  obtain ⟨hzex, hGc'⟩ := hGc Φ hΦ
  obtain ⟨-, hGo'⟩ := hGo Φ hΦ
  obtain ⟨⟨y, hy2, hyΦ⟩, -, hGg'⟩ := hGg Φ hΦ
  refine ⟨hzex, ?_⟩
  intro z hzC hzodd hzΦ ideal _ _ basis principal hprincipal i hi B₀ X d Ax Bx T Ua v f P Q L deg
    E J Eplus Eminus
  obtain ⟨c1, -, c3, c4, -, -, -, c8, c9⟩ :=
    hGc' z hzC hzodd hzΦ ideal basis principal hprincipal i hi
  obtain ⟨-, -, -, -, -, o6, -, o8, o9, o10, o11, o12, o13, o14, o15, o16, -⟩ :=
    hGo' z hzC hzodd hzΦ ideal basis principal hprincipal i hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, gdich, -⟩ :=
    hGg' y hy2 hyΦ z hzC hzodd hzΦ ideal basis principal hprincipal i hi
  have hfint : ∀ χ ∈ B₀, ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, ∃ k : ℤ, f χ j ℓ = k := c1
  have hfdeg : ∀ j ℓ, ∑ χ ∈ B₀, d χ * f χ j ℓ = 0 := c3
  have hfprin : ∀ j ∈ Finset.Icc 1 3, f principal j 0 = -1 ∧ f principal j 1 = 0 := c4
  have hfconj : ∀ χ ∈ B₀, ∀ χ' : basis.index, (∀ g, X χ' g = starRingEnd ℂ (X χ g)) →
      ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, f χ' j ℓ = f χ (4 - j) ℓ := c8
  have hfnorm : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3,
      ∑ χ ∈ B₀, f χ j 0 * f χ k 0 = if j = k then 8 else 4 := c9
  have hPd : ∑ χ ∈ B₀, d χ * P χ = 0 := o6
  have hPp : P principal = 1 := o8
  have hQp : Q principal = 0 := o9
  have hPf : ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, ∑ χ ∈ B₀, (P χ : ℂ) * f χ j ℓ = 0 ∧
      ∑ χ ∈ B₀, (Q χ : ℂ) * f χ j ℓ = 0 := o10
  have hEcard : E.card = 4 := o11
  have hPunit : ∀ χ ∈ B₀, P χ ≠ 0 → P χ = 1 ∨ P χ = -1 := o12
  have hJcard : J.card = 4 := o13
  have hQunit : ∀ χ ∈ B₀, Q χ ≠ 0 → Q χ = 1 ∨ Q χ = -1 := o14
  have hJpairs : ∃ χ₁ ψ₁ χ₂ ψ₂ : basis.index,
      (∀ g, X ψ₁ g = starRingEnd ℂ (X χ₁ g)) ∧ (∀ g, X ψ₂ g = starRingEnd ℂ (X χ₂ g)) ∧
      χ₁ ≠ ψ₁ ∧ χ₁ ≠ χ₂ ∧ χ₁ ≠ ψ₂ ∧ ψ₁ ≠ χ₂ ∧ ψ₁ ≠ ψ₂ ∧ χ₂ ≠ ψ₂ ∧
      J = {χ₁, ψ₁, χ₂, ψ₂} := o15
  have hpE : principal ∈ E := o16
  have hdich : GaussianPairDichotomy basis B₀ i T Ua := gdich
  clear c1 c3 c4 c8 c9 o6 o8 o9 o10 o11 o12 o13 o14 o15 o16 gdich hGc hGo hGg hGc' hGo' hGg'
  have hi0 : i.re = 0 := (re_eq_zero_and_im_sq_eq_one hi).1
  have hpr : principal ∈ B₀ := coefficientBlock_self_mem basis _ principal
  have hEB : E ⊆ B₀ := Finset.filter_subset _ _
  have hρ : ρ = actualRoot S e := (actualRoot_eq S e).symm
  have hρ2' : ρ ^ 2 = a := hρ2
  have hρ4' : ρ ^ 4 = x := hρ4
  have hρ8 : ρ ^ 8 = 1 := by
    rw [hρ, show (8 : ℕ) = 2 * 2 ^ 2 by norm_num, ← actualRoot_orderOf 2 hn S e]
    exact pow_orderOf_eq_one _
  have hσB : ∀ χ ∈ B₀, conjLabel basis χ ∈ B₀ :=
    conjLabel_mem_coefficientBlock basis _ principal hprincipal
  have hσp : conjLabel basis principal = principal :=
    conjLabel_eq_of_spec basis principal principal fun g => by
      rw [hprincipal]
      simp
  have hXσ : ∀ χ g, X (conjLabel basis χ) g = starRingEnd ℂ (X χ g) := conjLabel_spec basis
  have hPσ : ∀ χ, P (conjLabel basis χ) = P χ := fun χ => by
    change (X (conjLabel basis χ) ρ).re = (X χ ρ).re
    rw [hXσ, Complex.conj_re]
  have hd : ∀ χ, d χ = (deg χ : ℂ) := fun χ => by
    change (basis.representation χ).character 1 = _
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  have hdp : deg principal = 1 := by
    have h := hd principal
    rw [show d principal = 1 by
      change (basis.representation principal).character 1 = 1
      rw [hprincipal]
      rfl] at h
    exact_mod_cast h.symm
  have hirr : ∀ ψ ∈ B₀, ψ ≠ principal → (basis.representation ψ).IsIrreducible ∧
      (basis.representation ψ).character ≠ 1 ∧
      MonoidHom.ker (basis.representation ψ).representation = ⊥ ∧ 2 ≤ deg ψ := by
    intro ψ _ hne
    have hc : (basis.representation ψ).character ≠ 1 := fun h =>
      hne (basis.distinct (h.trans hprincipal.symm))
    exact ⟨basis.irreducible ψ, hc, ker_eq_bot_of_character_ne_one _ (basis.irreducible ψ) hc,
      two_le_finrank_of_character_ne_one hnonab _ (basis.irreducible ψ) hc⟩
  have hdeg2 : ∀ χ ∈ B₀, χ ≠ principal → 2 ≤ deg χ := fun χ hχ hne =>
    (hirr χ hχ hne).2.2.2
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_pow_nat_eq i (by norm_num : 0 < 2)
  let ν : basis.index → ℕ → ℕ := fun χ t =>
    cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) η t
  have hν15 : ∀ χ, ν χ 1 = ν χ 5 := fun χ =>
    (root_eigen_facts S e (basis.representation χ) hi hη).1
  have hν37 : ∀ χ, ν χ 3 = ν χ 7 := fun χ =>
    (root_eigen_facts S e (basis.representation χ) hi hη).2.1
  have hXρ : ∀ χ, X χ ρ =
      (((ν χ 0 : ℤ) - ν χ 4 : ℤ) : ℂ) + (((ν χ 2 : ℤ) - ν χ 6 : ℤ) : ℂ) * i := fun χ => by
    rw [hρ]
    exact (root_eigen_facts S e (basis.representation χ) hi hη).2.2.1
  have hTν : ∀ χ, T χ = (((ν χ 0 : ℤ) + ν χ 4 - ν χ 2 - ν χ 6 : ℤ) : ℂ) +
      ((2 * ((ν χ 1 : ℤ) - ν χ 3) : ℤ) : ℂ) * i := fun χ => by
    change X χ a = _
    rw [← hρ2', hρ]
    exact (root_eigen_facts S e (basis.representation χ) hi hη).2.2.2.1
  have hdegν : ∀ χ, (deg χ : ℤ) = ∑ t ∈ Finset.range 8, (ν χ t : ℤ) := fun χ =>
    (root_eigen_facts S e (basis.representation χ) hi hη).2.2.2.2.1
  have hfourν : ∀ χ, ∀ j, 1 ≤ j → j < 4 → (4 : ℂ)⁻¹ * ∑ k ∈ Finset.range 4,
      (i ^ (j * k) - 1) * X χ (ρ ^ (2 * k)) =
        (((ν χ (4 - j) : ℤ) + ν χ (8 - j) - ν χ 0 - ν χ 4 : ℤ) : ℂ) := fun χ => by
    rw [hρ]
    exact (root_eigen_facts S e (basis.representation χ) hi hη).2.2.2.2.2
  let Pz : basis.index → ℤ := fun χ => (ν χ 0 : ℤ) - ν χ 4
  let Qz : basis.index → ℤ := fun χ => (ν χ 2 : ℤ) - ν χ 6
  have hPz : ∀ χ, P χ = Pz χ := fun χ => by
    change (X χ ρ).re = _
    rw [hXρ χ]
    simp [hi0, Pz]
  have hQz : ∀ χ, Q χ = Qz χ := fun χ => by
    change imCoeff i (X χ ρ) = _
    rw [hXρ χ, ← Complex.ofReal_intCast, ← Complex.ofReal_intCast, imCoeff_add_mul hi]
  have hPc : ∀ χ, (P χ : ℂ) = (Pz χ : ℂ) := fun χ => by rw [hPz χ, Complex.ofReal_intCast]
  have hQc : ∀ χ, (Q χ : ℂ) = (Qz χ : ℂ) := fun χ => by rw [hQz χ, Complex.ofReal_intCast]
  have hfloor : ∀ t : ℂ, (∃ k : ℤ, t = k) → t = (⌊t.re⌋ : ℤ) := by
    rintro t ⟨k, rfl⟩
    rw [Complex.intCast_re, Int.floor_intCast]
  let Lz : ℕ → basis.index → ℤ := fun j χ => ⌊(f χ j 0).re⌋
  let Mz : ℕ → basis.index → ℤ := fun j χ => ⌊(f χ j 1).re⌋
  have hLz : ∀ j ∈ Finset.Icc 1 3, ∀ χ ∈ B₀, f χ j 0 = Lz j χ :=
    fun j hj χ hχ => hfloor _ (hfint χ hχ j hj 0)
  have hMz : ∀ j ∈ Finset.Icc 1 3, ∀ χ ∈ B₀, f χ j 1 = Mz j χ :=
    fun j hj χ hχ => hfloor _ (hfint χ hχ j hj 1)
  have hrow : ∀ χ, ∀ j, 1 ≤ j → j < 4 → f χ j 0 + 2 * f χ j 1 =
      (((ν χ (4 - j) : ℤ) + ν χ (8 - j) - ν χ 0 - ν χ 4 : ℤ) : ℂ) := by
    intro χ j hj1 hj4
    rw [← hfourν χ j hj1 hj4]
    refine fourier_rows_at_one i (v χ) (fun k => X χ (ρ ^ (2 * k))) ?_ ?_ ?_ j
    · change (T χ + 2 * Ua χ) / 3 + 2 * ((T χ - Ua χ) / 3) = X χ (ρ ^ (2 * 1))
      rw [mul_one, hρ2']
      change (T χ + 2 * Ua χ) / 3 + 2 * ((T χ - Ua χ) / 3) = T χ
      ring
    · change (Ax χ + 2 * Bx χ) / 3 + 2 * ((Ax χ - Bx χ) / 3) = X χ (ρ ^ (2 * 2))
      rw [show (2 * 2 : ℕ) = 4 from rfl, hρ4']
      change (Ax χ + 2 * Bx χ) / 3 + 2 * ((Ax χ - Bx χ) / 3) = Ax χ
      ring
    · change starRingEnd ℂ ((T χ + 2 * Ua χ) / 3) + 2 * starRingEnd ℂ ((T χ - Ua χ) / 3) =
        X χ (ρ ^ (2 * 3))
      have h6 : ρ ^ (2 * 3) = (ρ ^ 2)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_add, show 2 * 3 + 2 = 8 from rfl, hρ8]
      rw [h6, hρ2']
      change _ = (basis.representation χ).character a⁻¹
      rw [← finite_character_conjugate_inverse]
      change _ = starRingEnd ℂ (T χ)
      simp only [map_div₀, map_add, map_sub, map_mul, map_ofNat]
      ring
  have hparity : ∀ χ ∈ B₀, (∃ k : ℤ, imCoeff i (T χ) = 2 * k) ∧
      (∃ k : ℤ, L 1 χ = P χ + 2 * k) ∧ (∃ k : ℤ, L 3 χ = P χ + 2 * k) ∧
      (∃ k : ℤ, L 1 χ = L 3 χ + 2 * k) ∧ (∃ k : ℤ, L 2 χ = P χ + Q χ + 2 * k) ∧
      ∃ k : ℤ, d χ = P χ + Q χ + 2 * k := by
    intro χ hχ
    have h1 : f χ 1 0 + 2 * f χ 1 1 = (((ν χ 3 : ℤ) + ν χ 7 - ν χ 0 - ν χ 4 : ℤ) : ℂ) :=
      hrow χ 1 le_rfl (by norm_num)
    have h2 : f χ 2 0 + 2 * f χ 2 1 = (((ν χ 2 : ℤ) + ν χ 6 - ν χ 0 - ν χ 4 : ℤ) : ℂ) :=
      hrow χ 2 (by norm_num) (by norm_num)
    have h3 : f χ 3 0 + 2 * f χ 3 1 = (((ν χ 1 : ℤ) + ν χ 5 - ν χ 0 - ν χ 4 : ℤ) : ℂ) :=
      hrow χ 3 (by norm_num) (by norm_num)
    rw [hLz 1 (by decide) χ hχ, hMz 1 (by decide) χ hχ] at h1
    rw [hLz 2 (by decide) χ hχ, hMz 2 (by decide) χ hχ] at h2
    rw [hLz 3 (by decide) χ hχ, hMz 3 (by decide) χ hχ] at h3
    have z1 : Lz 1 χ + 2 * Mz 1 χ = (ν χ 3 : ℤ) + ν χ 7 - ν χ 0 - ν χ 4 := by exact_mod_cast h1
    have z2 : Lz 2 χ + 2 * Mz 2 χ = (ν χ 2 : ℤ) + ν χ 6 - ν χ 0 - ν χ 4 := by exact_mod_cast h2
    have z3 : Lz 3 χ + 2 * Mz 3 χ = (ν χ 1 : ℤ) + ν χ 5 - ν χ 0 - ν χ 4 := by exact_mod_cast h3
    have hdz := hdegν χ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hdz
    have e15 := hν15 χ
    have e37 := hν37 χ
    have hPzχ : Pz χ = (ν χ 0 : ℤ) - ν χ 4 := rfl
    have hQzχ : Qz χ = (ν χ 2 : ℤ) - ν χ 6 := rfl
    have hL1 : L 1 χ = (Lz 1 χ : ℂ) := hLz 1 (by decide) χ hχ
    have hL2 : L 2 χ = (Lz 2 χ : ℂ) := hLz 2 (by decide) χ hχ
    have hL3 : L 3 χ = (Lz 3 χ : ℂ) := hLz 3 (by decide) χ hχ
    refine ⟨⟨(ν χ 1 : ℤ) - ν χ 3, ?_⟩, ⟨(ν χ 3 : ℤ) - ν χ 0 - Mz 1 χ, ?_⟩,
      ⟨(ν χ 1 : ℤ) - ν χ 0 - Mz 3 χ, ?_⟩, ⟨(ν χ 3 : ℤ) - ν χ 1 - Mz 1 χ + Mz 3 χ, ?_⟩,
      ⟨(ν χ 6 : ℤ) - ν χ 0 - Mz 2 χ, ?_⟩, ⟨(ν χ 1 : ℤ) + ν χ 3 + ν χ 4 + ν χ 6, ?_⟩⟩
    · rw [hTν χ, ← Complex.ofReal_intCast, ← Complex.ofReal_intCast, imCoeff_add_mul hi]
      push_cast
      ring
    · rw [hL1, hPc χ, show Lz 1 χ = Pz χ + 2 * ((ν χ 3 : ℤ) - ν χ 0 - Mz 1 χ) by omega]
      push_cast
      ring
    · rw [hL3, hPc χ, show Lz 3 χ = Pz χ + 2 * ((ν χ 1 : ℤ) - ν χ 0 - Mz 3 χ) by omega]
      push_cast
      ring
    · rw [hL1, hL3, show Lz 1 χ = Lz 3 χ + 2 * ((ν χ 3 : ℤ) - ν χ 1 - Mz 1 χ + Mz 3 χ) by omega]
      push_cast
      ring
    · rw [hL2, hPc χ, hQc χ,
        show Lz 2 χ = Pz χ + Qz χ + 2 * ((ν χ 6 : ℤ) - ν χ 0 - Mz 2 χ) by omega]
      push_cast
      ring
    · rw [hd χ, hPc χ, hQc χ, show (deg χ : ℂ) = ((deg χ : ℤ) : ℂ) by push_cast; rfl,
        show (deg χ : ℤ) = Pz χ + Qz χ + 2 * ((ν χ 1 : ℤ) + ν χ 3 + ν χ 4 + ν χ 6) by omega]
      push_cast
      ring
  obtain ⟨χ₁, χ₂, χ₃, hnodup, hfilterU, hU1, hU2, hU3, hT1, hT2, hT3, hrestTU⟩ :=
    three_pairs_of_dichotomy basis B₀ i T Ua (fun χ => hXσ χ a) (fun χ => hXσ χ (a * z)) hdich
      fun χ hχ => (hparity χ hχ).1
  have hχ₁B : χ₁ ∈ B₀ := by
    have h : χ₁ ∈ B₀.filter (fun χ => imCoeff i (Ua χ) ≠ 0) := by
      rw [hfilterU]
      simp
    exact (Finset.mem_filter.mp h).1
  have hpJ : principal ∉ J := fun h => (Finset.mem_filter.mp h).2 hQp
  have hconjE : ∀ χ ψ, χ ∈ B₀ → (∀ g, X ψ g = starRingEnd ℂ (X χ g)) → (χ ∈ E ↔ ψ ∈ E) := by
    intro χ ψ hχ hψ
    have hψσ : conjLabel basis χ = ψ := conjLabel_eq_of_spec basis χ ψ hψ
    rw [← hψσ, Finset.mem_filter, Finset.mem_filter, hPσ]
    exact ⟨fun h => ⟨hσB χ hχ, h.2⟩, fun h => ⟨hχ, h.2⟩⟩
  have hinter : (E ∩ J).card = 0 ∨ (E ∩ J).card = 2 := by
    obtain ⟨χ₁', ψ₁', χ₂', ψ₂', hψ₁', hψ₂', h1, h2, h3, h4, h5, h6, hJeq⟩ := hJpairs
    have hmem : ∀ t ∈ ({χ₁', ψ₁', χ₂', ψ₂'} : Finset basis.index), t ∈ B₀ := fun t ht =>
      (Finset.mem_filter.mp (hJeq ▸ ht : t ∈ J)).1
    rw [hJeq]
    exact card_inter_two_pairs E χ₁' ψ₁' χ₂' ψ₂' principal h1 h2 h3 h4 h5 h6
      (hconjE χ₁' ψ₁' (hmem _ (by simp)) hψ₁') (hconjE χ₂' ψ₂' (hmem _ (by simp)) hψ₂')
      hEcard hpE (hJeq ▸ hpJ)
  have hPunitz : ∀ χ ∈ B₀, Pz χ = 0 ∨ Pz χ = 1 ∨ Pz χ = -1 := by
    intro χ hχ
    by_cases h : P χ = 0
    · left
      rw [hPz χ] at h
      exact_mod_cast h
    · right
      rcases hPunit χ hχ h with h' | h' <;> rw [hPz χ] at h'
      · left
        exact_mod_cast h'
      · right
        exact_mod_cast h'
  have hQunitz : ∀ χ ∈ B₀, Qz χ = 0 ∨ Qz χ = 1 ∨ Qz χ = -1 := by
    intro χ hχ
    by_cases h : Q χ = 0
    · left
      rw [hQz χ] at h
      exact_mod_cast h
    · right
      rcases hQunit χ hχ h with h' | h' <;> rw [hQz χ] at h'
      · left
        exact_mod_cast h'
      · right
        exact_mod_cast h'
  have hdpar : ∀ χ ∈ B₀, ∃ k : ℤ, (deg χ : ℤ) = Pz χ + Qz χ + 2 * k := by
    intro χ _
    have hdz := hdegν χ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hdz
    have e15 := hν15 χ
    have e37 := hν37 χ
    refine ⟨(ν χ 1 : ℤ) + ν χ 3 + ν χ 4 + ν χ 6, ?_⟩
    have hPzχ : Pz χ = (ν χ 0 : ℤ) - ν χ 4 := rfl
    have hQzχ : Qz χ = (ν χ 2 : ℤ) - ν χ 6 := rfl
    omega
  have hEz : B₀.filter (fun χ => Pz χ ≠ 0) = E :=
    Finset.filter_congr fun χ _ => by rw [hPz χ, Int.cast_ne_zero]
  have hJz : B₀.filter (fun χ => Qz χ ≠ 0) = J :=
    Finset.filter_congr fun χ _ => by rw [hQz χ, Int.cast_ne_zero]
  have hodd : B₀.filter (fun χ => Odd (deg χ)) = symmDiff E J := by
    rw [← hEz, ← hJz]
    exact odd_filter_eq_symmDiff B₀ Pz Qz deg hPunitz hQunitz hdpar
  have hcardsd := card_symmDiff_add E J
  have hcolumn : ∀ j ∈ ({1, 3} : Finset ℕ), ∃ η ∈ B₀, η ∉ E ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      L j η = 2 * ε ∧ (∀ χ ∈ B₀, χ ∉ E → χ ≠ η → L j χ = 0) ∧
      (∀ χ ∈ E, L j χ = 1 ∨ L j χ = -1) ∧
      ∃ β ∈ E, β ≠ principal ∧ (Eplus j).card = 2 ∧ (Eminus j).card = 2 ∧
        Eminus j = {principal, β} ∧ d η = ‖1 + P β * d β‖ ∧
        (d η = d β - 1 ∨ d η = d β + 1) ∧ ∑ χ ∈ Eplus j, P χ * d χ = -ε * d η ∧
        ∑ χ ∈ Eminus j, P χ * d χ = ε * d η := by
    intro j hj
    have hj' : j ∈ Finset.Icc 1 3 := by
      rcases Finset.mem_insert.mp hj with rfl | h
      · decide
      · rw [Finset.mem_singleton.mp h]
        decide
    have hnorm := hfnorm j hj' j hj'
    rw [ite_eq_left rfl] at hnorm
    have hparj : ∀ χ ∈ B₀, ∃ k : ℤ, L j χ = P χ + 2 * k := by
      intro χ hχ
      rcases Finset.mem_insert.mp hj with rfl | h
      · exact (hparity χ hχ).2.1
      · rw [Finset.mem_singleton.mp h]
        exact (hparity χ hχ).2.2.1
    exact fourier_column_analysis B₀ P (L j) d Pz (Lz j) deg principal hpr hPz
      (fun χ hχ => hLz j hj' χ hχ) hd hEcard hPunit hnorm hparj (hPf j hj' 0).1 hPd
      (hfdeg j 0) hPp (hfprin j hj').1 hdp hdeg2
  obtain ⟨η₁, hη₁B, hη₁E, ε₁, hε₁, hL₁η, hz₁, hu₁, β₁, hβ₁E, hβ₁p, hcp₁, hcm₁, hEm₁, hdη₁,
    hdβ₁, hSp₁, hSm₁⟩ := hcolumn 1 (by decide)
  obtain ⟨η₃, hη₃B, hη₃E, ε₃, hε₃, hL₃η, hz₃, hu₃, β₃, hβ₃E, hβ₃p, hcp₃, hcm₃, hEm₃, hdη₃,
    hdβ₃, hSp₃, hSm₃⟩ := hcolumn 3 (by decide)
  have hPσz : ∀ χ, Pz (conjLabel basis χ) = Pz χ := fun χ => by
    have h := hPσ χ
    rw [hPz, hPz] at h
    exact_mod_cast h
  have hLσz : ∀ χ ∈ B₀, Lz 3 (conjLabel basis χ) = Lz 1 χ := fun χ hχ => by
    have h : f (conjLabel basis χ) 3 0 = f χ 1 0 :=
      hfconj χ hχ (conjLabel basis χ) (hXσ χ) 3 (by decide) 0
    rw [hLz 3 (by decide) _ (hσB χ hχ), hLz 1 (by decide) χ hχ] at h
    exact_mod_cast h
  have hEmem : ∀ χ ∈ B₀, χ ∈ E ↔ Pz χ ≠ 0 := fun χ hχ => by
    rw [Finset.mem_filter, hPz χ, Int.cast_ne_zero]
    exact ⟨fun h => h.2, fun h => ⟨hχ, h⟩⟩
  have hL1z : ∀ χ ∈ B₀, L 1 χ = (Lz 1 χ : ℂ) := hLz 1 (by decide)
  have hL3z : ∀ χ ∈ B₀, L 3 χ = (Lz 3 χ : ℂ) := hLz 3 (by decide)
  have hβ₁B : β₁ ∈ B₀ := hEB hβ₁E
  have hβ₁m : β₁ ∈ Eminus 1 := by
    rw [hEm₁]
    simp
  obtain ⟨hη₃eq, hε31, hβ₃eq⟩ := conj_column_analysis B₀ Pz (Lz 1) (Lz 3) (conjLabel basis)
    (conjLabel_conjLabel basis) hσB hPσz hLσz principal hσp η₁ η₃ β₁ β₃ ε₁ ε₃ hη₁B
    (by by_contra h; exact hη₁E ((hEmem η₁ hη₁B).mpr h)) hε₁
    (by have h := hL₁η; rw [hL1z η₁ hη₁B] at h; exact_mod_cast h)
    (by have h := hL₃η; rw [hL3z η₃ hη₃B] at h; exact_mod_cast h)
    (fun χ hχ hP hne => by
      have h := hz₃ χ hχ (fun hE => (hEmem χ hχ).mp hE hP) hne
      rw [hL3z χ hχ] at h
      exact_mod_cast h)
    hβ₁B ((hEmem β₁ hβ₁B).mp hβ₁E)
    (by
      have h := (Finset.mem_filter.mp hβ₁m).2
      change L 1 β₁ = -(P β₁ : ℂ) at h
      rw [hL1z β₁ hβ₁B, hPc β₁] at h
      exact_mod_cast h) hβ₁p
    (fun χ hχ hP hL => by
      have hχm : χ ∈ Eminus 3 := Finset.mem_filter.mpr ⟨(hEmem χ hχ).mpr hP, by
        rw [hL3z χ hχ, hPc χ, hL]
        push_cast
        rfl⟩
      rw [hEm₃] at hχm
      simpa using hχm)
  have hTσ' : ∀ χ, imCoeff i (T (conjLabel basis χ)) = -imCoeff i (T χ) := fun χ => by
    change imCoeff i (X (conjLabel basis χ) a) = _
    rw [hXσ, imCoeff_conj]
  have hUσ' : ∀ χ, imCoeff i (Ua (conjLabel basis χ)) = -imCoeff i (Ua χ) := fun χ => by
    change imCoeff i (X (conjLabel basis χ) (a * z)) = _
    rw [hXσ, imCoeff_conj]
  have hD : ∀ χ, L 1 χ - L 3 χ =
      -(((imCoeff i (T χ) + 2 * imCoeff i (Ua χ)) / 3 : ℝ) : ℂ) := fun χ => by
    have h := fourier_one_sub_three hi (v χ) ((T χ + 2 * Ua χ) / 3) ((Ax χ + 2 * Bx χ) / 3)
      rfl rfl rfl
    rw [imCoeff_add_two_mul_div_three] at h
    exact h
  have hD1 : L 1 χ₁ - L 3 χ₁ = -2 := by
    rw [hD, hT1, hU1]
    norm_num
  have hD2 : L 1 (conjLabel basis χ₁) - L 3 (conjLabel basis χ₁) = 2 := by
    rw [hD, hTσ', hUσ', hT1, hU1]
    norm_num
  have hD0 : ∀ χ ∈ B₀, χ ≠ χ₁ → χ ≠ conjLabel basis χ₁ → L 1 χ = L 3 χ := by
    intro χ hχ h1 h1'
    rw [← sub_eq_zero, hD]
    by_cases h2 : χ = χ₂
    · rw [h2, hT2, hU2]
      norm_num
    by_cases h2' : χ = conjLabel basis χ₂
    · rw [h2', hTσ', hUσ', hT2, hU2]
      norm_num
    by_cases h3 : χ = χ₃
    · rw [h3, hT3, hU3]
      norm_num
    by_cases h3' : χ = conjLabel basis χ₃
    · rw [h3', hTσ', hUσ', hT3, hU3]
      norm_num
    obtain ⟨hT0, hU0⟩ := hrestTU χ hχ (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1, h1', h2, h2', h3, h3'⟩)
    rw [hT0, hU0]
    norm_num
  obtain ⟨halt1, halt2⟩ := fourier_pair_alternatives B₀ E (L 1) (L 3) χ₁ (conjLabel basis χ₁)
    hD1 hD2 hD0 hχ₁B (hσB χ₁ hχ₁B) hEB η₁ η₃ ε₁ ε₃ hη₁B hη₃B hη₁E hη₃E hε₁ hε31 hL₁η hL₃η hz₁
    hz₃
  refine ⟨hparity, hEcard, hJcard, hpE, hpJ, hinter, hodd, fun h0 => by rw [hodd]; omega,
    fun h2 => by rw [hodd]; omega, χ₁, conjLabel basis χ₁, χ₂, conjLabel basis χ₂, χ₃,
    conjLabel basis χ₃, hXσ χ₁, hXσ χ₂, hXσ χ₃, hnodup, hfilterU, hU1, hU2, hU3, hT1, hT2, hT3,
    hrestTU, fun j => if j = 1 then η₁ else η₃, fun j => if j = 1 then β₁ else β₃,
    fun j => if j = 1 then ε₁ else ε₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | h
    · have hη₁p : η₁ ≠ principal := fun h => hη₁E (h ▸ hpE)
      exact ⟨hη₁B, hη₁E, hε₁, hL₁η, hz₁, hu₁, hcp₁, hcm₁, hEm₁, hβ₁p, hdη₁, hdβ₁, hSp₁, hSm₁,
        fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | h'
          · exact hirr _ hη₁B hη₁p
          · rw [Finset.mem_singleton.mp h']
            exact hirr _ hβ₁B hβ₁p⟩
    · rw [Finset.mem_singleton.mp h]
      have hη₃p : η₃ ≠ principal := fun h => hη₃E (h ▸ hpE)
      exact ⟨hη₃B, hη₃E, hε₃, hL₃η, hz₃, hu₃, hcp₃, hcm₃, hEm₃, hβ₃p, hdη₃, hdβ₃, hSp₃, hSm₃,
        fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | h'
          · exact hirr _ hη₃B hη₃p
          · rw [Finset.mem_singleton.mp h']
            exact hirr _ (hEB hβ₃E) hβ₃p⟩
  · show ∀ g, X η₃ g = starRingEnd ℂ (X η₁ g)
    rw [hη₃eq]
    exact hXσ η₁
  · show ε₃ = ε₁
    exact hε31
  · show ∀ g, X β₃ g = starRingEnd ℂ (X β₁ g)
    rw [hβ₃eq]
    exact hXσ β₁
  · show η₁ ≠ η₃ →
      ({χ₁, conjLabel basis χ₁} : Finset basis.index) = {η₁, η₃} ∧ ∀ χ ∈ E, L 1 χ = L 3 χ
    exact halt1
  · show η₁ = η₃ → (∀ g, X η₁ g = starRingEnd ℂ (X η₁ g)) ∧ χ₁ ∈ E ∧ conjLabel basis χ₁ ∈ E
    intro heq
    have hfix : conjLabel basis η₁ = η₁ := (heq.trans hη₃eq).symm
    refine ⟨fun g => ?_, halt2 heq⟩
    have h := hXσ η₁ g
    rwa [hfix] at h

end CFSG.Wreathed.FourPointThreePairs

module

public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersValues
public import CFSG.CharacterTheory.Wreathed.FourPointBaseMultiplicity
public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersClassify

public noncomputable section

namespace CFSG.Wreathed.FourPointTwelveCharacters

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.FourPointOrderFour
  CFSG.Wreathed.FourPointGaussianColumns CFSG.Wreathed.FourPointCentralFourier
  CFSG.Wreathed.FourPointOrderEight CFSG.Wreathed.WreathCentralSquare
  CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.OrderThirtyTwo CFSG.Wreathed.ConditionalGeneralBase
  CFSG.Wreathed.ConditionalFourier

open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_twelve_column_data
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
          let L : ZMod 4 → basis.index → ℂ := fun j χ => f χ j.val 0
          let deg : basis.index → ℕ := fun χ => Module.finrank ℂ (basis.representation χ).vector
          ∃ D : ColumnData basis.index, D.Valid ∧ D.B = B₀ ∧ D.p₀ = principal ∧
            (∀ χ, D.cj χ = conjLabel basis χ) ∧ (∀ χ, D.d χ = deg χ) ∧
            (∀ χ ∈ B₀, (D.P χ : ℝ) = P χ ∧ (D.L₂ χ : ℂ) = L 2 χ) ∧
            B₀.filter (fun χ => Odd (deg χ)) =
              symmDiff (B₀.filter (fun χ => D.P χ ≠ 0)) (B₀.filter (fun χ => D.Q χ ≠ 0)) ∧
            ∀ χ ∈ B₀,
              T χ = ((-2 * D.L₂ χ + 2 * D.cs χ - D.c₂ χ - D.c₁ χ - D.c₃ χ : ℤ) : ℂ) +
                  ((2 * ((D.L₃ χ - D.L₁ χ) + (D.c₃ χ - D.c₁ χ)) : ℤ) : ℂ) * i ∧
                Ax χ = ((2 * (D.L₂ χ - D.L₁ χ - D.L₃ χ) - 2 * D.cs χ + 3 * D.c₂ χ - D.c₁ χ -
                  D.c₃ χ : ℤ) : ℂ) ∧
                2 * Bx χ = ((D.L₂ χ - D.L₁ χ - D.L₃ χ - 3 * D.c₂ χ + D.c₁ χ + D.c₃ χ +
                  2 * D.cs χ : ℤ) : ℂ) ∧
                2 * Ua χ = ((-D.L₂ χ - 2 * D.cs χ + D.c₂ χ + D.c₁ χ + D.c₃ χ : ℤ) : ℂ) +
                  ((2 * (D.c₁ χ - D.c₃ χ) + (D.L₃ χ - D.L₁ χ) : ℤ) : ℂ) * i := by
  intro H N π aN s w a x C ρ W u iF U₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  subst hn2
  obtain ⟨-, hΦex, hGc⟩ :=
    four_point_central_section_integral_fourier_columns hnonab 2 hn S e alpha
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGo⟩ :=
    four_point_order_eight_centralizer_and_norm_four_columns hnonab 2 hn S e alpha
  obtain ⟨-, -, hGg⟩ :=
    four_point_global_gaussian_columns_and_conjugate_pair_dichotomy hnonab 2 hn S e alpha
  obtain ⟨-, -, hGp⟩ :=
    FourPointThreePairs.four_point_fourier_support_three_pairs_and_adjacent_degrees hnonab 2 hn
      S e alpha
  obtain ⟨-, -, ⟨σ, υ, g, -, hA⟩, hGb⟩ :=
    FourPointBaseMultiplicity.four_point_base_multiplicity_integral_columns_and_gram hnonab 2 hn
      S e alpha
  refine ⟨rfl, hΦex, fun Φ hΦ => ⟨(hGc Φ hΦ).1, ?_⟩⟩
  intro z hzC hzodd hπz ideal _ _ basis principal hprincipal i hi B₀ X Ax Bx T Ua v f P L deg
  obtain ⟨⟨y, hy2, hyΦ⟩, -, hGg'⟩ := hGg Φ hΦ
  obtain ⟨hfint, -, hfdeg, hfprin, -, hinv, -, hconjf, hfnorm⟩ :=
    (hGc Φ hΦ).2 z hzC hzodd hπz ideal basis principal hprincipal i hi
  obtain ⟨hPQint, -, -, -, -, hdP, -, hP1, hQ1, -, -, hPunit, -, hQunit, -, -, -⟩ :=
    (hGo Φ hΦ).2 z hzC hzodd hπz ideal basis principal hprincipal i hi
  obtain ⟨hgint, -, -, -, -, hUn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hUim2, -, -,
      -, -, -, -, -⟩ := hGg' y hy2 hyΦ z hzC hzodd hπz ideal basis principal hprincipal i hi
  obtain ⟨hpar, hEc, -, -, -, -, hodd, -, -, χ₁, ψ₁, χ₂, ψ₂, χ₃, ψ₃, hc1, hc2, hc3, hsix, hfilt,
      hU1, hU2, hU3, hT1, hT2, hT3, hoff, η₀, β₀, ε₀, hηj, hη3, hε3, -, hdne, hdeq⟩ :=
    (hGp Φ hΦ).2 z hzC hzodd hπz ideal basis principal hprincipal i hi
  obtain ⟨⟨lam₀, hlam₀⟩, hGb'⟩ :=
    (hGb Φ hΦ).2 z hzC hzodd hπz ideal basis principal hprincipal i hi σ υ g hA
  obtain ⟨hnat, hLh, hcint, -, -, hcolp, hconjc, horth, hgram, -, hparb, hvalb⟩ :=
    hGb' lam₀ hlam₀
  let tm : ZMod 4 → ZMod 4 → basis.index → ℂ := fun r s' χ =>
    (Nat.card ↥(Subgroup.closure {s, wreathModelHom S e (Original.t (2 ^ 2))}) : ℂ)⁻¹ *
      ∑ y : ↥(Subgroup.closure {s, wreathModelHom S e (Original.t (2 ^ 2))}),
        X χ y * starRingEnd ℂ (lam₀ r s' y)
  let hh : ZMod 4 → basis.index → ℂ := fun j χ => f χ j.val 1
  let cc : ZMod 4 → ZMod 4 → basis.index → ℂ := fun r s' χ =>
    tm 0 0 χ - tm r s' χ + hh (-r - s') χ + hh r χ + hh s' χ
  let Q : basis.index → ℝ := fun χ => imCoeff i (X χ ρ)
  have hcint' : ∀ r s' : ZMod 4, ∀ χ ∈ B₀, ∃ k : ℤ, cc r s' χ = k := hcint
  have hvalb' : ∀ χ ∈ B₀,
      cc 1 1 χ - cc 3 3 χ = ((4 * imCoeff i (Ua χ) - imCoeff i (T χ)) / 6 : ℝ) ∧
      T χ = -2 * L 2 χ + 2 * cc 1 0 χ - cc 2 2 χ - cc 1 1 χ - cc 3 3 χ +
        2 * i * ((L 3 χ - L 1 χ) + (cc 3 3 χ - cc 1 1 χ)) ∧
      Ax χ = 2 * (L 2 χ - L 1 χ - L 3 χ) - 2 * cc 1 0 χ + 3 * cc 2 2 χ - cc 1 1 χ - cc 3 3 χ ∧
      Bx χ = (L 2 χ - L 1 χ - L 3 χ - 3 * cc 2 2 χ + cc 1 1 χ + cc 3 3 χ) / 2 + cc 1 0 χ ∧
      ((Ua χ).re : ℂ) = (-L 2 χ - 2 * cc 1 0 χ + cc 2 2 χ + cc 1 1 χ + cc 3 3 χ) / 2 := hvalb
  have hcolp' : cc 1 1 principal = 1 ∧ cc 2 2 principal = 1 ∧ cc 3 3 principal = 1 ∧
      cc 1 0 principal = 1 := ⟨hcolp 0, hcolp 1, hcolp 2, hcolp 3⟩
  have hconjc' : ∀ χ ∈ B₀, ∀ ψ : basis.index, (∀ g', X ψ g' = starRingEnd ℂ (X χ g')) →
      cc 1 1 ψ = cc 3 3 χ ∧ cc 3 3 ψ = cc 1 1 χ ∧ cc 2 2 ψ = cc 2 2 χ ∧
        cc 1 0 ψ = cc 1 0 χ := hconjc
  have hparb' : ∀ χ ∈ B₀, (∃ k : ℤ, cc 2 2 χ = L 1 χ + 2 * k) ∧
      (∃ k : ℤ, L 1 χ = P χ + 2 * k) ∧ ∃ k : ℤ, cc 1 1 χ + cc 3 3 χ = Q χ + 2 * k := hparb
  have hgram' : ∀ l l' : Fin 4, ∑ χ ∈ B₀, (![cc 1 1, cc 2 2, cc 3 3, cc 1 0] : Fin 4 → _) l χ *
      (![cc 1 1, cc 2 2, cc 3 3, cc 1 0] : Fin 4 → _) l' χ =
        ((!![8, 6, 6, 6; 6, 8, 6, 6; 6, 6, 8, 6; 6, 6, 6, 7] : Matrix (Fin 4) (Fin 4) ℤ) l l' :
          ℂ) := hgram
  have horth' : ∀ l : Fin 4,
      ∑ χ ∈ B₀, (![cc 1 1, cc 2 2, cc 3 3, cc 1 0] : Fin 4 → _) l χ * X χ 1 = 0 ∧
      (∀ j : ZMod 4, ∑ χ ∈ B₀, (![cc 1 1, cc 2 2, cc 3 3, cc 1 0] : Fin 4 → _) l χ * L j χ = 0) ∧
      ∑ χ ∈ B₀, (![cc 1 1, cc 2 2, cc 3 3, cc 1 0] : Fin 4 → _) l χ * (P χ : ℂ) = 0 ∧
      ∑ χ ∈ B₀, (![cc 1 1, cc 2 2, cc 3 3, cc 1 0] : Fin 4 → _) l χ * (Q χ : ℂ) = 0 := horth
  have hLh' : ∀ j : ZMod 4, ∀ χ ∈ B₀, (∃ k : ℤ, L j χ = k) ∧ ∃ k : ℤ, hh j χ = k := hLh
  have hPQint' : ∀ χ ∈ B₀, (∃ k : ℤ, P χ = k) ∧ ∃ k : ℤ, Q χ = k := hPQint
  have hgint' : ∀ χ ∈ B₀, (∃ k : ℤ, Ax χ = k) ∧ (∃ k : ℤ, Bx χ = k) ∧
      (∃ s k : ℤ, T χ = s + k * i) ∧ ∃ s k : ℤ, Ua χ = s + k * i := hgint
  let D : ColumnData basis.index :=
    { B := B₀
      cj := conjLabel basis
      p₀ := principal
      d := fun χ => (deg χ : ℤ)
      P := fun χ => ⌊P χ⌋
      Q := fun χ => ⌊Q χ⌋
      L₁ := fun χ => ⌊(L 1 χ).re⌋
      L₂ := fun χ => ⌊(L 2 χ).re⌋
      L₃ := fun χ => ⌊(L 3 χ).re⌋
      c₁ := fun χ => ⌊(cc 1 1 χ).re⌋
      c₂ := fun χ => ⌊(cc 2 2 χ).re⌋
      c₃ := fun χ => ⌊(cc 3 3 χ).re⌋
      cs := fun χ => ⌊(cc 1 0 χ).re⌋
      Tim := fun χ => ⌊imCoeff i (T χ)⌋
      Uim := fun χ => ⌊imCoeff i (Ua χ)⌋
      χ₁ := χ₁
      χ₂ := χ₂
      χ₃ := χ₃
      η₁ := η₀ 1
      β₁ := β₀ 1
      ε := ε₀ 1 }
  have cL : ∀ j : ZMod 4, ∀ χ ∈ B₀, ((⌊(L j χ).re⌋ : ℤ) : ℂ) = L j χ := fun j χ hχ =>
    cast_floor_re (hLh' j χ hχ).1
  have cc' : ∀ r s' : ZMod 4, ∀ χ ∈ B₀, ((⌊(cc r s' χ).re⌋ : ℤ) : ℂ) = cc r s' χ :=
    fun r s' χ hχ => cast_floor_re (hcint' r s' χ hχ)
  have cP : ∀ χ ∈ B₀, ((⌊P χ⌋ : ℤ) : ℂ) = (P χ : ℂ) := fun χ hχ =>
    cast_floor_complex (hPQint' χ hχ).1
  have cQ : ∀ χ ∈ B₀, ((⌊Q χ⌋ : ℤ) : ℂ) = (Q χ : ℂ) := fun χ hχ =>
    cast_floor_complex (hPQint' χ hχ).2
  have cPr : ∀ χ ∈ B₀, ((⌊P χ⌋ : ℤ) : ℝ) = P χ := fun χ hχ => cast_floor (hPQint' χ hχ).1
  have cQr : ∀ χ ∈ B₀, ((⌊Q χ⌋ : ℤ) : ℝ) = Q χ := fun χ hχ => cast_floor (hPQint' χ hχ).2
  have hdeg : ∀ χ, X χ 1 = (deg χ : ℂ) := fun χ => by
    show (basis.representation χ).character 1 = _
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  have cd : ∀ χ, ((deg χ : ℤ) : ℂ) = X χ 1 := fun χ => by
    rw [hdeg]
    simp
  have hTimZ : ∀ χ ∈ B₀, ∃ k : ℤ, imCoeff i (T χ) = k := by
    intro χ hχ
    obtain ⟨s₀, k, hk⟩ := (hgint' χ hχ).2.2.1
    refine ⟨k, ?_⟩
    rw [hk, show ((s₀ : ℂ) + (k : ℂ) * i) = (((s₀ : ℝ) : ℂ) + ((k : ℝ) : ℂ) * i) by push_cast; ring,
      imCoeff_add_mul hi]
  have hUimZ : ∀ χ ∈ B₀, ∃ k : ℤ, imCoeff i (Ua χ) = k := by
    intro χ hχ
    obtain ⟨s₀, k, hk⟩ := (hgint' χ hχ).2.2.2
    refine ⟨k, ?_⟩
    rw [hk, show ((s₀ : ℂ) + (k : ℂ) * i) = (((s₀ : ℝ) : ℂ) + ((k : ℝ) : ℂ) * i) by push_cast; ring,
      imCoeff_add_mul hi]
  have cTim : ∀ χ ∈ B₀, ((⌊imCoeff i (T χ)⌋ : ℤ) : ℝ) = imCoeff i (T χ) := fun χ hχ =>
    cast_floor (hTimZ χ hχ)
  have cUim : ∀ χ ∈ B₀, ((⌊imCoeff i (Ua χ)⌋ : ℤ) : ℝ) = imCoeff i (Ua χ) := fun χ hχ =>
    cast_floor (hUimZ χ hχ)
  have hcj : ∀ χ g, X (conjLabel basis χ) g = starRingEnd ℂ (X χ g) := conjLabel_spec basis
  have hψ₁ : conjLabel basis χ₁ = ψ₁ := conjLabel_eq_of_spec basis _ _ hc1
  have hψ₂ : conjLabel basis χ₂ = ψ₂ := conjLabel_eq_of_spec basis _ _ hc2
  have hψ₃ : conjLabel basis χ₃ = ψ₃ := conjLabel_eq_of_spec basis _ _ hc3
  have hη₃ : conjLabel basis (η₀ 1) = η₀ 3 := conjLabel_eq_of_spec basis _ _ hη3
  have hpB : principal ∈ B₀ := coefficientBlock_self_mem basis _ principal
  have hcjB : ∀ χ ∈ B₀, conjLabel basis χ ∈ B₀ := fun χ hχ =>
    conjLabel_mem_coefficientBlock basis _ principal hprincipal χ hχ
  have ha : a ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype := by
    refine ⟨e.symm (Original.a (2 ^ 2)), Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro g'
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_center_iff.mp (original_a_mem_center (2 ^ 2)) (e g'))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT0 : ∀ χ ∈ B₀, T χ ≠ 0 := fun χ hχ =>
    (principal_block_character_unit_ratio_of_mem_center_sylow basis ideal 2 principal
      hprincipal S a ha χ hχ).2.1
  have hPfl : ∀ χ ∈ B₀, (⌊P χ⌋ = 0 ↔ P χ = 0) := fun χ hχ => by
    constructor
    · intro h0
      rw [← cPr χ hχ, h0, Int.cast_zero]
    · intro h0
      rw [h0, Int.floor_zero]
  have hQfl : ∀ χ ∈ B₀, (⌊Q χ⌋ = 0 ↔ Q χ = 0) := fun χ hχ => by
    constructor
    · intro h0
      rw [← cQr χ hχ, h0, Int.cast_zero]
    · intro h0
      rw [h0, Int.floor_zero]
  have hX1 : X principal 1 = 1 := by
    show (basis.representation principal).character 1 = 1
    rw [hprincipal, Pi.one_apply]
  have hval : ∀ χ ∈ B₀, ∀ (l₁ l₂ l₃ a₁ a₂ a₃ s₀ : ℤ), L 1 χ = l₁ → L 2 χ = l₂ → L 3 χ = l₃ →
      cc 1 1 χ = a₁ → cc 2 2 χ = a₂ → cc 3 3 χ = a₃ → cc 1 0 χ = s₀ →
      T χ = ((-2 * l₂ + 2 * s₀ - a₂ - a₁ - a₃ : ℤ) : ℂ) +
          ((2 * ((l₃ - l₁) + (a₃ - a₁)) : ℤ) : ℂ) * i ∧
        Ax χ = ((2 * (l₂ - l₁ - l₃) - 2 * s₀ + 3 * a₂ - a₁ - a₃ : ℤ) : ℂ) ∧
        2 * Bx χ = ((l₂ - l₁ - l₃ - 3 * a₂ + a₁ + a₃ + 2 * s₀ : ℤ) : ℂ) ∧
        2 * Ua χ = ((-l₂ - 2 * s₀ + a₂ + a₁ + a₃ : ℤ) : ℂ) +
          ((2 * (a₁ - a₃) + (l₃ - l₁) : ℤ) : ℂ) * i := by
    intro χ hχ l₁ l₂ l₃ a₁ a₂ a₃ s₀ e1 e2 e3 f1 f2 f3 f4
    obtain ⟨v1, v2, v3, v4, v5⟩ := hvalb' χ hχ
    rw [f1, f3] at v1
    simp only [e1, e2, e3, f1, f2, f3, f4] at v2 v3 v4 v5
    exact values_of_row hi v1 v2 v3 v4 v5
  have hPunit' : ∀ χ ∈ B₀, P χ ≠ 0 → P χ = 1 ∨ P χ = -1 := hPunit
  have hQunit' : ∀ χ ∈ B₀, Q χ ≠ 0 → Q χ = 1 ∨ Q χ = -1 := hQunit
  have hP1' : P principal = 1 := hP1
  have hQ1' : Q principal = 0 := hQ1
  have hdP' : ∑ χ ∈ B₀, X χ 1 * (P χ : ℂ) = 0 := hdP
  have hfprin' : ∀ j ∈ Finset.Icc 1 3, f principal j 0 = -1 ∧ f principal j 1 = 0 := hfprin
  have hfdeg' : ∀ (j : ℕ) ℓ, ∑ χ ∈ B₀, X χ 1 * f χ j ℓ = 0 := hfdeg
  have hconjf' : ∀ χ ∈ B₀, ∀ χ' : basis.index, (∀ g, X χ' g = starRingEnd ℂ (X χ g)) →
      ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, f χ' j ℓ = f χ (4 - j) ℓ := hconjf
  have hfnorm' : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3,
      ∑ χ ∈ B₀, f χ j 0 * f χ k 0 = if j = k then 8 else 4 := hfnorm
  have hEc' : (B₀.filter (fun χ => P χ ≠ 0)).card = 4 := hEc
  obtain ⟨hηB, hηE, hε, hLη, hLoff, hLE, -, -, hEm, hβne, -⟩ := hηj 1 (by simp)
  have hβm := hEm ▸ (by simp : β₀ 1 ∈ ({principal, β₀ 1} : Finset basis.index))
  simp only [Finset.mem_filter] at hβm
  obtain ⟨⟨hβB, hβP⟩, hβL⟩ := hβm
  have hβP' : P (β₀ 1) ≠ 0 := hβP
  have hβL' : f (β₀ 1) 1 0 = -(P (β₀ 1) : ℂ) := hβL
  have hfl : ∀ t : ℂ, ∀ k : ℤ, t = k → ⌊t.re⌋ = k := fun t k h => by
    rw [h, floor_re_intCast]
  have hfl' : ∀ t : ℝ, ∀ k : ℤ, t = k → ⌊t⌋ = k := fun t k h => by
    rw [h, Int.floor_intCast]
  have hV : D.Valid :=
    { p_mem := hpB
      cj_mem := hcjB
      cj_cj := conjLabel_conjLabel basis
      cj_p := conjLabel_eq_of_spec basis _ _ fun g => by
        show (basis.representation principal).character g =
          starRingEnd ℂ ((basis.representation principal).character g)
        rw [hprincipal, Pi.one_apply, map_one]
      d_pos := fun χ _ => by
        have h0 := irreducible_character_degree_ne_zero (basis.representation χ)
          (basis.irreducible χ)
        have hd0 : deg χ ≠ 0 := by
          intro h0'
          apply h0
          change X χ 1 = 0
          rw [hdeg, h0', Nat.cast_zero]
        change (1 : ℤ) ≤ (deg χ : ℤ)
        omega
      d_p := by
        have h1 := hdeg principal
        rw [hX1] at h1
        change (deg principal : ℤ) = 1
        exact_mod_cast h1.symm
      d_cj := fun χ _ => by
        have h1 := hdeg (conjLabel basis χ)
        rw [hcj, hdeg χ, Complex.conj_natCast] at h1
        change (deg (conjLabel basis χ) : ℤ) = deg χ
        exact_mod_cast h1.symm
      P_p := hfl' (P principal) 1 (by rw [hP1']; simp)
      Q_p := hfl' (Q principal) 0 (by rw [hQ1']; simp)
      L₁_p := hfl (f principal 1 0) (-1) (by rw [(hfprin' 1 (by decide)).1]; simp)
      L₂_p := hfl (f principal 2 0) (-1) (by rw [(hfprin' 2 (by decide)).1]; simp)
      L₃_p := hfl (f principal 3 0) (-1) (by rw [(hfprin' 3 (by decide)).1]; simp)
      c₁_p := hfl (cc 1 1 principal) 1 (by rw [hcolp'.1]; simp)
      c₂_p := hfl (cc 2 2 principal) 1 (by rw [hcolp'.2.1]; simp)
      c₃_p := hfl (cc 3 3 principal) 1 (by rw [hcolp'.2.2.1]; simp)
      cs_p := hfl (cc 1 0 principal) 1 (by rw [hcolp'.2.2.2]; simp)
      P_cj := fun χ _ => by
        change ⌊(X (conjLabel basis χ) ρ).re⌋ = ⌊(X χ ρ).re⌋
        rw [hcj, Complex.conj_re]
      Q_cj := fun χ hχ => by
        change ⌊imCoeff i (X (conjLabel basis χ) ρ)⌋ = -⌊imCoeff i (X χ ρ)⌋
        obtain ⟨k, hk⟩ := (hPQint' χ hχ).2
        change imCoeff i (X χ ρ) = k at hk
        rw [hcj, imCoeff_conj, hk, ← Int.cast_neg]
        simp only [Int.floor_intCast]
      L₁_cj := fun χ hχ => by
        change ⌊(L 1 (conjLabel basis χ)).re⌋ = ⌊(L 3 χ).re⌋
        rw [show L 1 (conjLabel basis χ) = L 3 χ from
          hconjf' χ hχ _ (hcj χ) 1 (by decide) 0]
      L₂_cj := fun χ hχ => by
        change ⌊(L 2 (conjLabel basis χ)).re⌋ = ⌊(L 2 χ).re⌋
        rw [show L 2 (conjLabel basis χ) = L 2 χ from
          hconjf' χ hχ _ (hcj χ) 2 (by decide) 0]
      L₃_cj := fun χ hχ => by
        change ⌊(L 3 (conjLabel basis χ)).re⌋ = ⌊(L 1 χ).re⌋
        rw [show L 3 (conjLabel basis χ) = L 1 χ from
          hconjf' χ hχ _ (hcj χ) 3 (by decide) 0]
      c₁_cj := fun χ hχ => by
        change ⌊(cc 1 1 (conjLabel basis χ)).re⌋ = ⌊(cc 3 3 χ).re⌋
        rw [(hconjc' χ hχ _ (hcj χ)).1]
      c₂_cj := fun χ hχ => by
        change ⌊(cc 2 2 (conjLabel basis χ)).re⌋ = ⌊(cc 2 2 χ).re⌋
        rw [(hconjc' χ hχ _ (hcj χ)).2.2.1]
      c₃_cj := fun χ hχ => by
        change ⌊(cc 3 3 (conjLabel basis χ)).re⌋ = ⌊(cc 1 1 χ).re⌋
        rw [(hconjc' χ hχ _ (hcj χ)).2.1]
      cs_cj := fun χ hχ => by
        change ⌊(cc 1 0 (conjLabel basis χ)).re⌋ = ⌊(cc 1 0 χ).re⌋
        rw [(hconjc' χ hχ _ (hcj χ)).2.2.2]
      Tim_cj := fun χ hχ => by
        change ⌊imCoeff i (X (conjLabel basis χ) a)⌋ = -⌊imCoeff i (X χ a)⌋
        obtain ⟨k, hk⟩ := hTimZ χ hχ
        change imCoeff i (X χ a) = k at hk
        rw [hcj, imCoeff_conj, hk, ← Int.cast_neg]
        simp only [Int.floor_intCast]
      Uim_cj := fun χ hχ => by
        change ⌊imCoeff i (X (conjLabel basis χ) (a * z))⌋ = -⌊imCoeff i (X χ (a * z))⌋
        obtain ⟨k, hk⟩ := hUimZ χ hχ
        change imCoeff i (X χ (a * z)) = k at hk
        rw [hcj, imCoeff_conj, hk, ← Int.cast_neg]
        simp only [Int.floor_intCast]
      P_val := fun χ hχ => by
        change ⌊P χ⌋ = 0 ∨ ⌊P χ⌋ = 1 ∨ ⌊P χ⌋ = -1
        by_cases hP : P χ = 0
        · left
          rw [hP, Int.floor_zero]
        · rcases hPunit' χ hχ hP with e1 | e1
          · right; left
            rw [e1, Int.floor_one]
          · right; right
            rw [e1, show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
      Q_val := fun χ hχ => by
        change ⌊Q χ⌋ = 0 ∨ ⌊Q χ⌋ = 1 ∨ ⌊Q χ⌋ = -1
        by_cases hQ : Q χ = 0
        · left
          rw [hQ, Int.floor_zero]
        · rcases hQunit' χ hχ hQ with e1 | e1
          · right; left
            rw [e1, Int.floor_one]
          · right; right
            rw [e1, show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
      E_card := by
        change (B₀.filter (fun χ => ⌊P χ⌋ ≠ 0)).card = 4
        rw [← hEc']
        congr 1
        exact Finset.filter_congr fun χ hχ => not_congr (hPfl χ hχ)
      c₁c₁ := sum_mul_intCast_eq B₀ (cc' 1 1) (cc' 1 1) (c := 8) (hgram' 0 0)
      c₂c₂ := sum_mul_intCast_eq B₀ (cc' 2 2) (cc' 2 2) (c := 8) (hgram' 1 1)
      cscs := sum_mul_intCast_eq B₀ (cc' 1 0) (cc' 1 0) (c := 7) (hgram' 3 3)
      c₁c₂ := sum_mul_intCast_eq B₀ (cc' 1 1) (cc' 2 2) (c := 6) (hgram' 0 1)
      c₁cs := sum_mul_intCast_eq B₀ (cc' 1 1) (cc' 1 0) (c := 6) (hgram' 0 3)
      c₂cs := sum_mul_intCast_eq B₀ (cc' 2 2) (cc' 1 0) (c := 6) (hgram' 1 3)
      L₁L₃ := sum_mul_intCast_eq B₀ (cL 1) (cL 3) (c := 4) (by
        have h := hfnorm' 1 (by decide) 3 (by decide)
        norm_num at h
        exact_mod_cast h)
      L₂L₂ := sum_mul_intCast_eq B₀ (cL 2) (cL 2) (c := 8) (by
        have h := hfnorm' 2 (by decide) 2 (by decide)
        norm_num at h
        exact_mod_cast h)
      L₁L₂ := sum_mul_intCast_eq B₀ (cL 1) (cL 2) (c := 4) (by
        have h := hfnorm' 1 (by decide) 2 (by decide)
        norm_num at h
        exact_mod_cast h)
      L₂L₃ := sum_mul_intCast_eq B₀ (cL 2) (cL 3) (c := 4) (by
        have h := hfnorm' 2 (by decide) 3 (by decide)
        norm_num at h
        exact_mod_cast h)
      c₂L₁ := sum_mul_intCast_eq B₀ (cc' 2 2) (cL 1) (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 1).2.1 1)
      c₂L₂ := sum_mul_intCast_eq B₀ (cc' 2 2) (cL 2) (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 1).2.1 2)
      c₂L₃ := sum_mul_intCast_eq B₀ (cc' 2 2) (cL 3) (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 1).2.1 3)
      c₁L₁ := sum_mul_intCast_eq B₀ (cc' 1 1) (cL 1) (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 0).2.1 1)
      csL₁ := sum_mul_intCast_eq B₀ (cc' 1 0) (cL 1) (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 3).2.1 1)
      csL₂ := sum_mul_intCast_eq B₀ (cc' 1 0) (cL 2) (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 3).2.1 2)
      c₁P := sum_mul_intCast_eq B₀ (cc' 1 1) cP (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 0).2.2.1)
      c₂P := sum_mul_intCast_eq B₀ (cc' 2 2) cP (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 1).2.2.1)
      csP := sum_mul_intCast_eq B₀ (cc' 1 0) cP (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 3).2.2.1)
      c₁d := sum_mul_intCast_eq B₀ (cc' 1 1) (fun χ _ => cd χ) (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 0).1)
      c₂d := sum_mul_intCast_eq B₀ (cc' 2 2) (fun χ _ => cd χ) (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 1).1)
      csd := sum_mul_intCast_eq B₀ (cc' 1 0) (fun χ _ => cd χ) (c := 0) (by
        rw [Int.cast_zero]
        exact (horth' 3).1)
      L₁d := sum_mul_intCast_eq B₀ (cL 1) (fun χ _ => cd χ) (c := 0) (by
        rw [Int.cast_zero, ← hfdeg' 1 0]
        exact Finset.sum_congr rfl fun χ _ => mul_comm _ _)
      L₂d := sum_mul_intCast_eq B₀ (cL 2) (fun χ _ => cd χ) (c := 0) (by
        rw [Int.cast_zero, ← hfdeg' 2 0]
        exact Finset.sum_congr rfl fun χ _ => mul_comm _ _)
      L₃d := sum_mul_intCast_eq B₀ (cL 3) (fun χ _ => cd χ) (c := 0) (by
        rw [Int.cast_zero, ← hfdeg' 3 0]
        exact Finset.sum_congr rfl fun χ _ => mul_comm _ _)
      Pd := sum_mul_intCast_eq B₀ cP (fun χ _ => cd χ) (c := 0) (by
        rw [Int.cast_zero, ← hdP']
        exact Finset.sum_congr rfl fun χ _ => mul_comm _ _)
      ReU := by
        change ∑ χ ∈ B₀, (-⌊(L 2 χ).re⌋ - 2 * ⌊(cc 1 0 χ).re⌋ + ⌊(cc 2 2 χ).re⌋ +
          ⌊(cc 1 1 χ).re⌋ + ⌊(cc 3 3 χ).re⌋) ^ 2 = 24
        have hre : ∀ χ ∈ B₀, ((-⌊(L 2 χ).re⌋ - 2 * ⌊(cc 1 0 χ).re⌋ + ⌊(cc 2 2 χ).re⌋ +
            ⌊(cc 1 1 χ).re⌋ + ⌊(cc 3 3 χ).re⌋ : ℤ) : ℝ) = 2 * (Ua χ).re := by
          intro χ hχ
          have h5 := (hvalb' χ hχ).2.2.2.2
          have e : (((-⌊(L 2 χ).re⌋ - 2 * ⌊(cc 1 0 χ).re⌋ + ⌊(cc 2 2 χ).re⌋ +
              ⌊(cc 1 1 χ).re⌋ + ⌊(cc 3 3 χ).re⌋ : ℤ) : ℝ) : ℂ) = ((2 * (Ua χ).re : ℝ) : ℂ) := by
            push_cast
            rw [cL 2 χ hχ, cc' 1 0 χ hχ, cc' 2 2 χ hχ, cc' 1 1 χ hχ, cc' 3 3 χ hχ, h5]
            ring
          exact_mod_cast e
        have hUn' : ∑ χ ∈ B₀, Complex.normSq (Ua χ) = 12 := hUn
        have hUim2' : ∑ χ ∈ B₀, imCoeff i (Ua χ) ^ 2 = 6 := hUim2
        have hre2 : ∑ χ ∈ B₀, (Ua χ).re ^ 2 = 6 := by
          rw [Finset.sum_congr rfl fun χ _ => normSq_eq_re_sq_add_imCoeff_sq hi (Ua χ),
            Finset.sum_add_distrib, hUim2'] at hUn'
          linarith
        have e : ((∑ χ ∈ B₀, (-⌊(L 2 χ).re⌋ - 2 * ⌊(cc 1 0 χ).re⌋ + ⌊(cc 2 2 χ).re⌋ +
            ⌊(cc 1 1 χ).re⌋ + ⌊(cc 3 3 χ).re⌋) ^ 2 : ℤ) : ℝ) = 24 := by
          push_cast
          rw [Finset.sum_congr rfl fun χ hχ => by
            rw [show ((-(⌊(L 2 χ).re⌋ : ℝ) - 2 * ⌊(cc 1 0 χ).re⌋ + ⌊(cc 2 2 χ).re⌋ +
              ⌊(cc 1 1 χ).re⌋ + ⌊(cc 3 3 χ).re⌋) = 2 * (Ua χ).re) by exact_mod_cast hre χ hχ]]
          rw [Finset.sum_congr rfl fun χ _ => by rw [mul_pow], ← Finset.mul_sum, hre2]
          norm_num
        exact_mod_cast e
      c₂_par := fun χ hχ => by
        obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩, -⟩ := hparb' χ hχ
        refine ⟨k₁ + k₂, ?_⟩
        change ⌊(cc 2 2 χ).re⌋ = ⌊P χ⌋ + 2 * (k₁ + k₂)
        have e : ((⌊(cc 2 2 χ).re⌋ : ℤ) : ℂ) = ((⌊P χ⌋ + 2 * (k₁ + k₂) : ℤ) : ℂ) := by
          rw [cc' 2 2 χ hχ]
          push_cast
          rw [cP χ hχ, hk₁, hk₂]
          ring
        exact_mod_cast e
      c₁₃_par := fun χ hχ => by
        obtain ⟨-, -, ⟨k, hk⟩⟩ := hparb' χ hχ
        refine ⟨k, ?_⟩
        change ⌊(cc 1 1 χ).re⌋ + ⌊(cc 3 3 χ).re⌋ = ⌊Q χ⌋ + 2 * k
        have e : ((⌊(cc 1 1 χ).re⌋ + ⌊(cc 3 3 χ).re⌋ : ℤ) : ℂ) = ((⌊Q χ⌋ + 2 * k : ℤ) : ℂ) := by
          push_cast
          rw [cc' 1 1 χ hχ, cc' 3 3 χ hχ, cQ χ hχ, hk]
        exact_mod_cast e
      L₂_par := fun χ hχ => by
        obtain ⟨-, -, -, -, ⟨k, hk⟩, -⟩ := hpar χ hχ
        have hk' : L 2 χ = (P χ : ℂ) + (Q χ : ℂ) + 2 * k := hk
        refine ⟨k, ?_⟩
        change ⌊(L 2 χ).re⌋ = ⌊P χ⌋ + ⌊Q χ⌋ + 2 * k
        have e : ((⌊(L 2 χ).re⌋ : ℤ) : ℂ) = ((⌊P χ⌋ + ⌊Q χ⌋ + 2 * k : ℤ) : ℂ) := by
          rw [cL 2 χ hχ]
          push_cast
          rw [cP χ hχ, cQ χ hχ, hk']
        exact_mod_cast e
      c₁₃ := fun χ hχ => by
        change 6 * (⌊(cc 1 1 χ).re⌋ - ⌊(cc 3 3 χ).re⌋) =
          4 * ⌊imCoeff i (Ua χ)⌋ - ⌊imCoeff i (T χ)⌋
        have h1 := (hvalb' χ hχ).1
        rw [← cc' 1 1 χ hχ, ← cc' 3 3 χ hχ, ← cUim χ hχ, ← cTim χ hχ] at h1
        have h2 : ((⌊(cc 1 1 χ).re⌋ : ℝ) - ⌊(cc 3 3 χ).re⌋) =
            (4 * ⌊imCoeff i (Ua χ)⌋ - ⌊imCoeff i (T χ)⌋) / 6 := by exact_mod_cast h1
        have h3 : ((6 * (⌊(cc 1 1 χ).re⌋ - ⌊(cc 3 3 χ).re⌋) : ℤ) : ℝ) =
            ((4 * ⌊imCoeff i (Ua χ)⌋ - ⌊imCoeff i (T χ)⌋ : ℤ) : ℝ) := by
          push_cast
          linarith
        exact_mod_cast h3
      T_ne := fun χ hχ => by
        change -2 * ⌊(L 2 χ).re⌋ + 2 * ⌊(cc 1 0 χ).re⌋ - ⌊(cc 2 2 χ).re⌋ - ⌊(cc 1 1 χ).re⌋ -
          ⌊(cc 3 3 χ).re⌋ ≠ 0 ∨ ⌊(L 3 χ).re⌋ - ⌊(L 1 χ).re⌋ + ⌊(cc 3 3 χ).re⌋ -
          ⌊(cc 1 1 χ).re⌋ ≠ 0
        by_contra hc
        simp only [not_or, not_not] at hc
        obtain ⟨h1, h2⟩ := hc
        apply hT0 χ hχ
        have e1 : -2 * L 2 χ + 2 * cc 1 0 χ - cc 2 2 χ - cc 1 1 χ - cc 3 3 χ = 0 := by
          rw [← cL 2 χ hχ, ← cc' 1 0 χ hχ, ← cc' 2 2 χ hχ, ← cc' 1 1 χ hχ, ← cc' 3 3 χ hχ]
          exact_mod_cast h1
        have e2 : L 3 χ - L 1 χ + (cc 3 3 χ - cc 1 1 χ) = 0 := by
          rw [← cL 3 χ hχ, ← cL 1 χ hχ, ← cc' 3 3 χ hχ, ← cc' 1 1 χ hχ]
          have h2' : ((⌊(L 3 χ).re⌋ - ⌊(L 1 χ).re⌋ + ⌊(cc 3 3 χ).re⌋ - ⌊(cc 1 1 χ).re⌋ : ℤ) :
              ℂ) = 0 := by exact_mod_cast h2
          push_cast at h2'
          linear_combination h2'
        rw [(hvalb' χ hχ).2.1]
        linear_combination e1 + 2 * i * e2
      six_mem := by
        have hsixB : ∀ χ ∈ ({χ₁, ψ₁, χ₂, ψ₂, χ₃, ψ₃} : Finset basis.index), χ ∈ B₀ :=
          fun χ hχ => (Finset.mem_filter.mp (hfilt ▸ hχ)).1
        exact ⟨hsixB χ₁ (by simp), hsixB χ₂ (by simp), hsixB χ₃ (by simp)⟩
      six_nodup := by
        change [χ₁, conjLabel basis χ₁, χ₂, conjLabel basis χ₂, χ₃, conjLabel basis χ₃].Nodup
        rw [hψ₁, hψ₂, hψ₃]
        exact hsix
      Uim₁ := hfl' _ 1 (by exact_mod_cast hU1)
      Uim₂ := hfl' _ 1 (by exact_mod_cast hU2)
      Uim₃ := hfl' _ 1 (by exact_mod_cast hU3)
      Tim₁ := hfl' _ 4 (by exact_mod_cast hT1)
      Tim₂ := hfl' _ (-2) (by exact_mod_cast hT2)
      Tim₃ := hfl' _ (-2) (by exact_mod_cast hT3)
      off_six := fun χ hχ h1 h1' h2 h2' h3 h3' => by
        have hn : χ ∉ ({χ₁, ψ₁, χ₂, ψ₂, χ₃, ψ₃} : Finset basis.index) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h1, hψ₁ ▸ h1', h2, hψ₂ ▸ h2', h3, hψ₃ ▸ h3'⟩
        obtain ⟨hT, hU⟩ := hoff χ hχ hn
        exact ⟨hfl' _ 0 (by rw [hT]; simp), hfl' _ 0 (by rw [hU]; simp)⟩
      η_mem := hηB
      η_P := by
        have h0 : P (η₀ 1) = 0 := by
          by_contra hP
          exact hηE (Finset.mem_filter.mpr ⟨hηB, hP⟩)
        exact hfl' (P (η₀ 1)) 0 (by rw [h0]; simp)
      ε_val := hε
      L₁_η := hfl (f (η₀ 1) 1 0) (2 * ε₀ 1)
        (by rw [show f (η₀ 1) 1 0 = 2 * (ε₀ 1 : ℂ) from hLη]; simp)
      L₁_off := fun χ hχ hP hne => by
        have hPχ : P χ = 0 := (hPfl χ hχ).mp hP
        have hnE : χ ∉ B₀.filter (fun χ => P χ ≠ 0) := fun hm =>
          (Finset.mem_filter.mp hm).2 hPχ
        exact hfl (f χ 1 0) 0 (by rw [show f χ 1 0 = 0 from hLoff χ hχ hnE hne]; simp)
      L₁_E := fun χ hχ hP => by
        have hPχ : P χ ≠ 0 := fun h0 => hP ((hPfl χ hχ).mpr h0)
        rcases hLE χ (Finset.mem_filter.mpr ⟨hχ, hPχ⟩) with e1 | e1
        · left
          exact hfl (f χ 1 0) 1 (by rw [show f χ 1 0 = 1 from e1]; simp)
        · right
          exact hfl (f χ 1 0) (-1) (by rw [show f χ 1 0 = -1 from e1]; simp)
      β_mem := hβB
      β_P := fun h0 => hβP' ((hPfl _ hβB).mp h0)
      β_L := by
        change ⌊(L 1 (β₀ 1)).re⌋ = -⌊P (β₀ 1)⌋
        have e : ((⌊(L 1 (β₀ 1)).re⌋ : ℤ) : ℂ) = ((-⌊P (β₀ 1)⌋ : ℤ) : ℂ) := by
          rw [cL 1 _ hβB]
          push_cast
          rw [cP _ hβB]
          exact hβL'
        exact_mod_cast e
      β_ne := hβne
      Eminus := fun χ hχ hP hL => by
        have hPχ : P χ ≠ 0 := fun h0 => hP ((hPfl χ hχ).mpr h0)
        have hLχ : f χ 1 0 = -(P χ : ℂ) := by
          have e : ((⌊(L 1 χ).re⌋ : ℤ) : ℂ) = ((-⌊P χ⌋ : ℤ) : ℂ) := by exact_mod_cast hL
          rw [cL 1 χ hχ] at e
          push_cast at e
          rw [cP χ hχ] at e
          exact e
        have hm := (Finset.ext_iff.mp hEm χ).mp
          (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hχ, hPχ⟩, hLχ⟩)
        simpa using hm
      dich_ne := fun hne => by
        have hne' : η₀ 1 ≠ η₀ 3 := by
          rw [← hη₃]
          exact hne
        obtain ⟨hpair, hL13⟩ := hdne hne'
        refine ⟨?_, fun χ hχ hP => ?_⟩
        · have h1 : χ₁ ∈ ({η₀ 1, η₀ 3} : Finset basis.index) := hpair ▸ (by simp)
          simp only [Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with e1 | e1
          · left
            exact ⟨e1, by change conjLabel basis χ₁ = conjLabel basis (η₀ 1); rw [e1]⟩
          · right
            refine ⟨by change χ₁ = conjLabel basis (η₀ 1); rw [e1, hη₃], ?_⟩
            change conjLabel basis χ₁ = η₀ 1
            rw [e1, ← hη₃, conjLabel_conjLabel]
        · have hPχ : P χ ≠ 0 := fun h0 => hP ((hPfl χ hχ).mpr h0)
          have e := hL13 χ (Finset.mem_filter.mpr ⟨hχ, hPχ⟩)
          change ⌊(f χ 1 0).re⌋ = ⌊(f χ 3 0).re⌋
          rw [show f χ 1 0 = f χ 3 0 from e]
      dich_eq := fun heq => by
        have heq' : η₀ 1 = η₀ 3 := by
          rw [← hη₃]
          exact heq
        obtain ⟨-, h1, h2⟩ := hdeq heq'
        have hB1 := (Finset.mem_filter.mp h1).1
        have hB2 := (Finset.mem_filter.mp h2).1
        refine ⟨fun h0 => (Finset.mem_filter.mp h1).2 ((hPfl _ hB1).mp h0), fun h0 => ?_⟩
        change ⌊P (conjLabel basis χ₁)⌋ = 0 at h0
        rw [hψ₁] at h0
        exact (Finset.mem_filter.mp h2).2 ((hPfl _ hB2).mp h0) }
  refine ⟨D, hV, rfl, rfl, fun χ => rfl, fun χ => rfl, fun χ hχ => ⟨cPr χ hχ, cL 2 χ hχ⟩, ?_,
    fun χ hχ => hval χ hχ _ _ _ _ _ _ _ (cL 1 χ hχ).symm (cL 2 χ hχ).symm (cL 3 χ hχ).symm
      (cc' 1 1 χ hχ).symm (cc' 2 2 χ hχ).symm (cc' 3 3 χ hχ).symm (cc' 1 0 χ hχ).symm⟩
  rw [hodd]
  congr 1
  · exact Finset.filter_congr fun χ hχ => not_congr (hPfl χ hχ).symm
  · exact Finset.filter_congr fun χ hχ => not_congr (hQfl χ hχ).symm

theorem four_point_twelve_principal_characters_and_signed_degree_table
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
          let L : ZMod 4 → basis.index → ℂ := fun j χ => f χ j.val 0
          let deg : basis.index → ℕ := fun χ => Module.finrank ℂ (basis.representation χ).vector
          ∃ (β κ lam γ ψ η η' ξκ ξκ' ξl ξl' : basis.index) (pβ pκ pl δ ε ζ : ℤ),
            (pβ = 1 ∨ pβ = -1) ∧ (pκ = 1 ∨ pκ = -1) ∧ (pl = 1 ∨ pl = -1) ∧
            (δ = 1 ∨ δ = -1) ∧ (ε = 1 ∨ ε = -1) ∧ (ζ = 1 ∨ ζ = -1) ∧
            (∀ g, starRingEnd ℂ (X principal g) = X principal g) ∧
            (∀ g, starRingEnd ℂ (X β g) = X β g) ∧ (∀ g, starRingEnd ℂ (X κ g) = X κ g) ∧
            (∀ g, starRingEnd ℂ (X lam g) = X lam g) ∧ (∀ g, starRingEnd ℂ (X γ g) = X γ g) ∧
            (∀ g, starRingEnd ℂ (X ψ g) = X ψ g) ∧
            (∀ g, X η' g = starRingEnd ℂ (X η g)) ∧ (∀ g, X ξκ' g = starRingEnd ℂ (X ξκ g)) ∧
            (∀ g, X ξl' g = starRingEnd ℂ (X ξl g)) ∧
            (∃ g, starRingEnd ℂ (X η g) ≠ X η g) ∧ (∃ g, starRingEnd ℂ (X ξκ g) ≠ X ξκ g) ∧
            (∃ g, starRingEnd ℂ (X ξl g) ≠ X ξl g) ∧
            [principal, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'].Nodup ∧
            B₀ = {principal, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'} ∧
            P principal = 1 ∧ P β = pβ ∧ P κ = pκ ∧ P lam = pl ∧ P γ = 0 ∧ P η = 0 ∧
            P η' = 0 ∧ P ψ = 0 ∧ P ξκ = 0 ∧ P ξκ' = 0 ∧ P ξl = 0 ∧ P ξl' = 0 ∧
            L 2 principal = -1 ∧ L 2 β = -pβ ∧ L 2 κ = pκ ∧ L 2 lam = pl ∧ L 2 γ = 0 ∧
            L 2 η = 0 ∧ L 2 η' = 0 ∧ L 2 ψ = 0 ∧ L 2 ξκ = -pκ ∧ L 2 ξκ' = -pκ ∧
            L 2 ξl = -pl ∧ L 2 ξl' = -pl ∧
            Ax principal = 1 ∧ Ax β = 3 * pβ ∧ Ax κ = pκ ∧ Ax lam = -5 * pl ∧
            Ax γ = -2 * δ ∧ Ax η = -4 * ε ∧ Ax η' = -4 * ε ∧ Ax ψ = -2 * ζ ∧
            Ax ξκ = -3 * pκ ∧ Ax ξκ' = -3 * pκ ∧ Ax ξl = -pl ∧ Ax ξl' = -pl ∧
            Bx principal = 1 ∧ Bx β = 0 ∧ Bx κ = -2 * pκ ∧ Bx lam = pl ∧ Bx γ = δ ∧
            Bx η = -ε ∧ Bx η' = -ε ∧ Bx ψ = ζ ∧ Bx ξκ = 0 ∧ Bx ξκ' = 0 ∧ Bx ξl = -pl ∧
            Bx ξl' = -pl ∧
            T principal = 1 ∧ T β = 3 * pβ ∧ T κ = -3 * pκ ∧ T lam = -pl ∧ T γ = -2 * δ ∧
            T η = -4 * ε * i ∧ T ψ = 2 * ζ ∧ T ξκ = pκ - 2 * i ∧ T ξl = 3 * pl - 2 * i ∧
            T η' = 4 * ε * i ∧ T ξκ' = pκ + 2 * i ∧ T ξl' = 3 * pl + 2 * i ∧
            Ua principal = 1 ∧ Ua β = 0 ∧ Ua κ = 0 ∧ Ua lam = -pl ∧ Ua γ = δ ∧
            Ua η = -ε * i ∧ Ua ψ = -ζ ∧ Ua ξκ = pκ + i ∧ Ua ξl = i ∧
            Ua η' = ε * i ∧ Ua ξκ' = pκ - i ∧ Ua ξl' = -i ∧
            imCoeff i (Ua ξκ) = 1 ∧ imCoeff i (Ua ξl) = 1 ∧
            B₀.filter (fun χ => Odd (deg χ)) = {principal, β, κ, lam, ξκ, ξκ', ξl, ξl'} ∧
            1 + pβ * deg β + pκ * deg κ + pl * deg lam = 0 ∧ deg ξκ = deg κ ∧
            deg ξl = deg lam ∧ ε * deg η = 1 + pβ * deg β ∧ δ * deg γ = -1 - pκ * deg κ ∧
            ζ * deg ψ = 1 + pβ * deg β + 2 * (pκ * deg κ) ∧
            ∀ χ ∈ ({β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'} : Finset basis.index),
              MonoidHom.ker (basis.representation χ).representation = ⊥ ∧ 2 ≤ deg χ := by
  intro H N π aN s w a x C ρ W u iF U₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  subst hn2
  obtain ⟨-, hΦex, hGc⟩ :=
    four_point_central_section_integral_fourier_columns hnonab 2 hn S e alpha
  obtain ⟨-, -, hcol⟩ := four_point_twelve_column_data hnonab 2 hn S e alpha
  refine ⟨rfl, hΦex, fun Φ hΦ => ⟨(hGc Φ hΦ).1, ?_⟩⟩
  intro z hzC hzodd hπz ideal _ _ basis principal hprincipal i hi B₀ X Ax Bx T Ua v f P L deg
  obtain ⟨D, hV, hDB₀, hDp, hDcj, hDd₀, hPL₀, hodd₀, hvals₀⟩ :=
    (hcol Φ hΦ).2 z hzC hzodd hπz ideal basis principal hprincipal i hi
  have hDB : D.B = B₀ := hDB₀
  have hDd : ∀ χ, D.d χ = deg χ := hDd₀
  have hPL : ∀ χ ∈ B₀, (D.P χ : ℝ) = P χ ∧ (D.L₂ χ : ℂ) = L 2 χ := hPL₀
  have hodd : B₀.filter (fun χ => Odd (deg χ)) =
      symmDiff (B₀.filter (fun χ => D.P χ ≠ 0)) (B₀.filter (fun χ => D.Q χ ≠ 0)) := hodd₀
  have hvals : ∀ χ ∈ B₀,
      T χ = ((-2 * D.L₂ χ + 2 * D.cs χ - D.c₂ χ - D.c₁ χ - D.c₃ χ : ℤ) : ℂ) +
          ((2 * ((D.L₃ χ - D.L₁ χ) + (D.c₃ χ - D.c₁ χ)) : ℤ) : ℂ) * i ∧
        Ax χ = ((2 * (D.L₂ χ - D.L₁ χ - D.L₃ χ) - 2 * D.cs χ + 3 * D.c₂ χ - D.c₁ χ -
          D.c₃ χ : ℤ) : ℂ) ∧
        2 * Bx χ = ((D.L₂ χ - D.L₁ χ - D.L₃ χ - 3 * D.c₂ χ + D.c₁ χ + D.c₃ χ +
          2 * D.cs χ : ℤ) : ℂ) ∧
        2 * Ua χ = ((-D.L₂ χ - 2 * D.cs χ + D.c₂ χ + D.c₁ χ + D.c₃ χ : ℤ) : ℂ) +
          ((2 * (D.c₁ χ - D.c₃ χ) + (D.L₃ χ - D.L₁ χ) : ℤ) : ℂ) * i := hvals₀
  clear hDB₀ hDd₀ hPL₀ hodd₀ hvals₀
  obtain ⟨κ, lam, γ, ψ, ξκ, ξl, pβ, pκ, pl, δ, ζ, hC⟩ := hV.classified
  obtain ⟨⟨spβ, spκ, spl, sδ, sζ⟩, hBeq, hnd, ⟨rβ', rκ', rl', rγ', rψ'⟩, rowβ, rowκ, rowl, rowγ,
    rowψ, rowη, rowξκ, rowξl, -, dP, dη, dγ, dψ, dξκ, dξl, hEeq, hJeq⟩ := hC
  simp only [hDB, hDp, hDcj] at hBeq hnd rβ' rκ' rl' rγ' rψ' hEeq hJeq
  have hmem : ∀ χ ∈ ({principal, D.β₁, κ, lam, γ, ψ, D.η₁, conjLabel basis D.η₁, ξκ,
      conjLabel basis ξκ, ξl, conjLabel basis ξl} : Finset basis.index), χ ∈ B₀ := by
    intro χ hχ
    rw [hBeq]
    exact hχ
  have hpB : principal ∈ B₀ := hmem _ (by simp)
  have mβ : D.β₁ ∈ B₀ := hmem _ (by simp)
  have mκ : κ ∈ B₀ := hmem _ (by simp)
  have ml : lam ∈ B₀ := hmem _ (by simp)
  have mγ : γ ∈ B₀ := hmem _ (by simp)
  have mψ : ψ ∈ B₀ := hmem _ (by simp)
  have mη : D.η₁ ∈ B₀ := hmem _ (by simp)
  have mξκ : ξκ ∈ B₀ := hmem _ (by simp)
  have mξl : ξl ∈ B₀ := hmem _ (by simp)
  have hrow : ∀ χ ∈ B₀, ∀ p l₁ l₂ l₃ a₁ a₂ a₃ s₀ : ℤ, D.Row8 χ p l₁ l₂ l₃ a₁ a₂ a₃ s₀ →
      P χ = p ∧ L 2 χ = l₂ ∧
      T χ = ((-2 * l₂ + 2 * s₀ - a₂ - a₁ - a₃ : ℤ) : ℂ) +
          ((2 * ((l₃ - l₁) + (a₃ - a₁)) : ℤ) : ℂ) * i ∧
        Ax χ = ((2 * (l₂ - l₁ - l₃) - 2 * s₀ + 3 * a₂ - a₁ - a₃ : ℤ) : ℂ) ∧
        2 * Bx χ = ((l₂ - l₁ - l₃ - 3 * a₂ + a₁ + a₃ + 2 * s₀ : ℤ) : ℂ) ∧
        2 * Ua χ = ((-l₂ - 2 * s₀ + a₂ + a₁ + a₃ : ℤ) : ℂ) +
          ((2 * (a₁ - a₃) + (l₃ - l₁) : ℤ) : ℂ) * i := by
    intro χ hχ p l₁ l₂ l₃ a₁ a₂ a₃ s₀ hr
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hr
    obtain ⟨e1, e2⟩ := hPL χ hχ
    obtain ⟨t1, t2, t3, t4⟩ := hvals χ hχ
    rw [r1] at e1
    rw [r3] at e2
    simp only [r2, r3, r4, r5, r6, r7, r8] at t1 t2 t3 t4
    exact ⟨e1.symm, e2.symm, t1, t2, t3, t4⟩
  have rowp : D.Row8 principal 1 (-1) (-1) (-1) 1 1 1 1 := by
    rw [← hDp]
    exact ⟨hV.P_p, hV.L₁_p, hV.L₂_p, hV.L₃_p, hV.c₁_p, hV.c₂_p, hV.c₃_p, hV.cs_p⟩
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := rowξκ
  obtain ⟨l1', l2', l3', l4', l5', l6', l7', l8'⟩ := rowξl
  have rowξκ8 : D.Row8 ξκ 0 0 (-pκ) 0 (D.c₁ ξκ) 0 (D.c₃ ξκ) 0 :=
    ⟨k1, k2, k3, k4, rfl, k5, rfl, k6⟩
  have rowξl8 : D.Row8 ξl 0 0 (-pl) 0 (D.c₁ ξl) 0 (D.c₃ ξl) 0 :=
    ⟨l1', l2', l3', l4', rfl, l5', rfl, l6'⟩
  have k7' : (D.c₁ ξκ : ℂ) - D.c₃ ξκ = 1 := by exact_mod_cast k7
  have k8' : (D.c₁ ξκ : ℂ) + D.c₃ ξκ = pκ := by exact_mod_cast k8
  have l7'' : (D.c₁ ξl : ℂ) - D.c₃ ξl = 1 := by exact_mod_cast l7'
  have l8'' : (D.c₁ ξl : ℂ) + D.c₃ ξl = -pl := by exact_mod_cast l8'
  obtain ⟨vpP, vpL, vpT, vpA, vpB, vpU⟩ := hrow principal hpB _ _ _ _ _ _ _ _ rowp
  obtain ⟨vβP, vβL, vβT, vβA, vβB, vβU⟩ := hrow _ mβ _ _ _ _ _ _ _ _ rowβ
  obtain ⟨vκP, vκL, vκT, vκA, vκB, vκU⟩ := hrow _ mκ _ _ _ _ _ _ _ _ rowκ
  obtain ⟨vlP, vlL, vlT, vlA, vlB, vlU⟩ := hrow _ ml _ _ _ _ _ _ _ _ rowl
  obtain ⟨vγP, vγL, vγT, vγA, vγB, vγU⟩ := hrow _ mγ _ _ _ _ _ _ _ _ rowγ
  obtain ⟨vψP, vψL, vψT, vψA, vψB, vψU⟩ := hrow _ mψ _ _ _ _ _ _ _ _ rowψ
  obtain ⟨vηP, vηL, vηT, vηA, vηB, vηU⟩ := hrow _ mη _ _ _ _ _ _ _ _ rowη
  obtain ⟨vκ'P, vκ'L, vκ'T, vκ'A, vκ'B, vκ'U⟩ := hrow _ mξκ _ _ _ _ _ _ _ _ rowξκ8
  obtain ⟨vl'P, vl'L, vl'T, vl'A, vl'B, vl'U⟩ := hrow _ mξl _ _ _ _ _ _ _ _ rowξl8
  have tA_p : Ax principal = 1 := by rw [vpA]; norm_num
  have tB_p : Bx principal = 1 := by push_cast at vpB; linear_combination vpB / 2
  have tT_p : T principal = 1 := by rw [vpT]; push_cast; ring
  have tU_p : Ua principal = 1 := by push_cast at vpU; linear_combination vpU / 2
  have tA_β : Ax D.β₁ = 3 * pβ := by rw [vβA]; push_cast; ring
  have tB_β : Bx D.β₁ = 0 := by push_cast at vβB; linear_combination vβB / 2
  have tT_β : T D.β₁ = 3 * pβ := by rw [vβT]; push_cast; ring
  have tU_β : Ua D.β₁ = 0 := by push_cast at vβU; linear_combination vβU / 2
  have tA_κ : Ax κ = pκ := by rw [vκA]; push_cast; ring
  have tB_κ : Bx κ = -2 * pκ := by push_cast at vκB; linear_combination vκB / 2
  have tT_κ : T κ = -3 * pκ := by rw [vκT]; push_cast; ring
  have tU_κ : Ua κ = 0 := by push_cast at vκU; linear_combination vκU / 2
  have tA_l : Ax lam = -5 * pl := by rw [vlA]; push_cast; ring
  have tB_l : Bx lam = pl := by push_cast at vlB; linear_combination vlB / 2
  have tT_l : T lam = -pl := by rw [vlT]; push_cast; ring
  have tU_l : Ua lam = -pl := by push_cast at vlU; linear_combination vlU / 2
  have tA_γ : Ax γ = -2 * δ := by rw [vγA]; push_cast; ring
  have tB_γ : Bx γ = δ := by push_cast at vγB; linear_combination vγB / 2
  have tT_γ : T γ = -2 * δ := by rw [vγT]; push_cast; ring
  have tU_γ : Ua γ = δ := by push_cast at vγU; linear_combination vγU / 2
  have tA_ψ : Ax ψ = -2 * ζ := by rw [vψA]; push_cast; ring
  have tB_ψ : Bx ψ = ζ := by push_cast at vψB; linear_combination vψB / 2
  have tT_ψ : T ψ = 2 * ζ := by rw [vψT]; push_cast; ring
  have tU_ψ : Ua ψ = -ζ := by push_cast at vψU; linear_combination vψU / 2
  have tA_η : Ax D.η₁ = -4 * D.ε := by rw [vηA]; push_cast; ring
  have tB_η : Bx D.η₁ = -D.ε := by push_cast at vηB; linear_combination vηB / 2
  have tT_η : T D.η₁ = -4 * D.ε * i := by rw [vηT]; push_cast; ring
  have tU_η : Ua D.η₁ = -D.ε * i := by push_cast at vηU; linear_combination vηU / 2
  have tA_ξκ : Ax ξκ = -3 * pκ := by
    rw [vκ'A]
    push_cast
    linear_combination (-1 : ℂ) * k8'
  have tB_ξκ : Bx ξκ = 0 := by
    push_cast at vκ'B
    linear_combination vκ'B / 2 + (1 / 2 : ℂ) * k8'
  have tT_ξκ : T ξκ = pκ - 2 * i := by
    rw [vκ'T]
    push_cast
    linear_combination (-1 : ℂ) * k8' + (-2 * i) * k7'
  have tU_ξκ : Ua ξκ = pκ + i := by
    push_cast at vκ'U
    linear_combination vκ'U / 2 + (1 / 2 : ℂ) * k8' + i * k7'
  have tA_ξl : Ax ξl = -pl := by
    rw [vl'A]
    push_cast
    linear_combination (-1 : ℂ) * l8''
  have tB_ξl : Bx ξl = -pl := by
    push_cast at vl'B
    linear_combination vl'B / 2 + (1 / 2 : ℂ) * l8''
  have tT_ξl : T ξl = 3 * pl - 2 * i := by
    rw [vl'T]
    push_cast
    linear_combination (-1 : ℂ) * l8'' + (-2 * i) * l7''
  have tU_ξl : Ua ξl = i := by
    push_cast at vl'U
    linear_combination vl'U / 2 + (1 / 2 : ℂ) * l8'' + i * l7''
  have hcj : ∀ χ g, X (conjLabel basis χ) g = starRingEnd ℂ (X χ g) := conjLabel_spec basis
  have hci : starRingEnd ℂ i = -i := FourPointThreePairs.conj_eq_neg_of_sq_eq_neg_one hi
  have cjP : ∀ χ, P (conjLabel basis χ) = P χ := fun χ => by
    change (X (conjLabel basis χ) ρ).re = (X χ ρ).re
    rw [hcj, Complex.conj_re]
  have cjL : ∀ χ ∈ B₀, L 2 (conjLabel basis χ) = L 2 χ := by
    intro χ hχ
    have hcB := (hDcj χ) ▸ hV.cj_mem χ (hDB ▸ hχ)
    rw [hDB] at hcB
    rw [← (hPL _ hcB).2, ← (hPL χ hχ).2, ← hDcj, hV.L₂_cj χ (hDB ▸ hχ)]
  have cjA : ∀ χ, Ax (conjLabel basis χ) = starRingEnd ℂ (Ax χ) := fun χ => hcj χ x
  have cjB : ∀ χ, Bx (conjLabel basis χ) = starRingEnd ℂ (Bx χ) := fun χ => hcj χ (x * z)
  have cjT : ∀ χ, T (conjLabel basis χ) = starRingEnd ℂ (T χ) := fun χ => hcj χ a
  have cjU : ∀ χ, Ua (conjLabel basis χ) = starRingEnd ℂ (Ua χ) := fun χ => hcj χ (a * z)
  have hreal : ∀ χ, conjLabel basis χ = χ → ∀ g, starRingEnd ℂ (X χ g) = X χ g := by
    intro χ hχ g
    rw [← hcj, hχ]
  have hnonreal : ∀ χ, χ ≠ conjLabel basis χ → ∃ g, starRingEnd ℂ (X χ g) ≠ X χ g := by
    intro χ hχ
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hχ (conjLabel_eq_of_spec basis χ χ fun g => (hc g).symm).symm
  have hne_of : ∀ {a b : basis.index} {l : List basis.index}, (a :: l).Nodup → b ∈ l → a ≠ b :=
    fun hn hb e => (List.nodup_cons.mp hn).1 (e ▸ hb)
  have hnd_η := hnd.sublist (List.drop_sublist 6 _)
  have hnd_ξκ := hnd.sublist (List.drop_sublist 8 _)
  have hnd_ξl := hnd.sublist (List.drop_sublist 10 _)
  have hηne : D.η₁ ≠ conjLabel basis D.η₁ := hne_of hnd_η (by simp)
  have hξκne : ξκ ≠ conjLabel basis ξκ := hne_of hnd_ξκ (by simp)
  have hξlne : ξl ≠ conjLabel basis ξl := hne_of hnd_ξl (by simp)
  have hnd8 : ([principal, D.β₁, κ, lam] ++ [ξκ, conjLabel basis ξκ, ξl,
      conjLabel basis ξl]).Nodup :=
    hnd.sublist ((List.sublist_append_right [γ, ψ, D.η₁, conjLabel basis D.η₁]
      [ξκ, conjLabel basis ξκ, ξl, conjLabel basis ξl]).append_left
        [principal, D.β₁, κ, lam])
  have hdisj : Disjoint ({principal, D.β₁, κ, lam} : Finset basis.index)
      {ξκ, conjLabel basis ξκ, ξl, conjLabel basis ξl} := by
    rw [Finset.disjoint_left]
    intro χ h1 h2
    rw [List.nodup_append] at hnd8
    have h1' : χ ∈ [principal, D.β₁, κ, lam] := by simpa using h1
    have h2' : χ ∈ [ξκ, conjLabel basis ξκ, ξl, conjLabel basis ξl] := by simpa using h2
    exact hnd8.2.2 χ h1' χ h2' rfl
  have hoddeq : B₀.filter (fun χ => Odd (deg χ)) =
      {principal, D.β₁, κ, lam, ξκ, conjLabel basis ξκ, ξl, conjLabel basis ξl} := by
    rw [hodd, hEeq, hJeq, hdisj.symmDiff_eq_sup]
    ext χ
    simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      or_assoc]
  have hfaith : ∀ χ ∈ ({D.β₁, κ, lam, γ, ψ, D.η₁, conjLabel basis D.η₁, ξκ, conjLabel basis ξκ,
      ξl, conjLabel basis ξl} : Finset basis.index),
      MonoidHom.ker (basis.representation χ).representation = ⊥ ∧ 2 ≤ deg χ := by
    intro χ hχ
    have hne : χ ≠ principal := by
      intro e
      apply (List.nodup_cons.mp hnd).1
      rw [← e]
      simpa using hχ
    have hne1 : (basis.representation χ).character ≠ 1 := fun h1 =>
      hne (basis.distinct (show (basis.representation χ).character =
        (basis.representation principal).character by rw [h1, hprincipal]))
    exact ⟨ker_eq_bot_of_character_ne_one _ (basis.irreducible χ) hne1,
      FourPointThreePairs.two_le_finrank_of_character_ne_one hnonab _ (basis.irreducible χ) hne1⟩
  have tA_η' : Ax (conjLabel basis D.η₁) = -4 * D.ε := by
    rw [cjA, tA_η]
    simp only [map_mul, map_neg, map_ofNat, map_intCast]
  have tB_η' : Bx (conjLabel basis D.η₁) = -D.ε := by
    rw [cjB, tB_η]
    simp only [map_neg, map_intCast]
  have tT_η' : T (conjLabel basis D.η₁) = 4 * D.ε * i := by
    rw [cjT, tT_η]
    simp only [map_mul, map_neg, map_ofNat, map_intCast, hci]
    ring
  have tU_η' : Ua (conjLabel basis D.η₁) = D.ε * i := by
    rw [cjU, tU_η]
    simp only [map_mul, map_neg, map_intCast, hci]
    ring
  have tA_ξκ' : Ax (conjLabel basis ξκ) = -3 * pκ := by
    rw [cjA, tA_ξκ]
    simp only [map_mul, map_neg, map_ofNat, map_intCast]
  have tB_ξκ' : Bx (conjLabel basis ξκ) = 0 := by
    rw [cjB, tB_ξκ, map_zero]
  have tT_ξκ' : T (conjLabel basis ξκ) = pκ + 2 * i := by
    rw [cjT, tT_ξκ]
    simp only [map_sub, map_mul, map_ofNat, map_intCast, hci]
    ring
  have tU_ξκ' : Ua (conjLabel basis ξκ) = pκ - i := by
    rw [cjU, tU_ξκ]
    simp only [map_add, map_intCast, hci]
    ring
  have tA_ξl' : Ax (conjLabel basis ξl) = -pl := by
    rw [cjA, tA_ξl]
    simp only [map_neg, map_intCast]
  have tB_ξl' : Bx (conjLabel basis ξl) = -pl := by
    rw [cjB, tB_ξl]
    simp only [map_neg, map_intCast]
  have tT_ξl' : T (conjLabel basis ξl) = 3 * pl + 2 * i := by
    rw [cjT, tT_ξl]
    simp only [map_sub, map_mul, map_ofNat, map_intCast, hci]
    ring
  have tU_ξl' : Ua (conjLabel basis ξl) = -i := by
    rw [cjU, tU_ξl, hci]
  have hImξκ : imCoeff i (Ua ξκ) = 1 := by
    rw [tU_ξκ, show ((pκ : ℂ) + i) = ((pκ : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * i by push_cast; ring,
      imCoeff_add_mul hi]
  have hImξl : imCoeff i (Ua ξl) = 1 := by
    rw [tU_ξl, imCoeff]
    exact div_self (im_ne_zero hi)
  have hprinreal : ∀ g, starRingEnd ℂ (X principal g) = X principal g := fun g => by
    show starRingEnd ℂ ((basis.representation principal).character g) =
      (basis.representation principal).character g
    rw [hprincipal, Pi.one_apply, map_one]
  simp only [hDd] at dP dη dγ dψ dξκ dξl
  exact ⟨D.β₁, κ, lam, γ, ψ, D.η₁, conjLabel basis D.η₁, ξκ, conjLabel basis ξκ, ξl,
    conjLabel basis ξl, pβ, pκ, pl, δ, D.ε, ζ, spβ, spκ, spl, sδ, hV.ε_val, sζ, hprinreal,
    hreal _ rβ', hreal _ rκ', hreal _ rl', hreal _ rγ', hreal _ rψ', hcj D.η₁, hcj ξκ, hcj ξl,
    hnonreal _ hηne, hnonreal _ hξκne, hnonreal _ hξlne, hnd, hBeq,
    by exact_mod_cast vpP, vβP, vκP, vlP, by exact_mod_cast vγP, by exact_mod_cast vηP,
    by rw [cjP]; exact_mod_cast vηP, by exact_mod_cast vψP, by exact_mod_cast vκ'P,
    by rw [cjP]; exact_mod_cast vκ'P, by exact_mod_cast vl'P, by rw [cjP]; exact_mod_cast vl'P,
    by exact_mod_cast vpL, by rw [vβL]; push_cast; ring, by exact_mod_cast vκL,
    by exact_mod_cast vlL, by exact_mod_cast vγL, by exact_mod_cast vηL,
    by rw [cjL _ mη]; exact_mod_cast vηL, by exact_mod_cast vψL,
    by rw [vκ'L]; push_cast; ring, by rw [cjL _ mξκ, vκ'L]; push_cast; ring,
    by rw [vl'L]; push_cast; ring, by rw [cjL _ mξl, vl'L]; push_cast; ring,
    tA_p, tA_β, tA_κ, tA_l, tA_γ, tA_η, tA_η', tA_ψ, tA_ξκ, tA_ξκ', tA_ξl, tA_ξl',
    tB_p, tB_β, tB_κ, tB_l, tB_γ, tB_η, tB_η', tB_ψ, tB_ξκ, tB_ξκ', tB_ξl, tB_ξl',
    tT_p, tT_β, tT_κ, tT_l, tT_γ, tT_η, tT_ψ, tT_ξκ, tT_ξl, tT_η', tT_ξκ', tT_ξl',
    tU_p, tU_β, tU_κ, tU_l, tU_γ, tU_η, tU_ψ, tU_ξκ, tU_ξl, tU_η', tU_ξκ', tU_ξl',
    hImξκ, hImξl, hoddeq, dP, by exact_mod_cast dξκ, by exact_mod_cast dξl, dη, dγ, dψ,
    hfaith⟩

end CFSG.Wreathed.FourPointTwelveCharacters

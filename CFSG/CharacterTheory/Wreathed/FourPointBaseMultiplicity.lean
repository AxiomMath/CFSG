module

public import CFSG.CharacterTheory.Wreathed.FourPointBaseMultiplicityColumns
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseAssembly
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseGenericColumns
public import CFSG.CharacterTheory.Wreathed.FourPointBaseMultiplicitySupport
public import CFSG.CharacterTheory.Wreathed.FourPointRemainingOrderFourSection
public import CFSG.CharacterTheory.Wreathed.FourPointThreePairs
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusionExistence

public noncomputable section

namespace CFSG.Wreathed.FourPointBaseMultiplicity

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.FourPointOrderFour
  CFSG.Wreathed.FourPointGaussianColumns CFSG.Wreathed.FourPointCentralFourier
  CFSG.Wreathed.FourPointOrderEight CFSG.Wreathed.WreathCentralSquare
  CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.OrderThirtyTwo CFSG.Wreathed.ConditionalGeneralBase
  CFSG.Wreathed.ConditionalFourier

open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_base_multiplicity_integral_columns_and_gram
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let H := centralizerOddCoreQuotient n S e
    let N := involutionCentralizer n S e
    let π := centralizerOddCoreMap n S e
    let aN : N := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))
    let s : G := wreathModelHom S e (Original.s (2 ^ n))
    let t : G := wreathModelHom S e (Original.t (2 ^ n))
    let w : G := wreathModelHom S e (Original.z (2 ^ n))
    let a : G := wreathModelHom S e (Original.a (2 ^ n))
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let C := orderFourCentralizer n S e
    let U : Subgroup G := Subgroup.closure {s, t}
    let ρ : G := s * w
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let u := cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let iF := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let U₀ : W := iF (CentralSL2.upperSL (ZMod 3) 1)
    n = 2 ∧ (∃ Φ : W ≃* H, Φ (u ^ 2) = π aN) ∧
    (∃ σ υ g : G, ((σ = s ∧ υ = t) ∨ (σ = s ^ 2 * t ^ 3 ∧ υ = s ^ 3 * t ^ 2)) ∧
      IsAdaptedBase U a w σ υ g) ∧
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
          let L : ZMod 4 → basis.index → ℂ := fun j χ => f χ j.val 0
          let h : ZMod 4 → basis.index → ℂ := fun j χ => f χ j.val 1
          ∀ σ υ g : G, ∀ hA : IsAdaptedBase U a w σ υ g,
          (∃ lam : ZMod 4 → ZMod 4 → U →* ℂ, ∀ r s' : ZMod 4,
            lam r s' ⟨σ, hA.left_mem⟩ = i ^ r.val ∧ lam r s' ⟨υ, hA.right_mem⟩ = i ^ s'.val) ∧
          ∀ lam : ZMod 4 → ZMod 4 → U →* ℂ, (∀ r s' : ZMod 4,
            lam r s' ⟨σ, hA.left_mem⟩ = i ^ r.val ∧ lam r s' ⟨υ, hA.right_mem⟩ = i ^ s'.val) →
          let tm : ZMod 4 → ZMod 4 → basis.index → ℂ := fun r s' χ =>
            (Nat.card U : ℂ)⁻¹ * ∑ y : U, X χ y * starRingEnd ℂ (lam r s' y)
          let c : ZMod 4 → ZMod 4 → basis.index → ℂ := fun r s' χ =>
            tm 0 0 χ - tm r s' χ + h (-r - s') χ + h r χ + h s' χ
          let O : Fin 5 → Finset (ZMod 4 × ZMod 4) :=
            ![{(0, 0)}, {(1, 1), (1, 2), (2, 1)}, {(2, 2), (2, 0), (0, 2)},
              {(3, 3), (3, 2), (2, 3)}, {(1, 0), (0, 1), (3, 1), (1, 3), (0, 3), (3, 0)}]
          let col : Fin 4 → basis.index → ℂ := ![c 1 1, c 2 2, c 3 3, c 1 0]
          let Gr : Matrix (Fin 4) (Fin 4) ℤ :=
            !![8, 6, 6, 6; 6, 8, 6, 6; 6, 6, 8, 6; 6, 6, 6, 7]
          (∀ r s' : ZMod 4, ∀ χ, ∃ k : ℕ, tm r s' χ = k) ∧
          (∀ j : ZMod 4, ∀ χ ∈ B₀, (∃ k : ℤ, L j χ = k) ∧ ∃ k : ℤ, h j χ = k) ∧
          (∀ r s' : ZMod 4, ∀ χ ∈ B₀, ∃ k : ℤ, c r s' χ = k) ∧
          (∀ k : Fin 5, ∀ p ∈ O k, ∀ q ∈ O k, ∀ χ, c p.1 p.2 χ = c q.1 q.2 χ) ∧
          (∀ χ, c 0 0 χ = 0) ∧ (∀ l, col l principal = 1) ∧
          (∀ χ ∈ B₀, ∀ ψ : basis.index, (∀ g', X ψ g' = starRingEnd ℂ (X χ g')) →
            c 1 1 ψ = c 3 3 χ ∧ c 3 3 ψ = c 1 1 χ ∧ c 2 2 ψ = c 2 2 χ ∧ c 1 0 ψ = c 1 0 χ) ∧
          (∀ l, ∑ χ ∈ B₀, col l χ * d χ = 0 ∧ (∀ j : ZMod 4, ∑ χ ∈ B₀, col l χ * L j χ = 0) ∧
            ∑ χ ∈ B₀, col l χ * P χ = 0 ∧ ∑ χ ∈ B₀, col l χ * Q χ = 0) ∧
          (∀ l l', ∑ χ ∈ B₀, col l χ * col l' χ = Gr l l') ∧
          (∀ χ ∈ B₀, L 1 χ - 2 * h 1 χ = c 2 2 χ - 2 * c 1 1 χ ∧
            L 3 χ - 2 * h 3 χ = c 2 2 χ - 2 * c 3 3 χ ∧
            L 2 χ - 2 * h 2 χ = 2 * c 1 0 χ - c 2 2 χ - c 1 1 χ - c 3 3 χ) ∧
          (∀ χ ∈ B₀, (∃ k : ℤ, c 2 2 χ = L 1 χ + 2 * k) ∧ (∃ k : ℤ, L 1 χ = P χ + 2 * k) ∧
            ∃ k : ℤ, c 1 1 χ + c 3 3 χ = Q χ + 2 * k) ∧
          ∀ χ ∈ B₀,
            c 1 1 χ - c 3 3 χ = ((4 * imCoeff i (Ua χ) - imCoeff i (T χ)) / 6 : ℝ) ∧
            T χ = -2 * L 2 χ + 2 * c 1 0 χ - c 2 2 χ - c 1 1 χ - c 3 3 χ +
              2 * i * ((L 3 χ - L 1 χ) + (c 3 3 χ - c 1 1 χ)) ∧
            Ax χ = 2 * (L 2 χ - L 1 χ - L 3 χ) - 2 * c 1 0 χ + 3 * c 2 2 χ - c 1 1 χ - c 3 3 χ ∧
            Bx χ = (L 2 χ - L 1 χ - L 3 χ - 3 * c 2 2 χ + c 1 1 χ + c 3 3 χ) / 2 + c 1 0 χ ∧
            ((Ua χ).re : ℂ) = (-L 2 χ - 2 * c 1 0 χ + c 2 2 χ + c 1 1 χ + c 3 3 χ) / 2 := by
  intro H N π aN s t w a x C U ρ W u iF U₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  subst hn2
  obtain ⟨-, hΦex, hGc⟩ :=
    four_point_central_section_integral_fourier_columns hnonab 2 hn S e alpha
  obtain ⟨-, -, hρord, -, -, -, -, -, -, -, -, -, -, -, -, hGo⟩ :=
    four_point_order_eight_centralizer_and_norm_four_columns hnonab 2 hn S e alpha
  obtain ⟨-, -, hGp⟩ :=
    FourPointThreePairs.four_point_fourier_support_three_pairs_and_adjacent_degrees hnonab 2 hn
      S e alpha
  have hU : U = modelBase S e := by
    rw [modelBase, ← Original.U_eq, Original.U, MonoidHom.map_closure, Set.image_pair]
  clear_value U
  subst hU
  refine ⟨rfl, hΦex, exists_isAdaptedBase_special hnonab, fun Φ hΦ => ⟨(hGc Φ hΦ).1, ?_⟩⟩
  intro z hzC hzodd hπz ideal _ _ basis principal hprincipal i hi B₀ X d Ax Bx T Ua v f P Q L h
  obtain ⟨hfint, hfgram, hfdeg, hfprin, hsec, hinv, -, hconjf, -⟩ :=
    (hGc Φ hΦ).2 z hzC hzodd hπz ideal basis principal hprincipal i hi
  obtain ⟨hPQint, -, -, -, -, -, -, -, -, hPQf, -⟩ :=
    (hGo Φ hΦ).2 z hzC hzodd hπz ideal basis principal hprincipal i hi
  obtain ⟨hpar, -⟩ := (hGp Φ hΦ).2 z hzC hzodd hπz ideal basis principal hprincipal i hi
  have hfint' : ∀ χ ∈ B₀, ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, ∃ k : ℤ, f χ j ℓ = k := hfint
  have hfgram' : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3, ∀ ℓ t,
      ∑ χ ∈ B₀, f χ j ℓ * f χ k t = ((if j = k then 1 else 0) + 1) *
        (((!![16, 8; 8, 12] : Matrix (Fin 2) (Fin 2) ℤ) ℓ t : ℤ) : ℂ) / 4 := hfgram
  have hfdeg' : ∀ (j : ℕ) ℓ, ∑ χ ∈ B₀, d χ * f χ j ℓ = 0 := hfdeg
  have hfprin' : ∀ j ∈ Finset.Icc 1 3, f principal j 0 = -1 ∧ f principal j 1 = 0 := hfprin
  have hinv' : ∀ χ ∈ B₀, ∀ n' ∈ Finset.Icc 1 3, ∀ ℓ,
      v χ n' ℓ = ∑ j ∈ Finset.Icc 1 3, f χ j ℓ * i ^ (-((j : ℤ) * n')) := hinv
  have hconjf' : ∀ χ ∈ B₀, ∀ χ' : basis.index, (∀ g, X χ' g = starRingEnd ℂ (X χ g)) →
      ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, f χ' j ℓ = f χ (4 - j) ℓ := hconjf
  have hPQint' : ∀ χ ∈ B₀, (∃ k : ℤ, P χ = k) ∧ ∃ k : ℤ, Q χ = k := hPQint
  have hPQf' : ∀ j ∈ Finset.Icc 1 3, ∀ ℓ,
      ∑ χ ∈ B₀, (P χ : ℂ) * f χ j ℓ = 0 ∧ ∑ χ ∈ B₀, (Q χ : ℂ) * f χ j ℓ = 0 := hPQf
  have hpar' : ∀ χ ∈ B₀, (∃ k : ℤ, f χ 1 0 = P χ + 2 * k) ∧
      ∃ k : ℤ, f χ 2 0 = P χ + Q χ + 2 * k := fun χ hχ =>
    ⟨(hpar χ hχ).2.1, (hpar χ hχ).2.2.2.2.1⟩
  have hρord' : orderOf ρ = 2 * 2 ^ 2 := by rw [hρord]; norm_num
  have hIcc : Finset.Icc 1 3 = Finset.Ico 1 4 := by decide
  have hcases : ∀ j : ZMod 4, j.val = 0 ∨ j.val ∈ Finset.Icc 1 3 := by decide
  have hnegval : ∀ j : ZMod 4, j.val ∈ Finset.Icc 1 3 → (-j).val = 4 - j.val := by decide
  have hnegval0 : ∀ j : ZMod 4, j.val = 0 → (-j).val = 0 := by decide
  have hf0 : ∀ χ ℓ, f χ 0 ℓ = 0 := by
    intro χ ℓ
    simp only [f, zero_mul, pow_zero, sub_self, Finset.sum_const_zero, mul_zero]
  have hfZ : ∀ χ ∈ B₀, ∀ (j : ZMod 4) ℓ, ∃ k : ℤ, f χ j.val ℓ = k := by
    intro χ hχ j ℓ
    rcases hcases j with h0 | hj
    · exact ⟨0, by rw [h0, hf0, Int.cast_zero]⟩
    · exact hfint' χ hχ j.val hj ℓ
  have hfreal : ∀ χ ∈ B₀, ∀ (j : ZMod 4) ℓ, conj (f χ j.val ℓ) = f χ j.val ℓ := by
    intro χ hχ j ℓ
    obtain ⟨k, hk⟩ := hfZ χ hχ j ℓ
    rw [hk, map_intCast]
  have hfgram00 : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3,
      ∑ χ ∈ B₀, f χ j 0 * f χ k 0 = 4 * ((if j = k then 1 else 0) + 1) := by
    intro j hj k hk
    rw [hfgram' j hj k hk 0 0]
    simp
    ring
  have hfgram10 : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3,
      ∑ χ ∈ B₀, f χ j 1 * f χ k 0 = 2 * ((if j = k then 1 else 0) + 1) := by
    intro j hj k hk
    rw [hfgram' j hj k hk 1 0]
    simp
    ring
  have hfgram01 : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3,
      ∑ χ ∈ B₀, f χ j 0 * f χ k 1 = 2 * ((if j = k then 1 else 0) + 1) := by
    intro j hj k hk
    rw [hfgram' j hj k hk 0 1]
    simp
    ring
  have hfgram11 : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3,
      ∑ χ ∈ B₀, f χ j 1 * f χ k 1 = 3 * ((if j = k then 1 else 0) + 1) := by
    intro j hj k hk
    rw [hfgram' j hj k hk 1 1]
    simp
    ring
  have hza : Commute (z : G) a := Subgroup.mem_centralizer_singleton_iff.mp hzC
  have hzk : ∀ k : ℕ, (z : G) ∈ Subgroup.centralizer ({a ^ k} : Set G) := fun k =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hza.pow_right k).eq
  have hzodd' : Odd (orderOf (z : G)) := by rw [Subgroup.orderOf_coe]; exact hzodd
  have hzR : (z : G) ∉ (centralizerOddCore 2 S e).map (involutionCentralizer 2 S e).subtype ⊓
      C := by
    rintro ⟨hzR, -⟩
    obtain ⟨r, hr, hrz⟩ := Subgroup.mem_map.mp hzR
    have hrz' : r = z := Subtype.ext hrz
    have h1 : π z = 1 := by
      rw [← hrz']
      exact (QuotientGroup.eq_one_iff r).mpr hr
    have hord : orderOf (Φ U₀) = 3 := (odd_classes_of_equiv Φ).1
    rw [← hπz, h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hvals : ∀ χ ∈ B₀, ∀ k ∈ Finset.Icc 1 3,
      X χ (a ^ k) = v χ k 0 + 2 * v χ k 1 ∧ X χ (a ^ k * z) = v χ k 0 - v χ k 1 := by
    intro χ hχ k hk
    have h1 := hsec χ hχ k hk 1 (by rw [orderOf_one]; exact odd_one)
    have h2 := hsec χ hχ k hk ⟨z, hzC⟩ (by rw [Subgroup.orderOf_mk]; exact hzodd')
    split_ifs at h1 with hm1
    · split_ifs at h2 with hm2
      · exact absurd hm2 hzR
      · have h1' : X χ (a ^ k * 1) = v χ k 0 + v χ k 1 * (3 * 1 - 1) := h1
        have h2' : X χ (a ^ k * z) = v χ k 0 + v χ k 1 * (3 * 0 - 1) := h2
        rw [mul_one] at h1'
        refine ⟨?_, ?_⟩
        · rw [h1']
          ring
        · rw [h2']
          ring
    · exact absurd (Subgroup.one_mem _) hm1
  intro σ υ g hA
  have hc : Commute hA.left hA.right := commute_left_right hA
  have hgen : Subgroup.closure ({hA.left, hA.right} : Set (modelBase S e)) = ⊤ :=
    hA.closure_eq_top
  have hσ : orderOf hA.left = 4 := orderOf_left' hA
  have hυ : orderOf hA.right = 4 := orderOf_right' hA
  have hint : Subgroup.zpowers hA.left ⊓ Subgroup.zpowers hA.right = ⊥ :=
    zpowers_left_inf_right' hA
  have hζ : IsPrimitiveRoot i 4 := isPrimitiveRoot_of_sq_eq_neg_one hi
  refine ⟨exists_linearCharacters hc hgen hσ hυ hint hζ, ?_⟩
  intro lam hlam tm c O col Gr
  have hlam' : ∀ r s' : ZMod 4, lam r s' hA.left = i ^ r.val ∧ lam r s' hA.right = i ^ s'.val :=
    hlam
  have hcardU : (Fintype.card (modelBase S e) : ℂ) = ((4 : ℕ) : ℂ) ^ 2 := by
    rw [card_eq_sq hc hgen hσ hυ hint hζ lam hlam']
    push_cast
    ring
  let χres : basis.index → modelBase S e → ℂ := fun χ y => X χ y
  let v' : basis.index → ℕ → Fin 2 → ℂ := fun χ k => ![v χ k 0 - 4 * v χ k 1, v χ k 1]
  have hcbase : ∀ r s' χ, c r s' χ = baseColumn lam (χres χ) i (v' χ) 1 r s' := by
    intro r s' χ
    simp only [c, tm, h, f, baseColumn, baseMultiplicity, zmodFourier, fourierTransform, χres,
      v', Nat.card_eq_fintype_card, hIcc, Matrix.cons_val_one, Matrix.cons_val_zero,
      Nat.cast_ofNat]
    ring
  set h6 := sixAut hA with hh6
  have h6σ : ∀ k, h6 k hA.left = ![hA.left, hA.right, hA.right, (hA.left * hA.right)⁻¹, hA.left,
      (hA.left * hA.right)⁻¹] k := sixAut_left hA
  have h6υ : ∀ k, h6 k hA.right = ![hA.right, hA.left, (hA.left * hA.right)⁻¹, hA.left,
      (hA.left * hA.right)⁻¹, hA.right] k := sixAut_right hA
  have hcharconj : ∀ (χ : basis.index) {y y' : G}, IsConj y y' → X χ y = X χ y' := by
    intro χ y y' hyy
    obtain ⟨c', rfl⟩ := isConj_iff.mp hyy
    exact (Representation.char_conj _ y c').symm
  have hχconj : ∀ χ k y, χres χ (h6 k y) = χres χ y := fun χ k y =>
    (hcharconj χ ((isConj_iff_exists_sixAut hA hn y _).mpr ⟨k, rfl⟩)).symm
  set Pg := Finset.univ.filter (fun y : modelBase S e => y ∉ hA.exc) with hPg
  have hsplit : ∀ F' : modelBase S e → ℂ, ∑ y, F' y = F' 1 + ∑ k ∈ Finset.Ico 1 4,
      (F' ((hA.left * hA.right) ^ k) + F' (hA.left ^ k)⁻¹ + F' (hA.right ^ k)⁻¹) +
      ∑ y ∈ Pg, F' y := sum_split_exc hA
  have hPmem : ∀ y ∈ Pg, ∀ k, h6 k y ∈ Pg := by
    intro y hy k
    rw [hPg, Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, fun hmem => hy.2 ?_⟩
    have h1 := mem_exc_of_mem_closure hA (Subgroup.inv_mem _ (sixAut_mem hA k)) hmem
    rwa [MulAut.inv_apply_self] at h1
  have hPinj : ∀ y ∈ Pg, Function.Injective (fun k => h6 k y) := by
    intro y hy
    rw [hPg, Finset.mem_filter] at hy
    exact sixAut_apply_injective hA hn hy.2
  have hPne : ∀ y ∈ Pg, y ∉ hA.exc := fun y hy => (Finset.mem_filter.mp hy).2
  have htriple : ∀ χ, ∀ k ∈ Finset.Ico 1 4,
      χres χ (hA.left ^ k)⁻¹ = χres χ ((hA.left * hA.right) ^ k) ∧
      χres χ (hA.right ^ k)⁻¹ = χres χ ((hA.left * hA.right) ^ k) := by
    intro χ k _
    have h1 := isConj_mul_zpow_left hA (k : ℤ)
    have h2 := isConj_mul_zpow_right hA (k : ℤ)
    rw [zpow_neg, zpow_natCast, zpow_natCast] at h1 h2
    exact ⟨(hcharconj χ h1).symm, (hcharconj χ h2).symm⟩
  have hpowcoe : ∀ k : ℕ, (((hA.left * hA.right) ^ k : modelBase S e) : G) = a ^ k := by
    intro k
    rw [Subgroup.coe_pow, hA.coe_left_mul_right]
  have hval : ∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 4,
      χres χ ((hA.left * hA.right) ^ k) = v' χ k 0 + (2 + ((4 : ℕ) : ℂ) * 1) * v' χ k 1 := by
    intro χ hχ k hk
    rw [← hIcc] at hk
    simp only [χres, v', hpowcoe, (hvals χ hχ k hk).1, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    push_cast
    ring
  have hnorm : ∀ r s', ∀ χ ∈ B₀, ((4 : ℕ) : ℂ) ^ 2 * c r s' χ =
      ∑ k ∈ Finset.Ico 1 4, ((1 - conj (lam r s' ((hA.left * hA.right) ^ k))) +
        (1 - conj (lam r s' (hA.left ^ k)⁻¹)) + (1 - conj (lam r s' (hA.right ^ k)⁻¹))) *
          (v' χ k 0 + 2 * v' χ k 1) +
      ∑ y ∈ Pg, (1 - conj (lam r s' y)) * χres χ y := by
    intro r s' χ hχ
    rw [hcbase, ← hcardU]
    exact card_mul_column_eq hc hgen hσ hυ hint hζ lam hlam' Pg hsplit (χres χ) (v' χ) 1
      (htriple χ) (hval χ hχ) r s'
  let Z : basis.index → ℕ → ℂ := fun χ k => v' χ k 0 + 2 * v' χ k 1
  let gg : ℕ → basis.index → ℂ := fun j χ => f χ j 0 - 2 * f χ j 1
  have hZexp : ∀ χ ∈ B₀, ∀ k ∈ Finset.Icc 1 3,
      Z χ k = ∑ j ∈ Finset.Icc 1 3, gg j χ * i ^ (-((j : ℤ) * k)) := by
    intro χ hχ k hk
    have e1 : Z χ k = v χ k 0 - 2 * v χ k 1 := by
      simp only [Z, v', Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [e1, hinv' χ hχ k hk 0, hinv' χ hχ k hk 1, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [gg]; ring
  have hgreal : ∀ j ∈ Finset.Icc 1 3, ∀ χ ∈ B₀, conj (gg j χ) = gg j χ := by
    intro j hj χ hχ
    obtain ⟨k0, hk0⟩ := hfint' χ hχ j hj 0
    obtain ⟨k1, hk1⟩ := hfint' χ hχ j hj 1
    simp only [gg, hk0, hk1, map_sub, map_mul, map_intCast, map_ofNat]
  have hggram : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3,
      ∑ χ ∈ B₀, gg j χ * gg k χ = 8 * ((if j = k then 1 else 0) + 1) := by
    intro j hj k hk
    have hexp : ∀ χ, gg j χ * gg k χ = f χ j 0 * f χ k 0 - 2 * (f χ j 0 * f χ k 1) -
        2 * (f χ j 1 * f χ k 0) + 4 * (f χ j 1 * f χ k 1) := fun χ => by
      simp only [gg]
      ring
    rw [Finset.sum_congr rfl fun χ _ => hexp χ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hfgram00 j hj k hk, hfgram01 j hj k hk, hfgram10 j hj k hk, hfgram11 j hj k hk]
    ring
  have hZ1 : ∀ χ ∈ B₀, Z χ 1 = -i * gg 1 χ + -1 * gg 2 χ + i * gg 3 χ := by
    intro χ hχ
    rw [hZexp χ hχ 1 (by decide)]
    linear_combination inverse_one hi (fun j => gg j χ)
  have hZ2 : ∀ χ ∈ B₀, Z χ 2 = -1 * gg 1 χ + 1 * gg 2 χ + -1 * gg 3 χ := by
    intro χ hχ
    rw [hZexp χ hχ 2 (by decide)]
    linear_combination inverse_two hi (fun j => gg j χ)
  have hZ3 : ∀ χ ∈ B₀, Z χ 3 = i * gg 1 χ + -1 * gg 2 χ + -i * gg 3 χ := by
    intro χ hχ
    rw [hZexp χ hχ 3 (by decide)]
    linear_combination inverse_three hi (fun j => gg j χ)
  have hZZ := rows_gram B₀ hi gg hgreal hggram Z hZ1 hZ2 hZ3
  have hWv : ∀ y ∈ Pg, ∀ k ∈ Finset.Icc 1 3, ∀ ℓ : Fin 2,
      ∑ χ ∈ B₀, χres χ y * conj (v χ k ℓ) = 0 := by
    intro y hy k hk ℓ
    have hcs1 := generic_column_central_section hA hn basis ideal principal hprincipal
      (hPne y hy) k (Subgroup.one_mem _) (by rw [orderOf_one]; exact odd_one)
    have hcsz := generic_column_central_section hA hn basis ideal principal hprincipal
      (hPne y hy) k (hzk k) hzodd'
    fin_cases ℓ
    · refine sum_mul_conj_comb B₀ (fun χ => χres χ y) (fun χ => X χ (a ^ k * 1))
        (fun χ => X χ (a ^ k * z)) (fun χ => v χ k 0) (1 / 3) (2 / 3) (fun χ hχ => ?_) hcs1 hcsz
      obtain ⟨e1, e2⟩ := hvals χ hχ k hk
      simp only [mul_one]
      rw [e1, e2]
      ring
    · refine sum_mul_conj_comb B₀ (fun χ => χres χ y) (fun χ => X χ (a ^ k * 1))
        (fun χ => X χ (a ^ k * z)) (fun χ => v χ k 1) (1 / 3) (-1 / 3) (fun χ hχ => ?_) hcs1
        hcsz
      obtain ⟨e1, e2⟩ := hvals χ hχ k hk
      simp only [mul_one]
      rw [e1, e2]
      ring
  have hZW : ∀ k ∈ Finset.Ico 1 4, ∀ y ∈ Pg, ∑ χ ∈ B₀, Z χ k * conj (χres χ y) = 0 := by
    intro k hk y hy
    rw [← hIcc] at hk
    refine sum_mul_conj_eq_zero_symm B₀ _ _ ?_
    exact sum_mul_conj_comb B₀ (fun χ => χres χ y) (fun χ => v χ k 0) (fun χ => v χ k 1)
      (fun χ => Z χ k) 1 (-2)
      (fun χ _ => by simp only [Z, v', Matrix.cons_val_zero, Matrix.cons_val_one]; ring)
      (hWv y hy k hk 0) (hWv y hy k hk 1)
  have hWW : ∀ y ∈ Pg, ∀ y' ∈ Pg, ∑ χ ∈ B₀, χres χ y * conj (χres χ y') =
      if ∃ k, h6 k y = y' then ((4 : ℕ) : ℂ) ^ 2 else 0 := by
    intro y hy y' _
    rw [generic_column_generic hA hn basis ideal principal hprincipal (hPne y hy) y']
    by_cases hcj : IsConj (y : G) (y' : G)
    · rw [ite_eq_left hcj, ite_eq_left ((isConj_iff_exists_sixAut hA hn y y').mp hcj)]
      norm_num
    · rw [ite_eq_right hcj, ite_eq_right (mt (isConj_iff_exists_sixAut hA hn y y').mpr hcj)]
  have hgram := gram_of_normalized_columns hc hgen hσ hυ hint hζ lam hlam' h6 h6σ h6υ Pg hsplit
    hPmem hPinj B₀ Z χres hZZ hZW (fun y hy y' hy' => by convert hWW y hy y' hy' using 2) c
    hnorm
  have hnat : ∀ r s' χ, ∃ k : ℕ, tm r s' χ = k := fun r s' χ =>
    restriction_linear_pairing_nat basis (modelBase S e) (lam r s') χ
  have hcint : ∀ r s', ∀ χ ∈ B₀, ∃ k : ℤ, c r s' χ = k := by
    intro r s' χ hχ
    obtain ⟨k0, hk0⟩ := hnat 0 0 χ
    obtain ⟨k1, hk1⟩ := hnat r s' χ
    obtain ⟨f1, hf1⟩ := hfZ χ hχ (-r - s') 1
    obtain ⟨f2, hf2⟩ := hfZ χ hχ r 1
    obtain ⟨f3, hf3⟩ := hfZ χ hχ s' 1
    refine ⟨k0 - k1 + f1 + f2 + f3, ?_⟩
    have e : c r s' χ = tm 0 0 χ - tm r s' χ + f χ (-r - s').val 1 + f χ r.val 1 +
        f χ s'.val 1 := rfl
    rw [e, hk0, hk1, hf1, hf2, hf3]
    push_cast
    ring
  have hcreal : ∀ r s', ∀ χ ∈ B₀, conj (c r s' χ) = c r s' χ := by
    intro r s' χ hχ
    obtain ⟨k, hk⟩ := hcint r s' χ hχ
    rw [hk, map_intCast]
  have hcsym : ∀ r s' χ, c r s' χ = c s' r χ ∧ c r s' χ = c s' (-r - s') χ := by
    intro r s' χ
    rw [hcbase, hcbase, hcbase]
    exact baseColumn_symm hc hgen hζ lam hlam' h6 h6σ h6υ (χres χ) (hχconj χ) (v' χ) 1 r s'
  have hsw : ∀ r s' χ, c r s' χ = c s' r χ := fun r s' χ => (hcsym r s' χ).1
  have hrot : ∀ r s' χ, c r s' χ = c s' (-r - s') χ := fun r s' χ => (hcsym r s' χ).2
  have hc00 : ∀ χ, c 0 0 χ = 0 := fun χ => by
    rw [hcbase]
    exact baseColumn_zero lam (χres χ) (v' χ) 1
  have hprin1 : ∀ j : ZMod 4, zmodFourier i (fun k => v' principal k 1) j = 0 := by
    intro j
    have e : zmodFourier i (fun k => v' principal k 1) j = h j principal := by
      simp only [zmodFourier, fourierTransform, h, f, v', hIcc, Matrix.cons_val_one,
        Matrix.cons_val_zero, Nat.cast_ofNat]
      ring
    rw [e]
    rcases hcases j with h0 | hj
    · show f principal j.val 1 = 0
      rw [h0, hf0]
    · exact (hfprin' j.val hj).2
  have hχres1 : χres principal = fun _ => 1 := by
    funext y
    simp only [χres, X, hprincipal, Pi.one_apply]
  have hcprin : ∀ r s', (r, s') ≠ (0, 0) → c r s' principal = 1 := by
    intro r s' hrs
    rw [hcbase, hχres1]
    exact baseColumn_principal hc hgen hζ lam hlam' (v' principal) 1 hprin1 hrs
  have hlamc : ∀ (r s' : ZMod 4) y, conj (lam r s' y) = lam (-r) (-s') y := by
    intro r s' y
    have h1 := conj_lam_mul_lam hc hgen hζ lam hlam' r s' 0 0 y
    rw [lam_zero hc hgen lam hlam' y, mul_one, zero_sub, zero_sub] at h1
    exact h1
  have hconjc : ∀ χ ∈ B₀, ∀ ψ : basis.index, (∀ g', X ψ g' = conj (X χ g')) →
      ∀ r s', c r s' ψ = c (-r) (-s') χ := by
    intro χ hχ ψ hψ
    have htm : ∀ r s', tm r s' ψ = tm (-r) (-s') χ := by
      intro r s'
      obtain ⟨k, hk⟩ := hnat (-r) (-s') χ
      have e : tm r s' ψ = conj (tm (-r) (-s') χ) := by
        simp only [tm, map_mul, map_inv₀, map_natCast, map_sum, hψ, hlamc, neg_neg]
      rw [e, hk, map_natCast]
    have hhc : ∀ j : ZMod 4, h j ψ = h (-j) χ := by
      intro j
      show f ψ j.val 1 = f χ (-j).val 1
      rcases hcases j with h0 | hj
      · rw [h0, hf0, hnegval0 j h0, hf0]
      · rw [hconjf' χ hχ ψ hψ j.val hj 1, hnegval j hj]
    intro r s'
    show tm 0 0 ψ - tm r s' ψ + h (-r - s') ψ + h r ψ + h s' ψ =
      tm 0 0 χ - tm (-r) (-s') χ + h (-(-r) - -s') χ + h (-r) χ + h (-s') χ
    rw [htm, htm, hhc, hhc, hhc, neg_zero, show -(-r - s') = -(-r) - -s' by ring]
  have hcorth : ∀ r s' (T' : basis.index → ℂ),
      (∀ j ∈ Finset.Icc 1 3, ∑ χ ∈ B₀, gg j χ * conj (T' χ) = 0) →
      (∀ y ∈ Pg, ∑ χ ∈ B₀, χres χ y * conj (T' χ) = 0) →
      ∑ χ ∈ B₀, c r s' χ * conj (T' χ) = 0 := by
    intro r s' T' hg hW
    refine column_orthogonal B₀ Pg Z χres (c r s') _ _ (hnorm r s') T' (fun k hk => ?_) hW
    rw [← hIcc] at hk
    exact sum_comb_mul_conj_eq_zero B₀ (Finset.Icc 1 3) (fun χ => Z χ k) T' gg _
      (fun χ hχ => hZexp χ hχ k hk) hg
  have hdreal : ∀ χ, conj (d χ) = d χ := fun χ => by
    show conj ((basis.representation χ).character 1) = (basis.representation χ).character 1
    rw [finite_character_conjugate_inverse, inv_one]
  have horth_d : ∀ r s', ∑ χ ∈ B₀, c r s' χ * d χ = 0 := by
    intro r s'
    have h1 := hcorth r s' d (fun j _ => by
        rw [Finset.sum_congr rfl fun χ _ => by rw [hdreal χ]]
        have e : ∀ χ, gg j χ * d χ = d χ * f χ j 0 - 2 * (d χ * f χ j 1) := fun χ => by
          simp only [gg]
          ring
        rw [Finset.sum_congr rfl fun χ _ => e χ, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hfdeg' j 0, hfdeg' j 1]
        ring)
      (fun y hy => generic_column_odd_order hA hn basis ideal principal hprincipal (hPne y hy)
        (by rw [orderOf_one]; exact odd_one))
    rw [← h1]
    exact Finset.sum_congr rfl fun χ _ => by rw [hdreal χ]
  have horth_L : ∀ r s' (j' : ZMod 4), ∑ χ ∈ B₀, c r s' χ * L j' χ = 0 := by
    intro r s' j'
    rcases hcases j' with h0 | hj'
    · refine Finset.sum_eq_zero fun χ _ => ?_
      show c r s' χ * f χ j'.val 0 = 0
      rw [h0, hf0, mul_zero]
    have hLreal : ∀ χ ∈ B₀, conj (L j' χ) = L j' χ := fun χ hχ => hfreal χ hχ j' 0
    have h1 := hcorth r s' (L j') (fun j hj => by
        rw [Finset.sum_congr rfl fun χ hχ => by rw [hLreal χ hχ]]
        have e : ∀ χ, gg j χ * L j' χ =
            f χ j 0 * f χ j'.val 0 - 2 * (f χ j 1 * f χ j'.val 0) := fun χ => by
          simp only [gg, L]
          ring
        rw [Finset.sum_congr rfl fun χ _ => e χ, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hfgram00 j hj j'.val hj', hfgram10 j hj j'.val hj']
        ring)
      (fun y hy => sum_mul_conj_sum_eq_zero B₀ (Finset.Icc 1 3) (fun χ => χres χ y)
        (fun n' χ => v χ n' 0) (1 / 4) (fun n' => i ^ (j'.val * n') - 1)
        (fun n' hn' => hWv y hy n' hn' 0))
    rw [← h1]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hLreal χ hχ]
  have hPW : ∀ y ∈ Pg, ∑ χ ∈ B₀, χres χ y * ((X χ ρ).re : ℂ) = 0 ∧
      ∑ χ ∈ B₀, χres χ y * ((imCoeff i (X χ ρ) : ℝ) : ℂ) = 0 := by
    intro y hy
    refine FourPointRemainingOrderFour.sum_mul_re_imCoeff_eq_zero B₀ (fun χ => χres χ y)
      (fun χ => X χ ρ) i ?_ ?_
    · have h1 := generic_column_odd_power hA hn basis ideal principal hprincipal (hPne y hy)
        hρord' (t := -1) odd_one.neg
      simp only [zpow_neg_one, finite_character_conjugate_inverse, inv_inv] at h1
      exact h1
    · have h1 := generic_column_odd_power hA hn basis ideal principal hprincipal (hPne y hy)
        hρord' (t := 1) odd_one
      simp only [zpow_one] at h1
      exact h1
  have horth_P : ∀ r s', ∑ χ ∈ B₀, c r s' χ * (P χ : ℂ) = 0 := by
    intro r s'
    have h1 := hcorth r s' (fun χ => (P χ : ℂ)) (fun j hj => by
        simp only [Complex.conj_ofReal]
        have e : ∀ χ, gg j χ * (P χ : ℂ) = (P χ : ℂ) * f χ j 0 - 2 * ((P χ : ℂ) * f χ j 1) :=
          fun χ => by
            simp only [gg]
            ring
        rw [Finset.sum_congr rfl fun χ _ => e χ, Finset.sum_sub_distrib, ← Finset.mul_sum,
          (hPQf' j hj 0).1, (hPQf' j hj 1).1]
        ring)
      (fun y hy => by simp only [Complex.conj_ofReal]; exact (hPW y hy).1)
    rw [← h1]
    simp only [Complex.conj_ofReal]
  have horth_Q : ∀ r s', ∑ χ ∈ B₀, c r s' χ * (Q χ : ℂ) = 0 := by
    intro r s'
    have h1 := hcorth r s' (fun χ => (Q χ : ℂ)) (fun j hj => by
        simp only [Complex.conj_ofReal]
        have e : ∀ χ, gg j χ * (Q χ : ℂ) = (Q χ : ℂ) * f χ j 0 - 2 * ((Q χ : ℂ) * f χ j 1) :=
          fun χ => by
            simp only [gg]
            ring
        rw [Finset.sum_congr rfl fun χ _ => e χ, Finset.sum_sub_distrib, ← Finset.mul_sum,
          (hPQf' j hj 0).2, (hPQf' j hj 1).2]
        ring)
      (fun y hy => by simp only [Complex.conj_ofReal]; exact (hPW y hy).2)
    rw [← h1]
    simp only [Complex.conj_ofReal]
  have hrow : ∀ χ ∈ B₀, ∀ j : ZMod 4,
      L j χ - 2 * h j χ = (∑ r : ZMod 4, c r (0 - r) χ) - ∑ r : ZMod 4, c r (-j - r) χ := by
    intro χ hχ j
    have hid := second_row_identity hc hgen hσ hυ hint hζ hlam' (χres χ) (v' χ) 1 (hval χ hχ) j
    simp only [baseColumnSum, ← hcbase] at hid
    have e0 : zmodFourier i (fun k => v' χ k 0) j = L j χ - 4 * h j χ := by
      simp only [zmodFourier, fourierTransform, L, h, f, v', hIcc, Matrix.cons_val_zero,
        Nat.cast_ofNat, sum_Ico_one_four]
      ring
    have e1 : zmodFourier i (fun k => v' χ k 1) j = h j χ := by
      simp only [zmodFourier, fourierTransform, h, f, v', hIcc, Matrix.cons_val_one,
        Matrix.cons_val_zero, Nat.cast_ofNat]
      ring
    rw [← hid, e0, e1]
    ring
  have hid3 : ∀ χ ∈ B₀, L 1 χ - 2 * h 1 χ = c 2 2 χ - 2 * c 1 1 χ ∧
      L 3 χ - 2 * h 3 χ = c 2 2 χ - 2 * c 3 3 χ ∧
      L 2 χ - 2 * h 2 χ = 2 * c 1 0 χ - c 2 2 χ - c 1 1 χ - c 3 3 χ := by
    intro χ hχ
    obtain ⟨C0, C1, C2, C3⟩ := antidiagonal_sums c hsw hrot hc00 χ
    refine ⟨?_, ?_, ?_⟩
    · rw [hrow χ hχ 1, show (-1 : ZMod 4) = 3 by decide, C0, C3]
      ring
    · rw [hrow χ hχ 3, show (-3 : ZMod 4) = 1 by decide, C0, C1]
      ring
    · rw [hrow χ hχ 2, show (-2 : ZMod 4) = 2 by decide, C0, C2]
      ring
  let idx : Fin 4 → ZMod 4 × ZMod 4 := ![(1, 1), (2, 2), (3, 3), (1, 0)]
  have hcolidx : ∀ l : Fin 4, col l = c (idx l).1 (idx l).2 := by
    intro l
    fin_cases l <;> rfl
  have hidx : ∀ l : Fin 4, idx l ≠ 0 := by
    have h1 : ∀ l : Fin 4, (![(1, 1), (2, 2), (3, 3), (1, 0)] : Fin 4 → ZMod 4 × ZMod 4) l ≠ 0 := by
      decide
    exact h1
  refine ⟨hnat, fun j χ hχ => ⟨hfZ χ hχ j 0, hfZ χ hχ j 1⟩, hcint, orbit_constant c hsw hrot,
    hc00, ?_, ?_, ?_, ?_, hid3, ?_, ?_⟩
  ·
    intro l
    rw [hcolidx l]
    exact hcprin _ _ (hidx l)
  ·
    intro χ hχ ψ hψ
    have hcc := hconjc χ hχ ψ hψ
    obtain ⟨-, -, -, -, -, -, -, -, e30, -, -⟩ := orbit_values c hsw hrot χ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcc, show (-1 : ZMod 4) = 3 by decide]
    · rw [hcc, show (-3 : ZMod 4) = 1 by decide]
    · rw [hcc, show (-2 : ZMod 4) = 2 by decide]
    · rw [hcc, show (-1 : ZMod 4) = 3 by decide, neg_zero, e30]
  ·
    intro l
    rw [hcolidx l]
    exact ⟨horth_d _ _, horth_L _ _, horth_P _ _, horth_Q _ _⟩
  ·
    intro l l'
    rw [hcolidx l, hcolidx l']
    have h1 := hgram (idx l) (idx l') (hidx l) (hidx l')
    have h2 := dualSix_counts l l'
    rw [Finset.sum_congr rfl fun χ hχ => by rw [← hcreal (idx l').1 (idx l').2 χ hχ], h1]
    exact_mod_cast h2
  ·
    intro χ hχ
    obtain ⟨e1, -, e2⟩ := hid3 χ hχ
    obtain ⟨k11, hk11⟩ := hcint 1 1 χ hχ
    obtain ⟨k33, hk33⟩ := hcint 3 3 χ hχ
    obtain ⟨k22, hk22⟩ := hcint 2 2 χ hχ
    obtain ⟨k10, hk10⟩ := hcint 1 0 χ hχ
    obtain ⟨l1, hl1⟩ := hfint' χ hχ 1 (by decide) 0
    obtain ⟨l2, hl2⟩ := hfint' χ hχ 2 (by decide) 0
    obtain ⟨m1, hm1⟩ := hfint' χ hχ 1 (by decide) 1
    obtain ⟨m2, hm2⟩ := hfint' χ hχ 2 (by decide) 1
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hPQint' χ hχ
    obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ := hpar' χ hχ
    have hL1 : L 1 χ = l1 := hl1
    have hL2 : L 2 χ = l2 := hl2
    have hh1 : h 1 χ = m1 := hm1
    have hh2 : h 2 χ = m2 := hm2
    rw [hL1, hh1, hk22, hk11] at e1
    rw [hL2, hh2, hk10, hk22, hk11, hk33] at e2
    have e1z : l1 - 2 * m1 = k22 - 2 * k11 := by exact_mod_cast e1
    have e2z : l2 - 2 * m2 = 2 * k10 - k22 - k11 - k33 := by exact_mod_cast e2
    have p1z : l1 = p + 2 * k₁ := by
      rw [hl1, hp] at hk₁
      exact_mod_cast hk₁
    have p2z : l2 = p + q + 2 * k₂ := by
      rw [hl2, hp, hq] at hk₂
      exact_mod_cast hk₂
    refine ⟨⟨k11 - m1, ?_⟩, ⟨k₁, hk₁⟩, ⟨k10 - k₁ - k11 + m1 - k₂ + m2 - p - q, ?_⟩⟩
    · rw [hk22, hL1]
      have h3 : k22 = l1 + 2 * (k11 - m1) := by linear_combination -e1z
      exact_mod_cast h3
    · rw [hk11, hk33, hq]
      have h3 : k11 + k33 = q + 2 * (k10 - k₁ - k11 + m1 - k₂ + m2 - p - q) := by
        linear_combination e2z + e1z - p1z - p2z
      exact_mod_cast h3
  ·
    intro χ hχ
    obtain ⟨e1, e3, e2⟩ := hid3 χ hχ
    obtain ⟨k11, hk11⟩ := hcint 1 1 χ hχ
    obtain ⟨k33, hk33⟩ := hcint 3 3 χ hχ
    obtain ⟨k22, hk22⟩ := hcint 2 2 χ hχ
    obtain ⟨k10, hk10⟩ := hcint 1 0 χ hχ
    obtain ⟨l1, hl1⟩ := hfint' χ hχ 1 (by decide) 0
    obtain ⟨l2, hl2⟩ := hfint' χ hχ 2 (by decide) 0
    obtain ⟨l3, hl3⟩ := hfint' χ hχ 3 (by decide) 0
    obtain ⟨m1, hm1⟩ := hfint' χ hχ 1 (by decide) 1
    obtain ⟨m2, hm2⟩ := hfint' χ hχ 2 (by decide) 1
    obtain ⟨m3, hm3⟩ := hfint' χ hχ 3 (by decide) 1
    have hL1 : L 1 χ = l1 := hl1
    have hL2 : L 2 χ = l2 := hl2
    have hL3 : L 3 χ = l3 := hl3
    have hh1 : h 1 χ = m1 := hm1
    have hh2 : h 2 χ = m2 := hm2
    have hh3 : h 3 χ = m3 := hm3
    rw [hL1, hh1, hk22, hk11] at e1
    rw [hL3, hh3, hk22, hk33] at e3
    rw [hL2, hh2, hk10, hk22, hk11, hk33] at e2
    have e1z : l1 - 2 * m1 = k22 - 2 * k11 := by exact_mod_cast e1
    have e3z : l3 - 2 * m3 = k22 - 2 * k33 := by exact_mod_cast e3
    have e2z : l2 - 2 * m2 = 2 * k10 - k22 - k11 - k33 := by exact_mod_cast e2
    have hv10 : v χ 1 0 = -(l2 : ℂ) + i * ((l3 : ℂ) - l1) := by
      rw [hinv' χ hχ 1 (by decide) 0, ← hl1, ← hl2, ← hl3]
      linear_combination inverse_one hi (fun j => f χ j 0)
    have hv11 : v χ 1 1 = -(m2 : ℂ) + i * ((m3 : ℂ) - m1) := by
      rw [hinv' χ hχ 1 (by decide) 1, ← hm1, ← hm2, ← hm3]
      linear_combination inverse_one hi (fun j => f χ j 1)
    have hv20 : v χ 2 0 = -(l1 : ℂ) + l2 - l3 := by
      rw [hinv' χ hχ 2 (by decide) 0, ← hl1, ← hl2, ← hl3]
      linear_combination inverse_two hi (fun j => f χ j 0)
    have hv21 : v χ 2 1 = -(m1 : ℂ) + m2 - m3 := by
      rw [hinv' χ hχ 2 (by decide) 1, ← hm1, ← hm2, ← hm3]
      linear_combination inverse_two hi (fun j => f χ j 1)
    have hT : T χ = v χ 1 0 + 2 * v χ 1 1 := by
      show T χ = (T χ + 2 * Ua χ) / 3 + 2 * ((T χ - Ua χ) / 3)
      ring
    have hU : Ua χ = v χ 1 0 - v χ 1 1 := by
      show Ua χ = (T χ + 2 * Ua χ) / 3 - (T χ - Ua χ) / 3
      ring
    have hA' : Ax χ = v χ 2 0 + 2 * v χ 2 1 := by
      show Ax χ = (Ax χ + 2 * Bx χ) / 3 + 2 * ((Ax χ - Bx χ) / 3)
      ring
    have hB' : Bx χ = v χ 2 0 - v χ 2 1 := by
      show Bx χ = (Ax χ + 2 * Bx χ) / 3 - (Ax χ - Bx χ) / 3
      ring
    obtain ⟨r1, r2, r3, r4, r5⟩ := base_value_formulas hi l1 l2 l3 m1 m2 m3 k11 k22 k33 k10
      (v χ 1 0) (v χ 1 1) (v χ 2 0) (v χ 2 1) (T χ) (Ua χ) (Ax χ) (Bx χ) hv10 hv11 hv20 hv21
      hT hU hA' hB' e1z e3z e2z
    rw [hk11, hk33, hL1, hL2, hL3, hk10, hk22]
    exact ⟨r1, r2, r3, r4, r5⟩

end CFSG.Wreathed.FourPointBaseMultiplicity

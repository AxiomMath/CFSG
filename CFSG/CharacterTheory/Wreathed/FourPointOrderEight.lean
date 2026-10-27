module

public import CFSG.CharacterTheory.Wreathed.FourPointOrderEightColumns
public import CFSG.CharacterTheory.Wreathed.FourPointCentralFourier
public import CFSG.CharacterTheory.Wreathed.FourPointOrderEightSupport

public noncomputable section

namespace CFSG.Wreathed.FourPointOrderEight

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.FourPointOrderFour
  CFSG.Wreathed.FourPointGaussianColumns CFSG.Wreathed.FourPointCentralFourier
  CFSG.Wreathed.WreathCentralSquare

open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_order_eight_centralizer_and_norm_four_columns
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let H := centralizerOddCoreQuotient n S e
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let π := centralizerOddCoreMap n S e
    let aN : N := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))
    let s : G := wreathModelHom S e (Original.s (2 ^ n))
    let w : G := wreathModelHom S e (Original.z (2 ^ n))
    let a : G := wreathModelHom S e (Original.a (2 ^ n))
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let C := orderFourCentralizer n S e
    let ρ : G := s * w
    let D : Subgroup G := Subgroup.centralizer {ρ}
    let Rρ : Subgroup G := R.map N.subtype ⊓ D
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let u := cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let iF := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let U₀ : W := iF (CentralSL2.upperSL (ZMod 3) 1)
    n = 2 ∧ (∃ Φ : W ≃* H, Φ (u ^ 2) = π aN) ∧
    orderOf ρ = 8 ∧ ρ ^ 2 = a ∧ ρ ^ 4 = x ∧
    s ^ 2 ∈ (S : Subgroup G) ∧ (s ^ 2)⁻¹ * ρ * s ^ 2 = ρ ^ 5 ∧
    (∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = Subgroup.zpowers ρ) ∧
    Rρ.subgroupOf D = CFSG.oddCore D ∧ (Rρ.subgroupOf D).Normal ∧ Odd (Nat.card Rρ) ∧
    (Rρ : Set G) * (Subgroup.zpowers ρ : Set G) = D ∧ Rρ ⊓ Subgroup.zpowers ρ = ⊥ ∧
    Nat.card D = 8 * Nat.card Rρ ∧ ¬ IsConj ρ ρ⁻¹ ∧
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
          (∀ χ ∈ B₀, (∃ k : ℤ, P χ = k) ∧ ∃ k : ℤ, Q χ = k) ∧
          (∀ χ ∈ B₀, ∀ r ∈ D, Odd (orderOf r) →
            X χ (ρ * r) = X χ ρ ∧ X χ ρ = P χ + i * Q χ) ∧
          ∑ χ ∈ B₀, P χ ^ 2 = 4 ∧ ∑ χ ∈ B₀, Q χ ^ 2 = 4 ∧ ∑ χ ∈ B₀, P χ * Q χ = 0 ∧
          ∑ χ ∈ B₀, d χ * P χ = 0 ∧ ∑ χ ∈ B₀, d χ * Q χ = 0 ∧
          P principal = 1 ∧ Q principal = 0 ∧
          (∀ j ∈ Finset.Icc 1 3, ∀ ℓ,
            ∑ χ ∈ B₀, P χ * f χ j ℓ = 0 ∧ ∑ χ ∈ B₀, Q χ * f χ j ℓ = 0) ∧
          (B₀.filter (fun χ => P χ ≠ 0)).card = 4 ∧
          (∀ χ ∈ B₀, P χ ≠ 0 → P χ = 1 ∨ P χ = -1) ∧
          (B₀.filter (fun χ => Q χ ≠ 0)).card = 4 ∧
          (∀ χ ∈ B₀, Q χ ≠ 0 → Q χ = 1 ∨ Q χ = -1) ∧
          (∃ χ₁ ψ₁ χ₂ ψ₂ : basis.index,
            (∀ g, X ψ₁ g = starRingEnd ℂ (X χ₁ g)) ∧ (∀ g, X ψ₂ g = starRingEnd ℂ (X χ₂ g)) ∧
            χ₁ ≠ ψ₁ ∧ χ₁ ≠ χ₂ ∧ χ₁ ≠ ψ₂ ∧ ψ₁ ≠ χ₂ ∧ ψ₁ ≠ ψ₂ ∧ χ₂ ≠ ψ₂ ∧
            B₀.filter (fun χ => Q χ ≠ 0) = {χ₁, ψ₁, χ₂, ψ₂}) ∧
          principal ∈ B₀.filter (fun χ => P χ ≠ 0) ∧
          ∀ χ ∈ B₀, P χ ≠ 0 → ∀ ψ : basis.index, (∀ g, X ψ g = starRingEnd ℂ (X χ g)) →
            ψ ∈ B₀ ∧ P ψ ≠ 0 := by
  intro H N R π aN s w a x C ρ D Rρ W u iF U₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  subst hn2
  obtain ⟨-, hΦex, hG⟩ :=
    four_point_central_section_integral_fourier_columns hnonab 2 hn S e alpha
  have hρ : ρ = actualRoot S e := (actualRoot_eq S e).symm
  obtain ⟨hsyl, hsub, hnormal, hodd, hprod, hinf, hcard⟩ :=
    rootCentralizer_structure 2 hn S e alpha ρ hρ
  obtain ⟨hs2, hconj5⟩ := root_conj_s_sq S e
  refine ⟨rfl, hΦex, ?_, ?_, ?_, hs2, ?_, hsyl, hsub, hnormal, hodd, hprod, hinf, hcard, ?_, ?_⟩
  · rw [hρ, actualRoot_orderOf 2 hn S e]
    norm_num
  · rw [hρ]
    exact actualRoot_sq S e
  · rw [hρ]
    exact actualRoot_pow_modulus 2 (by norm_num) S e
  · rw [hρ]
    exact hconj5
  · rw [hρ]
    exact root_not_isConj_inv S e
  intro Φ hΦ
  refine ⟨(hG Φ hΦ).1, ?_⟩
  intro z hzC hzodd _ ideal _ _ basis principal hprincipal i hi B₀ X d Ax Bx T Ua v f P Q
  have hi0 : i.re = 0 := (re_eq_zero_and_im_sq_eq_one hi).1
  have hconji : starRingEnd ℂ i = -i := by
    apply Complex.ext <;> simp [hi0]
  have hpr : principal ∈ B₀ := coefficientBlock_self_mem basis _ principal
  obtain ⟨c₀, c₁, hsec, hval, h00, h11, h01, hd0, hd1, hp0, hp1, hcard0, hunit0, hcard1,
    hunit1⟩ := root_signed_columns S e basis ideal principal hprincipal hi ρ hρ
  have hval' : ∀ χ ∈ B₀, X χ ρ = c₀ χ + c₁ χ * i := hval
  have hd0' : ∑ χ ∈ B₀, (c₀ χ : ℂ) * d χ = 0 := hd0
  have hd1' : ∑ χ ∈ B₀, (c₁ χ : ℂ) * d χ = 0 := hd1
  have hPc : ∀ χ ∈ B₀, P χ = c₀ χ := fun χ hχ => by
    change (X χ ρ).re = _
    rw [hval' χ hχ]
    simp [hi0]
  have hQc : ∀ χ ∈ B₀, Q χ = c₁ χ := fun χ hχ => by
    change imCoeff i (X χ ρ) = _
    rw [hval' χ hχ, ← Complex.ofReal_intCast, ← Complex.ofReal_intCast, imCoeff_add_mul hi]
  have hvalinv : ∀ χ ∈ B₀, X χ ρ⁻¹ = c₀ χ - c₁ χ * i := fun χ hχ => by
    change (basis.representation χ).character ρ⁻¹ = _
    rw [← finite_character_conjugate_inverse, hval χ hχ, map_add, map_mul, hconji, map_intCast,
      map_intCast]
    ring
  have hza : (z : G) * a = a * z := Subgroup.mem_centralizer_singleton_iff.mp hzC
  have hzodd' : Odd (orderOf (z : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hzodd
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := root_orthogonal_central_columns S e basis ideal principal
    hprincipal (z : G) hza hzodd' odd_one ρ (by rw [zpow_one, hρ])
  obtain ⟨o1', o2', o3', o4', o5', o6'⟩ := root_orthogonal_central_columns S e basis ideal
    principal hprincipal (z : G) hza hzodd' (h := -1) ⟨-1, by norm_num⟩ ρ⁻¹
    (by rw [zpow_neg_one, hρ])
  have hcols : ∀ g : basis.index → ℂ, ∑ χ ∈ B₀, X χ ρ * g χ = 0 →
      ∑ χ ∈ B₀, X χ ρ⁻¹ * g χ = 0 →
        ∑ χ ∈ B₀, (c₀ χ : ℂ) * g χ = 0 ∧ ∑ χ ∈ B₀, (c₁ χ : ℂ) * g χ = 0 :=
    fun g h₁ h₂ => sum_coeff_eq_zero B₀ hi (fun χ => X χ ρ) (fun χ => X χ ρ⁻¹) g c₀ c₁ hval'
      hvalinv h₁ h₂
  have qT := hcols T o1 o1'
  have qU := hcols Ua o2 o2'
  have qA := hcols Ax o3 o3'
  have qB := hcols Bx o4 o4'
  have qcT := hcols (fun χ => starRingEnd ℂ (T χ)) o5 o5'
  have qcU := hcols (fun χ => starRingEnd ℂ (Ua χ)) o6 o6'
  have hf0 : ∀ j ℓ, ∑ χ ∈ B₀, (c₀ χ : ℂ) * f χ j ℓ = 0 := fun j ℓ =>
    sum_mul_fourier_eq_zero B₀ (fun χ => (c₀ χ : ℂ)) T Ua Ax Bx i v (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) qT.1 qU.1 qA.1 qB.1 qcT.1 qcU.1 j ℓ
  have hf1 : ∀ j ℓ, ∑ χ ∈ B₀, (c₁ χ : ℂ) * f χ j ℓ = 0 := fun j ℓ =>
    sum_mul_fourier_eq_zero B₀ (fun χ => (c₁ χ : ℂ)) T Ua Ax Bx i v (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) qT.2 qU.2 qA.2 qB.2 qcT.2 qcU.2 j ℓ
  have hPσ : ∀ χ, P (conjLabel basis χ) = P χ := fun χ => by
    change (X (conjLabel basis χ) ρ).re = (X χ ρ).re
    rw [show X (conjLabel basis χ) ρ = starRingEnd ℂ (X χ ρ) from conjLabel_spec basis χ ρ,
      Complex.conj_re]
  have hQσ : ∀ χ, Q (conjLabel basis χ) = -Q χ := fun χ => by
    change imCoeff i (X (conjLabel basis χ) ρ) = -imCoeff i (X χ ρ)
    rw [show X (conjLabel basis χ) ρ = starRingEnd ℂ (X χ ρ) from conjLabel_spec basis χ ρ,
      imCoeff_conj]
  have hfilterP : B₀.filter (fun χ => P χ ≠ 0) = B₀.filter (fun χ => c₀ χ ≠ 0) :=
    Finset.filter_congr fun χ hχ => by rw [hPc χ hχ, Int.cast_ne_zero]
  have hfilterQ : B₀.filter (fun χ => Q χ ≠ 0) = B₀.filter (fun χ => c₁ χ ≠ 0) :=
    Finset.filter_congr fun χ hχ => by rw [hQc χ hχ, Int.cast_ne_zero]
  have hPp : P principal = 1 := by
    rw [hPc principal hpr, hp0, Int.cast_one]
  refine ⟨fun χ hχ => ⟨⟨c₀ χ, hPc χ hχ⟩, ⟨c₁ χ, hQc χ hχ⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, hPp, ?_, ?_,
    by rw [hfilterP]; exact hcard0, ?_, by rw [hfilterQ]; exact hcard1, ?_, ?_,
    Finset.mem_filter.mpr ⟨hpr, by rw [hPp]; norm_num⟩, ?_⟩
  ·
    intro χ hχ r hr hrodd
    refine ⟨hsec χ hχ r hr hrodd, ?_⟩
    rw [hPc χ hχ, hQc χ hχ, Complex.ofReal_intCast, Complex.ofReal_intCast, hval' χ hχ]
    ring
  ·
    calc ∑ χ ∈ B₀, P χ ^ 2 = ((∑ χ ∈ B₀, c₀ χ * c₀ χ : ℤ) : ℝ) := by
          push_cast
          exact Finset.sum_congr rfl fun χ hχ => by rw [hPc χ hχ, sq]
      _ = 4 := by rw [h00]; norm_num
  ·
    calc ∑ χ ∈ B₀, Q χ ^ 2 = ((∑ χ ∈ B₀, c₁ χ * c₁ χ : ℤ) : ℝ) := by
          push_cast
          exact Finset.sum_congr rfl fun χ hχ => by rw [hQc χ hχ, sq]
      _ = 4 := by rw [h11]; norm_num
  ·
    calc ∑ χ ∈ B₀, P χ * Q χ = ((∑ χ ∈ B₀, c₀ χ * c₁ χ : ℤ) : ℝ) := by
          push_cast
          exact Finset.sum_congr rfl fun χ hχ => by rw [hPc χ hχ, hQc χ hχ]
      _ = 0 := by rw [h01]; norm_num
  ·
    rw [← hd0']
    exact Finset.sum_congr rfl fun χ hχ => by rw [hPc χ hχ, Complex.ofReal_intCast, mul_comm]
  ·
    rw [← hd1']
    exact Finset.sum_congr rfl fun χ hχ => by rw [hQc χ hχ, Complex.ofReal_intCast, mul_comm]
  ·
    rw [hQc principal hpr, hp1, Int.cast_zero]
  ·
    intro j _ ℓ
    constructor
    · rw [Finset.sum_congr rfl fun χ hχ => by rw [hPc χ hχ, Complex.ofReal_intCast]]
      exact hf0 j ℓ
    · rw [Finset.sum_congr rfl fun χ hχ => by rw [hQc χ hχ, Complex.ofReal_intCast]]
      exact hf1 j ℓ
  ·
    intro χ hχ hne
    rw [hPc χ hχ] at hne ⊢
    rcases hunit0 χ hχ with h | h | h
    · rw [h, Int.cast_zero] at hne
      exact absurd rfl hne
    · left
      rw [h, Int.cast_one]
    · right
      rw [h, Int.cast_neg, Int.cast_one]
  ·
    intro χ hχ hne
    rw [hQc χ hχ] at hne ⊢
    rcases hunit1 χ hχ with h | h | h
    · rw [h, Int.cast_zero] at hne
      exact absurd rfl hne
    · left
      rw [h, Int.cast_one]
    · right
      rw [h, Int.cast_neg, Int.cast_one]
  ·
    have hσT : ∀ χ ∈ B₀.filter (fun χ => Q χ ≠ 0),
        conjLabel basis χ ∈ B₀.filter (fun χ => Q χ ≠ 0) := by
      intro χ hχ
      rw [Finset.mem_filter] at hχ ⊢
      refine ⟨conjLabel_mem_coefficientBlock basis _ principal hprincipal χ hχ.1, ?_⟩
      rw [hQσ, neg_ne_zero]
      exact hχ.2
    have hσne : ∀ χ ∈ B₀.filter (fun χ => Q χ ≠ 0), conjLabel basis χ ≠ χ := by
      intro χ hχ h
      have hQ := hQσ χ
      rw [h] at hQ
      exact (Finset.mem_filter.mp hχ).2 (by linarith)
    obtain ⟨χ₁, -, χ₂, -, h1, h2, h3, h4, h5, h6, hT⟩ :=
      exists_two_pairs _ (by rw [hfilterQ]; exact hcard1) (conjLabel basis)
        (conjLabel_conjLabel basis) hσT hσne
    exact ⟨χ₁, conjLabel basis χ₁, χ₂, conjLabel basis χ₂, conjLabel_spec basis χ₁,
      conjLabel_spec basis χ₂, h1, h2, h3, h4, h5, h6, hT⟩
  ·
    intro χ hχ hne ψ hψ
    have hψeq : conjLabel basis χ = ψ := conjLabel_eq_of_spec basis χ ψ hψ
    refine ⟨hψeq ▸ conjLabel_mem_coefficientBlock basis _ principal hprincipal χ hχ, ?_⟩
    rw [← hψeq, hPσ]
    exact hne

end CFSG.Wreathed.FourPointOrderEight

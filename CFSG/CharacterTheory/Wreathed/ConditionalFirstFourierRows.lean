module

public import CFSG.CharacterTheory.Wreathed.ConditionalFirstFourierRowsCharacters
public import CFSG.CharacterTheory.Wreathed.ConditionalUniformOddFourier
public import CFSG.CharacterTheory.Wreathed.ConditionalFirstFourierRowsColumns

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalFirstFourierRows

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.ConditionalSquareRoot CFSG.Wreathed.ConditionalOddFourier
  CFSG.Wreathed.ConditionalUniformOddFourier

theorem conditional_odd_constituent_complete_first_fourier_rows_of_localHyp
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f)
    [Fintype (centralizerOddCoreQuotient n S e)]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
    ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      let m : ℕ := 2 ^ n
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      let J : Finset ℕ := (Finset.Ico 1 m).filter Odd
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ ξ : ℂ, IsPrimitiveRoot ξ (2 * m) → ξ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (ξ ^ t))
      let c : basis.index → ℕ → ℤ := fun χ r => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      let Y : ℕ → G → ℂ := fun r g =>
        ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character g
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let fc : basis.index → ℕ → ℂ := fun χ j => fourierTransform m ζ (fun k => v χ k 0) j
      let X : ℕ → G → ℂ := fun j => ∑ χ ∈ B₀, fc χ j • (basis.representation χ).character
      let constituents : (Fin 3 → basis.index) → (Fin 3 → ℤ) → (Fin 3 → ℤ) → ℤ →
          (ℕ → basis.index) → ℕ → Fin 3 → Prop := fun α β η σ χ δ e₀ =>
        Function.Injective α ∧ (∀ i, α i ∈ B₀ ∧ α i ≠ principal) ∧
        (∀ i, β i = 1 ∨ β i = -1) ∧ (∀ i, η i = 1 ∨ η i = -1) ∧ (σ = 1 ∨ σ = -1) ∧
        Set.InjOn χ J ∧ (∀ j ∈ J, χ j ∈ B₀ ∧ χ j ≠ principal ∧ ∀ i, χ j ≠ α i) ∧ 0 < δ ∧
        η e₀ = -β e₀ ∧ (∀ i, i ≠ e₀ → η i = β i) ∧ (∀ i, η i = -β i → i = e₀) ∧
        Y 0 = 1 + ∑ i, (β i : ℂ) • (basis.representation (α i)).character ∧
        (∀ j ∈ J, X j = -1 + ∑ i, (η i : ℂ) • (basis.representation (α i)).character +
          (2 * σ : ℂ) • (basis.representation (χ j)).character) ∧
        (∀ j ∈ J, (basis.representation (χ j)).character 1 = δ) ∧
        1 + ∑ i, (β i : ℂ) * (basis.representation (α i)).character 1 = 0 ∧
        (σ * δ : ℂ) = 1 + β e₀ * (basis.representation (α e₀)).character 1 ∧
        β e₀ = σ ∧ (δ : ℂ) = (basis.representation (α e₀)).character 1 + σ
      (∃ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
          (e₀ : Fin 3), constituents α β η σ χ δ e₀ ∧ (J.image χ).card = m / 2 ∧
            ∀ j ∈ J, fc (χ j) j = 2 * σ) ∧
      ∀ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
          (e₀ : Fin 3), constituents α β η σ χ δ e₀ →
        (∀ j ∈ J, ∀ t ∈ Finset.Ico 1 m, fc (χ j) t = if t = j then 2 * σ else 0) ∧
        (∀ t ∈ Finset.Ico 1 m, fc (α e₀) t = -σ) ∧
        (∀ j ∈ J, ∀ r < m / 2, c (χ j) r = 0) ∧ c (α e₀) 0 = σ ∧
        (∀ r, 0 < r → r < m / 2 → c (α e₀) r = 0) ∧
        ∀ h : ℤ, Odd h → ∀ z ∈ Subgroup.centralizer ({y} : Set G), Odd (orderOf z) →
          (∀ j ∈ J, (basis.representation (χ j)).character (y ^ h * z) = 0) ∧
          (basis.representation (α e₀)).character (y ^ h * z) = σ := by
  refine ⟨hloc.modelData, ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata m a y ΦH ΦN ε B₀ J ζ hζ ξ hξ hξζ ν c Y
  have hU := (conditional_uniform_odd_fourier_actual_equal_degree_constituent_family_of_localHyp n
    hn S e p f hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
    ζ hζ ξ hξ hξζ
  refine ⟨hU.1, fun v hv => ?_⟩
  intro fc X constituents
  refine ⟨?_, fun α β η σ χ δ e₀ hP => ?_⟩
  · obtain ⟨α, β, η, σ, χ, δ, e₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16, h17, h18, hcard, hfc⟩ := hU.2 v hv
    exact ⟨α, β, η, σ, χ, δ, e₀, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16, h17, h18⟩, hcard, hfc⟩
  obtain ⟨hinj, hα, hβ, -, hσ, hχinj, hχ, -, hηe, hηi, -, hY0, hXj, hdegχ, -, -, hβe, -⟩ := hP
  obtain ⟨-, -, -, -, -, -, -, hSR⟩ :=
    (conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp n hn S e p f hp
      hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨hsec, -, -, hcgram, hY1, -, hcr, hfourc, -, hall⟩ := hSR ζ hζ ξ hξ hξζ
  obtain ⟨Fc, hFc, horth, -, heven, -, hcard, -, -⟩ := hall v hv
  obtain ⟨v₀, -, -, huniq, -, -, -, -, hdeg, hprin, -, hsq, hgram⟩ :=
    (conditional_global_central_section_integral_fourier_columns_of_localHyp n hn S e p f hp hpodd
      hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata ζ hζ
  have hP0 : principal ∈ B₀ := coefficientBlock_self_mem basis _ principal
  let cc : ℕ → basis.index → ℤ := fun j χ => Fc χ j 0
  have hcc : ∀ j ∈ Finset.Ico 1 m, ∀ χ ∈ B₀, (cc j χ : ℂ) = fc χ j :=
    fun j hj χ hχ => hFc χ hχ j hj 0
  have hccF : ∀ j ∈ Finset.Ico 1 m, ∀ χ ∈ B₀,
      (cc j χ : ℂ) = fourierTransform m ζ (fun k => v₀ χ k 0) j := by
    intro j hj χ hχ
    rw [hcc j hj χ hχ]
    refine fourierTransform_congr (fun k hk => ?_) j
    rw [huniq χ hχ k hk (v χ k) fun r hr hodd => hv χ hχ k hk r hr hodd]
  have hgramZ : ∀ j ∈ Finset.Ico 1 m, ∀ t ∈ Finset.Ico 1 m,
      ∑ χ ∈ B₀, cc j χ * cc t χ = if j = t then 8 else 4 := by
    intro j hj t ht
    have key : ((∑ χ ∈ B₀, cc j χ * cc t χ : ℤ) : ℂ) = ∑ χ ∈ B₀,
        fourierTransform m ζ (fun k => v₀ χ k 0) j *
          fourierTransform m ζ (fun k => v₀ χ k 0) t := by
      push_cast
      exact Finset.sum_congr rfl fun χ hχ => by rw [hccF j hj χ hχ, hccF t ht χ hχ]
    by_cases hjt : j = t
    · subst hjt
      rw [ite_eq_left rfl]
      have h : ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j ^ 2 = 8 := hsq j hj
      rw [show ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j ^ 2 =
        ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j *
          fourierTransform m ζ (fun k => v₀ χ k 0) j from
        Finset.sum_congr rfl fun _ _ => sq _, ← key] at h
      exact_mod_cast h
    · rw [ite_eq_right hjt]
      have h : ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j *
          fourierTransform m ζ (fun k => v₀ χ k 0) t = 4 := hgram j hj t ht hjt
      rw [← key] at h
      exact_mod_cast h
  have hdegZ : ∀ j ∈ Finset.Ico 1 m, ∑ χ ∈ B₀, basisDegree basis χ * cc j χ = 0 := by
    intro j hj
    have h : ∑ χ ∈ B₀, (basis.representation χ).character 1 *
        fourierTransform m ζ (fun k => v₀ χ k 0) j = 0 := hdeg j hj 0
    have key : ((∑ χ ∈ B₀, basisDegree basis χ * cc j χ : ℤ) : ℂ) = ∑ χ ∈ B₀,
        (basis.representation χ).character 1 * fourierTransform m ζ (fun k => v₀ χ k 0) j := by
      push_cast
      exact Finset.sum_congr rfl fun χ hχ => by rw [basisDegree_cast, hccF j hj χ hχ]
    rw [← key] at h
    exact_mod_cast h
  have hprinZ : ∀ j ∈ Finset.Ico 1 m, cc j principal = -1 := by
    intro j hj
    have h : fourierTransform m ζ (fun k => v₀ principal k 0) j = -1 := (hprin j hj).1
    rw [← hccF j hj principal hP0] at h
    exact_mod_cast h
  have hydeg : ∀ r < m / 2, ∑ χ ∈ B₀, basisDegree basis χ * c χ r = 0 := by
    intro r hr
    have h : Y r 1 = 0 := hY1 r hr
    have key : ((∑ χ ∈ B₀, basisDegree basis χ * c χ r : ℤ) : ℂ) = Y r 1 := by
      push_cast
      exact Finset.sum_congr rfl fun χ _ => by rw [basisDegree_cast, mul_comm]
    rw [← key] at h
    exact_mod_cast h
  have hαB : ∀ i, α i ∈ B₀ := fun i => (hα i).1
  have hJI : ∀ j ∈ J, j ∈ Finset.Ico 1 m := fun j hj => (Finset.mem_filter.mp hj).1
  have hy0 : ∀ φ ∈ B₀, c φ 0 = unitVector principal φ + ∑ i, β i * unitVector (α i) φ := by
    have h : basisCombination basis B₀ (fun χ => c χ 0) =
        basisCombination basis B₀ (unitVector principal + ∑ i, β i • unitVector (α i)) := by
      rw [basisCombination_principal_add_sum hprincipal hP0 hαB, ← hY0]
      exact basisCombination_eq_fun B₀ _
    intro φ hφ
    rw [eq_of_basisCombination_eq h hφ]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hcj : ∀ j ∈ J, ∀ φ ∈ B₀, cc j φ = -unitVector principal φ +
      ∑ i, η i * unitVector (α i) φ + 2 * σ * unitVector (χ j) φ := by
    intro j hj
    have hX : X j = basisCombination basis B₀ (cc j) :=
      Finset.sum_congr rfl fun χ hχ' => by rw [← hcc j (hJI j hj) χ hχ']
    have h : basisCombination basis B₀ (cc j) = basisCombination basis B₀
        (-unitVector principal + ∑ i, η i • unitVector (α i) + (2 * σ) • unitVector (χ j)) := by
      rw [basisCombination_neg_principal_add_sum_add hprincipal hP0 hαB (hχ j hj).1, ← hX,
        hXj j hj]
      push_cast
      rfl
    intro φ hφ
    rw [eq_of_basisCombination_eq h hφ]
    simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hχdeg : ∀ j ∈ J, ∀ t ∈ J, basisDegree basis (χ j) = basisDegree basis (χ t) := by
    intro j hj t ht
    have h1 := hdegχ j hj
    have h2 := hdegχ t ht
    rw [← basisDegree_cast] at h1 h2
    exact_mod_cast h1.trans h2.symm
  have hm : m = 4 ∨ 8 ≤ m := by
    rcases Nat.lt_or_ge n 3 with h | h
    · left
      show 2 ^ n = 4
      rw [show n = 2 by omega]
      norm_num
    · right
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
  have hJcard : J.card = m / 2 := hcard
  have hJ2 : 2 ≤ J.card := by
    rw [hJcard]
    rcases hm with h | h
    · rw [h]
    · omega
  have hm2 : 2 * (m / 2) = m :=
    Nat.two_mul_div_two_of_even ((Nat.even_pow' (by omega)).mpr even_two)
  have hpar : ∀ t ∈ Finset.Ico 1 m, Even t →
      ∃ r, 0 < r ∧ r < m / 2 ∧ ∀ φ ∈ B₀, cc t φ ≡ c φ 0 + c φ r [ZMOD 2] := by
    intro t ht hte
    have ht' := Finset.mem_Ico.mp ht
    obtain ⟨k, hk⟩ := hte
    have htk : t / 2 = k := by omega
    refine ⟨m / 2 - t / 2, by omega, by omega, fun φ hφ =>
      heven t ht ⟨k, hk⟩ (m / 2 - t / 2) (by omega) (by omega) ?_ φ hφ⟩
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  have hpos := pos_columns_vanish (y := fun r φ => c φ r) hm hP0
    (fun φ _ => basisDegree_pos basis φ) (basisDegree_principal basis hprincipal) hgramZ hdegZ
    hprinZ (fun r hr => (hfourc r hr).2) (fun r hr => (hfourc r hr).1) hydeg
    (fun r hr0 hrM => hcr r hr0 hrM) hcgram (fun r hr t ht => horth r hr t ht 0) hσ hinj hα hβ
    hχinj hχ hχdeg hηe hηi hβe hy0 hcj hJcard
  have hrows := first_rows_columns (y := fun r φ => c φ r) hP0 hgramZ hprinZ
    (fun r hr t ht => horth r hr t ht 0) hσ hinj hα hχinj hχ hηe hηi hβe hy0 hcj hJ2 hpos hpar
  have hcχ : ∀ j ∈ J, ∀ r < m / 2, c (χ j) r = 0 := by
    intro j hj r hr
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · rw [hr0, hy0 (χ j) (hχ j hj).1, unitVector_of_ne (hχ j hj).2.1,
        sum_mul_unitVector_of_forall_ne β (hχ j hj).2.2]
      ring
    · exact (hpos r hr0 hr).2 j hj
  have hcα0 : c (α e₀) 0 = σ := by
    rw [hy0 (α e₀) (hα e₀).1, unitVector_of_ne (hα e₀).2, sum_mul_unitVector_apply hinj, hβe]
    ring
  refine ⟨fun j hj t ht => ?_, fun t ht => ?_, hcχ, hcα0, fun r hr0 hrM => (hpos r hr0 hrM).1,
    fun h hh z hz hzodd => ⟨fun j hj => ?_, ?_⟩⟩
  · rw [← hcc t ht (χ j) (hχ j hj).1, (hrows t ht).2 j hj]
  · rw [← hcc t ht (α e₀) (hα e₀).1, (hrows t ht).1]
    push_cast
    ring
  · obtain ⟨h1, h2⟩ := hsec (χ j) (hχ j hj).1 h hh z hz hzodd
    have h2' : (basis.representation (χ j)).character (y ^ h) =
        ∑ r ∈ Finset.range (m / 2), (c (χ j) r : ℂ) * ζ ^ ((r : ℤ) * h) := h2
    rw [h1, h2']
    exact Finset.sum_eq_zero fun r hr => by
      rw [hcχ j hj r (Finset.mem_range.mp hr), Int.cast_zero, zero_mul]
  · obtain ⟨h1, h2⟩ := hsec (α e₀) (hα e₀).1 h hh z hz hzodd
    have h2' : (basis.representation (α e₀)).character (y ^ h) =
        ∑ r ∈ Finset.range (m / 2), (c (α e₀) r : ℂ) * ζ ^ ((r : ℤ) * h) := h2
    have hM0 : 0 < m / 2 := by omega
    rw [h1, h2', Finset.sum_eq_single 0 (fun r hr hr0 => by
        rw [(hpos r (Nat.pos_of_ne_zero hr0) (Finset.mem_range.mp hr)).1, Int.cast_zero,
          zero_mul])
      fun h0 => absurd (Finset.mem_range.mpr hM0) h0, hcα0]
    simp

theorem conditional_odd_constituent_complete_first_fourier_rows
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    [Fintype (centralizerOddCoreQuotient n S e)]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
    ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      let m : ℕ := 2 ^ n
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      let J : Finset ℕ := (Finset.Ico 1 m).filter Odd
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ ξ : ℂ, IsPrimitiveRoot ξ (2 * m) → ξ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (ξ ^ t))
      let c : basis.index → ℕ → ℤ := fun χ r => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      let Y : ℕ → G → ℂ := fun r g =>
        ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character g
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let fc : basis.index → ℕ → ℂ := fun χ j => fourierTransform m ζ (fun k => v χ k 0) j
      let X : ℕ → G → ℂ := fun j => ∑ χ ∈ B₀, fc χ j • (basis.representation χ).character
      let constituents : (Fin 3 → basis.index) → (Fin 3 → ℤ) → (Fin 3 → ℤ) → ℤ →
          (ℕ → basis.index) → ℕ → Fin 3 → Prop := fun α β η σ χ δ e₀ =>
        Function.Injective α ∧ (∀ i, α i ∈ B₀ ∧ α i ≠ principal) ∧
        (∀ i, β i = 1 ∨ β i = -1) ∧ (∀ i, η i = 1 ∨ η i = -1) ∧ (σ = 1 ∨ σ = -1) ∧
        Set.InjOn χ J ∧ (∀ j ∈ J, χ j ∈ B₀ ∧ χ j ≠ principal ∧ ∀ i, χ j ≠ α i) ∧ 0 < δ ∧
        η e₀ = -β e₀ ∧ (∀ i, i ≠ e₀ → η i = β i) ∧ (∀ i, η i = -β i → i = e₀) ∧
        Y 0 = 1 + ∑ i, (β i : ℂ) • (basis.representation (α i)).character ∧
        (∀ j ∈ J, X j = -1 + ∑ i, (η i : ℂ) • (basis.representation (α i)).character +
          (2 * σ : ℂ) • (basis.representation (χ j)).character) ∧
        (∀ j ∈ J, (basis.representation (χ j)).character 1 = δ) ∧
        1 + ∑ i, (β i : ℂ) * (basis.representation (α i)).character 1 = 0 ∧
        (σ * δ : ℂ) = 1 + β e₀ * (basis.representation (α e₀)).character 1 ∧
        β e₀ = σ ∧ (δ : ℂ) = (basis.representation (α e₀)).character 1 + σ
      (∃ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
          (e₀ : Fin 3), constituents α β η σ χ δ e₀ ∧ (J.image χ).card = m / 2 ∧
            ∀ j ∈ J, fc (χ j) j = 2 * σ) ∧
      ∀ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
          (e₀ : Fin 3), constituents α β η σ χ δ e₀ →
        (∀ j ∈ J, ∀ t ∈ Finset.Ico 1 m, fc (χ j) t = if t = j then 2 * σ else 0) ∧
        (∀ t ∈ Finset.Ico 1 m, fc (α e₀) t = -σ) ∧
        (∀ j ∈ J, ∀ r < m / 2, c (χ j) r = 0) ∧ c (α e₀) 0 = σ ∧
        (∀ r, 0 < r → r < m / 2 → c (α e₀) r = 0) ∧
        ∀ h : ℤ, Odd h → ∀ z ∈ Subgroup.centralizer ({y} : Set G), Odd (orderOf z) →
          (∀ j ∈ J, (basis.representation (χ j)).character (y ^ h * z) = 0) ∧
          (basis.representation (α e₀)).character (y ^ h * z) = σ :=
  conditional_odd_constituent_complete_first_fourier_rows_of_localHyp n hn S e p f hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal

end CFSG.Wreathed.ConditionalFirstFourierRows
